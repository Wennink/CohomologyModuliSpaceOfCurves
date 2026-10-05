r"""
Task scheduler for multiprocessing.
This was written for the specific purpose of computing Deligne's weight spectral sequence.
As such it should not be considered as an efficient or reliable general purpose scheduler.
"""
from queue import Empty as queueEmpty
from multiprocessing import Queue, Process, active_children, cpu_count, set_start_method, get_context
from sage.rings.all import QQ
from time import sleep, time
from collections import defaultdict, deque
import logging
import psutil
from .log_setup import log_setup

try:
    import tblib.pickling_support
    tblib.pickling_support.install()
    imported_tblib = True
except ModuleNotFoundError:
    imported_tblib = False
import sys


class ExceptionWrapper(object):

    def __init__(self, ee, nr):
        self.ee = ee
        self.nr = nr
        __, __, self.tb = sys.exc_info()

    def re_raise(self):
        print('error in task', self.nr)
        raise self.ee.with_traceback(self.tb)


def set_context(context='forkserver'):
    try:
        set_start_method(context)
        logging.info(f'set multiprocessing context to {context}')
    except RuntimeError:
        assert (get_context() == get_context(context))
    return


def worker(que, task_label, task, args, is_scheduler):
    try:
        if is_scheduler:
            que.put((task_label, *task(task_label + '-', *args)))
        else:
            task(*args)
            que.put((task_label, (), (), False))
    except Exception as e:
        if imported_tblib:
            que.put(ExceptionWrapper(e, task_label))
        else:
            que.put('error in task ' + task_label + ' ' + task.__name__ + str(args))
    return


previous_string = ''


def print_progress(string):
    global previous_string
    if string == previous_string:
        return
    print(string)
    previous_string = string
    return


def run_tasks(initial_scheduler_task, initial_args, soft_max_cpu=None, hard_max_cpu=None, memory_threshold=80, bottleneck_scheduling=False, verbose=False):
    r"""
    This is called by other parts of the program to run the tasks.
    It stops starting new tasks when the memory usage is over the ``memory_threshold``.
    This ``memory_threshold`` is given as a percentage of total memory.
    """
    if hard_max_cpu is None:
        hard_max_cpu = cpu_count()
    if soft_max_cpu is None:
        soft_max_cpu = hard_max_cpu
    current_hard_max_cpu = [hard_max_cpu]
    timestamp = [0]

    log_setup(initial_scheduler_task.__name__ + str(initial_args))
    set_context()

    queue = Queue()

    tasks = {'0': (initial_scheduler_task, initial_args, True)}
    children_list = {}
    parent_list = defaultdict(list)

    lifo_task_queue = deque()

    failed_task_queue = deque()
    failed_task_times = defaultdict(int)
    failed_1_start_times = [0]
    check_wait = True
    wait_first = True

    writer_tasks = []

    queue_list = []

    task_label = '0'
    current_scheduler_process = Process(target=worker, args=(queue, '0', initial_scheduler_task, initial_args, True))
    logging.info(f'starting task {initial_scheduler_task.__name__}{initial_args} and label {task_label}')
    current_scheduler_process.start()
    current_tasks = {'0': current_scheduler_process}

    while True:
        try:
            queue_output = queue.get(block=False)
            process_queue_output(queue_output, current_tasks, tasks, writer_tasks, queue_list, children_list, parent_list, lifo_task_queue)
        except queueEmpty:
            nr_active = len(active_children())
            if cpu_free(nr_active - len(writer_tasks), soft_max_cpu, current_hard_max_cpu[0]):
                memory_usage = psutil.virtual_memory().percent
                if memory_usage < memory_threshold:
                    if failed_task_queue:
                        check_wait, wait_first = process_failed_task(queue, failed_task_queue, failed_task_times, tasks, memory_usage, check_wait, wait_first, bottleneck_scheduling, current_scheduler_process, failed_1_start_times, current_tasks, verbose)
                    elif lifo_task_queue:
                        start_new_task(queue, lifo_task_queue, tasks, bottleneck_scheduling, current_scheduler_process, current_tasks, memory_usage)
                    else:
                        if len(current_tasks) == 0:
                            sleep(1)
                            # check if something got added in the meantime
                            if queue.empty():
                                # finished computing
                                if len(tasks) != 0:
                                    raise RuntimeError('did not finish all tasks')
                                return
                        else:
                            sleep(1)
                            find_failed_tasks(nr_active, tasks, current_tasks, failed_task_queue, failed_task_times, current_hard_max_cpu, timestamp)
                            if verbose:
                                printinfo('waiting for new tasks', current_tasks, writer_tasks, tasks)
                else:
                    sleep(10)
                    find_failed_tasks(nr_active, tasks, current_tasks, failed_task_queue, failed_task_times, current_hard_max_cpu, timestamp)
                    if verbose:
                        print_progress('memory block')
            else:
                sleep(1)
                find_failed_tasks(nr_active, tasks, current_tasks, failed_task_queue, failed_task_times, current_hard_max_cpu, timestamp)
                if current_hard_max_cpu[0] < hard_max_cpu and int(time()) - timestamp[0] > 3600:
                    if psutil.virtual_memory().percent < 45:
                        current_hard_max_cpu[0] = min(2 * current_hard_max_cpu[0], hard_max_cpu)
                        logging.info(f'increased max tasks to {current_hard_max_cpu[0]}')
                    timestamp[0] += 600
                if verbose:
                    printinfo('full process nr', current_tasks, writer_tasks, tasks)
    raise RuntimeError


def start_new_task(queue, lifo_task_queue, tasks, bottleneck_scheduling, current_scheduler_process, current_tasks, memory_usage):
    task_label = lifo_task_queue.pop()
    task, args, is_scheduler_task = tasks[task_label]
    if bottleneck_scheduling and is_scheduler_task:
        if current_scheduler_process.is_alive():
            lifo_task_queue.append(task_label)
            logging.info('waiting for scheduler task')
            current_scheduler_process.join()
            return
    process = Process(target=worker, args=(queue, task_label, task, args, is_scheduler_task))
    if bottleneck_scheduling and is_scheduler_task:
        current_scheduler_process = process
    logging.info(f'starting task {task.__name__}{args} with label {task_label}')
    process.start()
    current_tasks[task_label] = process
    if memory_usage > 50:
        sleep(5)
    return


def cpu_free(nr, soft_max, hard_max):
    if nr >= hard_max:
        return False
    if nr < soft_max:
        return True
    if psutil.cpu_percent() < 85:
        return True
    if psutil.cpu_percent() < 94:
        sleep(0.2)
        if psutil.cpu_percent() < 94:
            return True
    return False


def process_failed_task(queue, failed_task_queue, failed_task_times, tasks, memory_usage, check_wait, wait_first, bottleneck_scheduling, current_scheduler_process, failed_1_start_times, current_tasks, verbose):
    task_label = failed_task_queue.popleft()
    failed_times = failed_task_times[task_label]
    if failed_times > 4:
        task, args, _ = tasks[task_label]
        raise RuntimeError(f'task {task.__name__}{args} with label {task_label}  has failed 5 times')
    memory_threshold_failed = [80, 80, 40, 10][failed_times - 1]
    if memory_usage < memory_threshold_failed:
        if check_wait:
            wait_first = True
            if failed_times == 1:
                failed_1_start_times[0] += 1
                if failed_1_start_times[0] == 5:
                    failed_1_start_times[0] = 0
                elif memory_usage < 30:
                    wait_first = False
            check_wait = False
        if wait_first:
            logging.info('sleeping for one minute to see if memory is stable enough to restart failed task')
            sleep(60)
        if (not wait_first) or psutil.virtual_memory().percent - memory_usage < 1:
            task, args, is_scheduler_task = tasks[task_label]
            if bottleneck_scheduling and is_scheduler_task:
                if current_scheduler_process.is_alive():
                    failed_task_queue.appendleft(task_label)
                    logging.info('waiting for scheduler task')
                    current_scheduler_process.join()
                    return check_wait, wait_first
            process = Process(target=worker, args=(queue, task_label, task, args, is_scheduler_task))
            if bottleneck_scheduling and is_scheduler_task:
                current_scheduler_process = process
            logging.info(f'restarting task {task.__name__}{args} with label {task_label}, this task has failed {failed_times} times so far')
            process.start()
            current_tasks[task_label] = process
            sleepmins = [0, 10, 60, 300][failed_times - 1]
            logging.info(f'sleeping for {sleepmins} minutes to give the restarted task some time')
            sleep(60 * sleepmins)
            return True, wait_first
    if verbose:
        print_progress('memory blocked for rerun')
    failed_task_queue.appendleft(task_label)
    return check_wait, wait_first


def process_queue_output(queue_output, current_tasks, tasks, writer_tasks, queue_list, children_list, parent_list, lifo_task_queue):
    if imported_tblib:
        if isinstance(queue_output, ExceptionWrapper):
            queue_output.re_raise()
    elif isinstance(queue_output, str):
        raise RuntimeError(queue_output)
    finished_task_label, new_tasks, replacement_task_labels, needQueue = queue_output
    del (current_tasks[finished_task_label])
    del (tasks[finished_task_label])
    if finished_task_label in writer_tasks:
        writer_tasks.remove(finished_task_label)
    logging.info(f'finished task {finished_task_label}')
    if needQueue:
        queue_list.append(Queue())
        new_queue = queue_list[-1]
    for task_label, task, args, is_scheduler_task, dependencies in new_tasks:
        if needQueue:
            args = (new_queue, *args)
        tasks[task_label] = (task, args, is_scheduler_task)
        if dependencies:
            children_list[task_label] = set(dependencies)
        else:
            lifo_task_queue.append(task_label)
        for child in dependencies:
            parent_list[child].append(task_label)
    for task_label in replacement_task_labels:
        parent_list[task_label] += parent_list[finished_task_label]
    for parent_label in parent_list[finished_task_label]:
        children_list[parent_label].remove(finished_task_label)
        children_list[parent_label].update(replacement_task_labels)
        if not children_list[parent_label]:
            lifo_task_queue.append(parent_label)
            del (children_list[parent_label])
    del (parent_list[finished_task_label])
    if needQueue:
        # assuming here that the writer task is the last task added whenever we need a queue
        writer_tasks.append(task_label)
    return

# for debugging purposes:


def printinfo(initial_string, current_tasks, writer_tasks, tasks):
    string = initial_string
    string += f', current tasks: {list(current_tasks.keys())}'
    string += f'\n active_children: {len(active_children())}, current_tasks: {len(current_tasks)}, writer_tasks: {len(writer_tasks)}'
    tempdic = defaultdict(int)
    for tt in current_tasks:
        tempdic[tasks[tt][0]] += 1
    for tn, tnr in tempdic.items():
        string += f'\n{tn} {tnr}'
    print_progress(string)
    return


def find_failed_tasks(nr_active, tasks, current_tasks, failed_task_queue, failed_task_times, current_hard_max_cpu, timestamp):
    any_first_time_fails = False
    while nr_active < len(current_tasks):
        found_culprit = False
        for task_label, proc in current_tasks.items():
            if proc.exitcode is not None:
                if proc.exitcode != 0:
                    task, args, _ = tasks[task_label]
                    failed_task_queue.append(task_label)
                    failed_task_times[task_label] += 1
                    if failed_task_times[task_label] == 1:
                        any_first_time_fails = True
                    del (current_tasks[task_label])
                    found_culprit = True
                    break
        if not found_culprit:
            raise RuntimeError('zombie tasks without exit code')
    if any_first_time_fails:
        new_timestamp = int(time())
        if new_timestamp - timestamp[0] > 600:
            timestamp[0] = new_timestamp
            current_hard_max_cpu[0] = QQ((current_hard_max_cpu[0], 2)).ceil()
            logging.info(f'decreased max tasks to {current_hard_max_cpu[0]}')
    return
