r"""
Sets up logs using the `logging` package.
"""
import logging
import psutil
import os
from psutil._common import bytes2human


def log_setup(logname):
    try:
        logger = logging.getLogger()
        if logger.hasHandlers():
            logger.handlers.clear()
        else:
            if not os.path.isdir('logs'):
                os.mkdir('logs')
            logger.setLevel(logging.INFO)
        fh = logging.FileHandler('logs/' + logname + '.log')
        sh = logging.StreamHandler()
        fmt = logging.Formatter('%(asctime)s %(message)s', datefmt="%m-%d %H:%M")
        fh.setFormatter(fmt)
        sh.setFormatter(fmt)
        logger.addHandler(fh)
        logger.addHandler(sh)
        logging.info(f"start log {logname}")
    except OSError as e:
        if str(e)[:10] == '[Errno 36]':
            print('WARNING')
            print('changing log name to \'log_name_too_long\'')
            log_setup('log_name_too_long')
        else:
            raise e
    return


def log_memory(process=False):
    message = f"available memory: {bytes2human(psutil.virtual_memory().available)}"
    if process:
        pid = os.getpid()
        message = f"pid: {pid}, memory%: {psutil.Process(pid).memory_percent()}, " + message
    logging.info(message)
    return
