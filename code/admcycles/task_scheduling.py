r"""
Gives the multiprocessing manager the tasks to be computed and information about their dependencies.
"""
from .mp_manager import run_tasks
from collections import defaultdict
from .pushforward_spectral_sequence import compute_image, compute_image_single_gamma, compute_image_rank_sym, diffmap_prod_basis_single_target, symmetrize_graph_contribution, precompute_matrix_image_single_gamma
from .pullback_spectral_sequence import split_iter, GK_image_rank, GK_image_single_gamma, diff_loop_single_vertex, diff_split_single_vertex, GK_symmetrized_graph_image, get_diff_split_targets, diff_loop_single_vertex_relabel, diff_split_single_vertex_relabel, diff_split_single_target, diff_loop_product_basis, GK_image, relabel_basis_dict
from sage.rings.all import QQ
from .list_strata import list_strata_can, get_strata_list_inds
from .antisymmetry import as_basis_rank, comp_as_basis, get_sym_graph_canon, symmetrize_graph
from .cohomology_computation import compute_wH, get_gnr_pq, get_pq
from sage.combinat.all import Partitions
import shelve
import os
from sage.env import DOT_SAGE


def compute_gns(gns, no_sym, dss_precompute_image_matrix, lazier=False, verbose=False, soft_num_cpu=None, hard_num_cpu=None, slow_as_bases_precompute=False, moduli_type='sm'):
    if slow_as_bases_precompute:
        slow_as_bases_computation(gns, no_sym, verbose=verbose)
    return run_tasks(gns_list_scheduler, (gns, no_sym, dss_precompute_image_matrix, moduli_type), soft_max_cpu=soft_num_cpu, hard_max_cpu=hard_num_cpu, bottleneck_scheduling=lazier, verbose=verbose)


def gns_list_scheduler(task_label, gns_list, no_sym, dss_precompute_image_matrix, moduli_type='sm'):
    task_list = []
    task_nr = 0
    if moduli_type == 'sm':
        if no_sym:
            task_list.append((task_label + str(task_nr), shared_as_bases_scheduler, (gns_list,), True, ()))
            task_nr += 1
            task_list.append((task_label + str(task_nr), full_GK_scheduler, (gns_list,), True, (task_label + str(0),)))
            task_nr += 1
        for g, n, nr_push_rows, GK, rowdict in gns_list:
            if not no_sym:
                task_list.append((task_label + str(task_nr), full_gn_scheduler, (g, n, nr_push_rows, GK, rowdict, no_sym, dss_precompute_image_matrix), True, ()))
                task_nr += 1
            else:
                task_list.append((task_label + str(task_nr), full_gn_scheduler, (g, n, nr_push_rows, 0, rowdict, no_sym, dss_precompute_image_matrix), True, (task_label + str(0),)))
                task_nr += 1
    else:
        assert (moduli_type in ('rt', 'ct'))
        for g, n, nr_push_rows, GK, rowdict in gns_list:
            task_list.append((task_label + str(task_nr), full_scheduler_ct_rt, (g, n, nr_push_rows, GK, rowdict, no_sym, moduli_type), True, ()))
            task_nr += 1
    return task_list, (), False


def gns_list_scheduler_old(task_label, gns_list, only_no_sym=False):
    task_list = []
    task_list.append((task_label + str(0), GK_single_vertex_scheduler, (gns_list,), True, ()))
    task_nr = 1
    for g, n, nr_push_rows, GK, rowdict in gns_list:
        if rowdict:
            task_list.append((task_label + str(task_nr), full_gn_scheduler, (g, n, nr_push_rows, GK, only_no_sym, rowdict), True, (task_label + str(0),)))
            task_nr += 1
        else:
            task_list.append((task_label + str(task_nr), full_gn_scheduler, (g, n, 0, GK, only_no_sym), True, (task_label + str(0),)))
            task_nr += 1
            task_list.append((task_label + str(task_nr), full_gn_scheduler, (g, n, nr_push_rows, 0, only_no_sym), True, ()))
            task_nr += 1
    return task_list, (), False


def full_gn_scheduler(task_label, g, n, nr_push_rows, GK, rowdict, only_no_sym=False, dss_precompute_image_matrix=False):
    tasks = 0
    task_list = []
    full_tasknrs_wh = []

    dim = 3 * g - 3 + n

    pqlist = get_pq(g, n, nr_push_rows, GK, only_no_sym, rowdict=rowdict)

    tasknrs_wh = {}
    if only_no_sym:
        parts = (tuple([1] * n),)
    else:
        parts = reversed(Partitions(n))
    for lpar in parts:
        par = tuple(lpar)
        tasknrs_asb = {}
        tasknrs_im = {}
        no_sym = len(par) == n
        for p, q, weight_sequence in pqlist:
            if compute_wH.file_exists(g, n, p, q, par):
                continue
            if not no_sym and compute_wH.file_exists(g, n, p, q, tuple([1] * n)):
                if compute_wH(g, n, p, q, tuple([1] * n)) == 0:
                    continue
            pq_dependencies = []
            if weight_sequence:
                r = q - p
                grrs = [(p, r), (p + 1, r - 1)]
            else:
                r = dim - q
                grrs = [(p, r), (p - 1, r)]
            grrs = [x for x in grrs if x[0] >= 0 and x[1] >= 0 and sum(x) <= dim]
            for grr in grrs:
                im_dependencies = []
                if (*grr, weight_sequence) in tasknrs_im:
                    pq_dependencies.append(tasknrs_im[(*grr, weight_sequence)])
                    continue
                gamma_r, r = grr
                if weight_sequence:
                    grrs2 = [(gamma_r, r), (gamma_r - 1, r + 1)]
                else:
                    grrs2 = [(gamma_r, r), (gamma_r + 1, r)]
                grrs2 = [x for x in grrs2 if x[0] >= 0 and x[1] >= 0 and sum(x) <= dim]
                for grr2 in grrs2:
                    if grr2 in tasknrs_asb:
                        im_dependencies.append(tasknrs_asb[grr2])
                        continue
                    gamma_r2, r2 = grr2
                    sym_dependency = []
                    if not no_sym:
                        if weight_sequence:
                            qq = gamma_r2 + r2
                        else:
                            qq = dim - r2
                        for epsilon in (-1, 0, 1):
                            key = (gamma_r2 + epsilon, qq)
                            if key in tasknrs_wh:
                                sym_dependency.append(tasknrs_wh[key])
                    task_list.append((task_label + str(tasks), as_basis_scheduler, (g, n, gamma_r2, r2, par), True, sym_dependency))
                    tasknrs_asb[grr2] = task_label + str(tasks)
                    im_dependencies.append(task_label + str(tasks))
                    tasks += 1

                sym_dependency = []
                if not no_sym:
                    for epsilon in (-1, 0):
                        key = (gamma_r + epsilon, gamma_r + r)
                        if key in tasknrs_wh:
                            sym_dependency.append(tasknrs_wh[key])
                if weight_sequence:
                    task_list.append((task_label + str(tasks), image_scheduler, (g, n, gamma_r, r, par, 'sm', dss_precompute_image_matrix), True, sym_dependency + im_dependencies))
                else:
                    task_list.append((task_label + str(tasks), GK_image_scheduler, (g, n, gamma_r, r, par, 'sm'), True, sym_dependency + im_dependencies))
                tasknrs_im[(*grr, weight_sequence)] = task_label + str(tasks)
                pq_dependencies.append(task_label + str(tasks))
                tasks += 1

            if no_sym or not (p, q) in tasknrs_wh:
                sym_dependency = []
            else:
                sym_dependency = [tasknrs_wh[(p, q)]]
            task_list.append((task_label + str(tasks), compute_wH_scheduler, (g, n, p, q, par, weight_sequence), True, sym_dependency + pq_dependencies))
            if no_sym:
                tasknrs_wh[(p, q)] = task_label + str(tasks)
            full_tasknrs_wh.append(task_label + str(tasks))
            tasks += 1

    return task_list, full_tasknrs_wh, False


def compute_wH_scheduler(task_label, g, n, p, q, n_part, weight_sequence):
    if len(n_part) != n:
        if compute_wH(g, n, p, q, tuple([1] * n)) == 0:
            return (), (), False
    return ((task_label + '0', compute_wH, (g, n, p, q, n_part, weight_sequence), False, ()),), (task_label + '0',), False


def image_scheduler(task_label, g, n, gamma_r, r, n_part, moduli_type, precompute_matrix, delete_files=False, ignore_file_exists=False):
    if len(n_part) == n:
        if compute_image.file_exists(g, n, gamma_r, r, moduli_type) and not ignore_file_exists:
            return (), (), False
        if gamma_r == 0:
            return [(task_label + '0', compute_image, (g, n, gamma_r, r, delete_files), False, ())], (task_label + '0',), False
        task_list = []
        nr_graphs = len(list_strata_can(g, n, gamma_r))
        dependencies = []
        task_nr = 0
        if moduli_type == 'sm':
            for i in range(nr_graphs):
                if compute_image_single_gamma.file_exists(g, n, gamma_r, i, r):
                    continue
                gamma = list(list_strata_can(g, n, gamma_r))[i]
                dependencies2 = []
                for j in range(len(gamma._edges)):
                    task_list.append((task_label + str(task_nr), diffmap_prod_basis_single_target, (g, n, gamma_r, i, j, r), False, ()))
                    dependencies2.append(task_label + str(task_nr))
                    task_nr += 1
                if precompute_matrix:
                    task_list.append((task_label + str(task_nr), precompute_matrix_image_single_gamma, (g, n, gamma_r, i, r), False, dependencies2))
                    task_nr += 1
                    task_list.append((task_label + str(task_nr), compute_image_single_gamma, (g, n, gamma_r, i, r, delete_files, precompute_matrix), False, (task_nr - 1,)))
                else:
                    task_list.append((task_label + str(task_nr), compute_image_single_gamma, (g, n, gamma_r, i, r, delete_files, precompute_matrix), False, dependencies2))
                dependencies.append(task_label + str(task_nr))
                task_nr += 1
        final_label = task_label + str(task_nr)
        task_list.append((final_label, compute_image, (g, n, gamma_r, r, delete_files, moduli_type), False, dependencies))
        return task_list, (final_label,), False

    do_computation = False
    for epsilon in (-1, 0):
        key = (g, n, gamma_r + epsilon, gamma_r + r, tuple([1] * n), True, moduli_type)
        if compute_wH.file_exists(*key):
            if compute_wH(*key) != 0:
                do_computation = True
                break
    if not do_computation:
        return (), (), False
    if gamma_r == 0:
        return [(task_label + '0', compute_image_rank_sym, (g, n, gamma_r, r, n_part, moduli_type), False, ())], (task_label + '0',), False
    post_gamma_r = gamma_r - 1
    post_r = r + 1
    index = 0
    task_list = []
    dependencies = []
    task_nr = 0
    for i in get_strata_list_inds(g, n, post_gamma_r, moduli_type):
        old_index = index
        index = old_index + as_basis_rank(g, n, post_gamma_r, i, post_r)
        if old_index == index:
            continue
        task_list.append((task_label + str(task_nr), symmetrize_graph_contribution, (g, n, post_gamma_r, i, post_r, n_part, moduli_type, old_index, index), False, ()))
        dependencies.append(task_label + str(task_nr))
        task_nr += 1
    task_list.append((task_label + str(task_nr), compute_image_rank_sym, (g, n, gamma_r, r, n_part, moduli_type), False, dependencies))
    return task_list, (task_label + str(task_nr),), False


def as_basis_scheduler(task_label, g, n, gamma_r, r, n_part):
    try:
        with shelve.open(os.path.join(DOT_SAGE, f'admcycles/cohomology/as_bases_{g}_{n}_{gamma_r}_{r}_{n_part}'), 'c') as file:
            if 'finished' in file:
                if file['finished']:
                    return (), (), False
            have_sym = len(n_part) != n
            task_list = []
            tasks = 0
            for i, gamma in enumerate(list_strata_can(g, n, gamma_r)):
                if 'gr' + str(i) in file:
                    continue
                if have_sym:
                    if as_basis_rank(g, n, gamma_r, i, r) == 0:
                        continue
                    sym_ind = symmetrize_graph(g, n, gamma_r, i, n_part)
                    gamma = get_sym_graph_canon(g, n, gamma_r, n_part, sym_ind)
                if len(gamma.leg_automorphism_group()) == 1:
                    continue
                task_list.append((task_label + str(tasks), compute_as_bases, (g, n, gamma_r, r, n_part, i), False, ()))
                tasks += 1
            if tasks > 0:
                task_list.append((task_label + str(tasks), as_basis_writer, (tasks, g, n, gamma_r, r, n_part), False, ()))
        if tasks > 0:
            return task_list, (task_label + str(tasks),), True
        else:
            return (), (), False
    except IOError as e:
        print('got IOError')
        print(str(e))
        print('removing file and starting again')
        os.remove(os.path.join(DOT_SAGE, f'admcycles/cohomology/as_bases_{g}_{n}_{gamma_r}_{r}_{n_part}'))
        return as_basis_scheduler(task_label, g, n, gamma_r, r, n_part)


def compute_as_bases(que, g, n, gamma_r, r, n_part, ind):
    que.put((ind, *comp_as_basis(g, n, gamma_r, n_part, ind, r)))
    return


def as_basis_writer(que, nr_cases, g, n, gamma_r, r, n_part):
    cases_completed = 0
    n_part = tuple(n_part)
    with shelve.open(os.path.join(DOT_SAGE, f'admcycles/cohomology/as_bases_{g}_{n}_{gamma_r}_{r}_{n_part}'), 'c') as file:
        while cases_completed < nr_cases:
            ind, asb, ptasb = que.get()
            file['asb' + str(ind)] = asb
            file['ptasb' + str(ind)] = ptasb
            file['gr' + str(ind)] = len(asb)
            cases_completed += 1
        file['finished'] = True
    que.close()
    return


def GK_image_scheduler(task_label, g, n, gamma_r, r, n_part, moduli_type):
    if GK_image_rank.file_exists(g, n, gamma_r, r, n_part, moduli_type):
        return (), (), False
    if gamma_r >= 3 * g - 3 + n - r:
        return [(task_label + '0', GK_image_rank, (g, n, gamma_r, r, n_part, moduli_type), False, ())], (task_label + '0',), False
    task_list = []
    dependencies = []
    task_nr = 0
    if len(n_part) == n:
        if moduli_type == 'sm':
            nr_graphs = len(list_strata_can(g, n, gamma_r))
            for i in range(nr_graphs):
                if GK_image_single_gamma.file_exists(g, n, gamma_r, i, r):
                    continue
                task_list.append((task_label + str(task_nr), GK_image_single_gamma, (g, n, gamma_r, i, r), False, ()))
                dependencies.append(task_label + str(task_nr))
                task_nr += 1
    else:
        do_computation = False
        for epsilon in (0, 1):
            key = (g, n, gamma_r + epsilon, 3 * g - 3 + n - r, tuple([1] * n), False, moduli_type)
            if compute_wH.file_exists(*key):
                if compute_wH(*key) != 0:
                    do_computation = True
                    break
        if not do_computation:
            return (), (), False
        post_gamma_r = gamma_r + 1
        index = 0
        for i in get_strata_list_inds(g, n, post_gamma_r, moduli_type):
            old_index = index
            index = old_index + as_basis_rank(g, n, post_gamma_r, i, r)
            if old_index == index:
                continue
            task_list.append((task_label + str(task_nr), GK_symmetrized_graph_image, (g, n, post_gamma_r, i, r, n_part, moduli_type, old_index, index), False, ()))
            dependencies.append(task_label + str(task_nr))
            task_nr += 1
    task_list.append((task_label + str(task_nr), GK_image_rank, (g, n, gamma_r, r, n_part, moduli_type), False, dependencies))
    return task_list, (task_label + str(task_nr),), False


def GK_single_vertex_scheduler(task_label, gns):
    gnrs = []
    for g, n, _, GK, rowdict in gns:
        prset = []
        par = tuple([1] * n)
        dim = 3 * g - 3 + n
        for p, q, dss in get_pq(g, n, 0, GK, True, rowdict=rowdict):
            if dss:
                continue
            if compute_wH.file_exists(g, n, p, q, par):
                continue
            r = dim - q
            if p == 0:
                prset.append((p, r))
            else:
                prset += [(p, r), (p - 1, r)]
        for p, r in set(prset):
            gnrs += get_gnr_pq(g, n, p, r)

    task_list = []
    tasks = 0
    inheritance_dependencies = []
    for g, n, r, n_part, se in set(gnrs):
        if 3 * g - 3 + n == r:
            continue
        if g > 0 and not diff_loop_single_vertex.file_exists(g, n, r, n_part, se):
            task_list.append((task_label + str(tasks), diff_loop_single_vertex, (g, n, r, n_part, se), False, ()))
            inheritance_dependencies.append(task_label + str(tasks))
            tasks += 1
        for g1, _, S1, _ in split_iter(g, n, se):
            if not diff_split_single_vertex.file_exists(g, n, r, n_part, se, g1, S1):
                task_list.append((task_label + str(tasks), diff_split_single_vertex, (g, n, r, n_part, se, g1, S1), False, ()))
                inheritance_dependencies.append(task_label + str(tasks))
                tasks += 1
    return task_list, inheritance_dependencies, False


def shared_as_bases_scheduler(task_label, gns_list):
    task_list = []
    dependencies = []
    tasks = 0
    for g, n, D, GK, rowdict in gns_list:
        n_part = tuple([1] * n)
        prsetD = []
        prsetGK = []
        par = tuple([1] * n)
        dim = 3 * g - 3 + n
        for p, q, dss in get_pq(g, n, D, GK, True, rowdict=rowdict):
            if compute_wH.file_exists(g, n, p, q, par):
                continue
            if dss:
                r = q - p
                if p == q or r == 0:
                    prsetD.append((p, r))
                else:
                    prsetD += [(p, r), (p + 1, r - 1)]
            else:
                r = dim - q
                if p == 0:
                    prsetGK.append((p, r))
                else:
                    prsetGK += [(p, r), (p - 1, r)]
        for p, r in set(prsetGK):
            if (p, r) in prsetD:
                task_list.append((task_label + str(tasks), as_basis_scheduler, (g, n, p, r, n_part), True, ()))
                dependencies.append(task_label + str(tasks))
                tasks += 1

    return task_list, dependencies, False


def full_GK_scheduler(task_label, gns_list):
    gnprs = []
    gnpqs = []
    for g, n, _, GK, rowdict in gns_list:
        prset = []
        par = tuple([1] * n)
        dim = 3 * g - 3 + n
        for p, q, dss in get_pq(g, n, 0, GK, True, rowdict=rowdict):
            if dss:
                continue
            if compute_wH.file_exists(g, n, p, q, par):
                continue
            r = dim - q
            if p == 0:
                prset.append((p, r))
            else:
                prset += [(p, r), (p - 1, r)]
            gnpqs.append((g, n, p, q))
        for p, r in set(prset):
            if dim == p + r:
                continue
            gnprs.append((g, n, p, r))

    sss = []
    for g, n, p, r in gnprs:
        for ind in range(len(list_strata_can(g, n, p))):
            sss.append(((g, n, p, ind, r), get_diff_split_targets(g, n, p, ind, r, scheduling=True)))

    sv_relabel_dict = {}
    sv_dict = {}
    ind_dict_dict = {}
    sv_dict_loop = {}
    sv_rel_dict_loop = {}
    as_basis_dict = {}
    gamma_dict = defaultdict(list)
    tasks = 0
    task_list = []
    for g, n, p, r in gnprs:
        loop_depend = []
        combine_depend = []
        as_param = (g, n, p + 1, r, tuple([1] * n))

        if as_param in as_basis_dict:
            as_target_depend = [as_basis_dict[as_param]]
        else:
            task_list.append((task_label + str(tasks), as_basis_scheduler, as_param, True, ()))
            as_basis_dict[as_param] = task_label + str(tasks)
            as_target_depend = [task_label + str(tasks)]
            tasks += 1
        for ind in range(len(list_strata_can(g, n, p))):
            split_sss, loop_sss = get_diff_split_targets(g, n, p, ind, r, scheduling=True)
            gnpir = (g, n, p, ind, r)

            # split
            target_depend = defaultdict(list)
            for target_ind, sv_rel_min_r1, ind_dict_list in split_sss:
                sv_params, rel_dicts = sv_rel_min_r1
                if sv_params in sv_dict:
                    sv_rel_depend = [sv_dict[sv_params]]
                else:
                    task_list.append((task_label + str(tasks), diff_split_single_vertex, sv_params, False, ()))
                    sv_dict[sv_params] = task_label + str(tasks)
                    sv_rel_depend = [task_label + str(tasks)]
                    tasks += 1
                for r1 in range(sv_params[2] + 1):
                    params = (*sv_params, r1, *rel_dicts)
                    if params in sv_relabel_dict:
                        if not sv_relabel_dict[params] in target_depend[target_ind]:
                            target_depend[target_ind].append(sv_relabel_dict[params])
                    else:
                        task_list.append((task_label + str(tasks), diff_split_single_vertex_relabel, params, False, sv_rel_depend))
                        sv_relabel_dict[params] = task_label + str(tasks)
                        target_depend[target_ind].append(task_label + str(tasks))
                        tasks += 1
                for params in ind_dict_list:
                    if params in ind_dict_dict:
                        if not ind_dict_dict[params] in target_depend[target_ind]:
                            target_depend[target_ind].append(ind_dict_dict[params])
                    else:
                        task_list.append((task_label + str(tasks), relabel_basis_dict, params, False, ()))
                        ind_dict_dict[params] = task_label + str(tasks)
                        target_depend[target_ind].append(task_label + str(tasks))
                        tasks += 1

            for target_ind, target_dependencies in target_depend.items():
                task_list.append((task_label + str(tasks), diff_split_single_target, (*gnpir, target_ind), False, target_dependencies + as_target_depend))
                combine_depend.append(task_label + str(tasks))
                tasks += 1

            # loop
            for loop_sv_rel, loop_ind_dicts in loop_sss:
                if loop_sv_rel[:-1] in sv_dict_loop:
                    sv_rel_depend = [sv_dict_loop[loop_sv_rel[:-1]]]
                else:
                    task_list.append((task_label + str(tasks), diff_loop_single_vertex, loop_sv_rel[:-1], False, ()))
                    sv_dict_loop[loop_sv_rel[:-1]] = task_label + str(tasks)
                    sv_rel_depend = [task_label + str(tasks)]
                    tasks += 1
                if loop_sv_rel in sv_rel_dict_loop:
                    if not sv_rel_dict_loop[loop_sv_rel] in loop_depend:
                        loop_depend.append(sv_rel_dict_loop[loop_sv_rel])
                else:
                    task_list.append((task_label + str(tasks), diff_loop_single_vertex_relabel, loop_sv_rel, False, sv_rel_depend))
                    sv_rel_dict_loop[loop_sv_rel] = task_label + str(tasks)
                    loop_depend.append(task_label + str(tasks))
                    tasks += 1
                for params in loop_ind_dicts:
                    if params in ind_dict_dict:
                        if not ind_dict_dict[params] in loop_depend:
                            loop_depend.append(ind_dict_dict[params])
                    else:
                        task_list.append((task_label + str(tasks), relabel_basis_dict, params, False, ()))
                        ind_dict_dict[params] = task_label + str(tasks)
                        loop_depend.append(task_label + str(tasks))
                        tasks += 1

        task_list.append((task_label + str(tasks), diff_loop_product_basis, gnpir, False, loop_depend + as_target_depend))
        combine_depend.append(task_label + str(tasks))
        tasks += 1

        as_param = (g, n, p, r, tuple([1] * n))

        if as_param in as_basis_dict:
            combine_depend.append(as_basis_dict[as_param])
        else:
            task_list.append((task_label + str(tasks), as_basis_scheduler, as_param, True, ()))
            as_basis_dict[as_param] = task_label + str(tasks)
            combine_depend.append(task_label + str(tasks))
            tasks += 1

        task_list.append((task_label + str(tasks), GK_image_single_gamma, gnpir, False, combine_depend))
        gamma_dict[(g, n, p, r)].append(task_label + str(tasks))
        tasks += 1

    image_dict = {}
    for gnpr, dependencies in gamma_dict.items():
        task_list.append((task_label + str(tasks), GK_image, (*gnpr, tuple([1] * gnpr[1])), False, dependencies))
        image_dict[gnpr] = task_label + str(tasks)
        tasks += 1

    tasks_wh = []
    for g, n, p, q in gnpqs:
        dim = 3 * g - 3 + n
        r = dim - q
        if p == 0:
            dependencies = []
        else:
            dependencies = [image_dict[(g, n, p - 1, r)]]
        if dim == r + p:
            as_param = (g, n, p, r, tuple([1] * n))
            if as_param in as_basis_dict:
                dependencies.append(as_basis_dict[as_param])
            else:
                task_list.append((task_label + str(tasks), as_basis_scheduler, as_param, True, ()))
                as_basis_dict[as_param] = task_label + str(tasks)
                dependencies.append(task_label + str(tasks))
                tasks += 1
        else:
            dependencies.append(image_dict[(g, n, p, r)])

        task_list.append((task_label + str(tasks), compute_wH, (g, n, p, q, tuple([1] * n), False), False, dependencies))
        tasks_wh.append(task_label + str(tasks))
        tasks += 1

    return task_list, tasks_wh, False


def slow_as_bases_computation(gns_list, nonsym_case, num_cpu=None, verbose=False, check_only=False):
    # this is currently missing some cases
    for g, n, D, GK, rowdict in gns_list:
        dim = 3 * g - 3 + n
        for p, q, dss in get_pq(g, n, D, GK, nonsym_case, rowdict=rowdict):
            if nonsym_case:
                n_parts = (tuple([1] * n),)
            else:
                n_parts = reversed(Partitions(n))
            for pn_part in n_parts:
                n_part = tuple(pn_part)
                prset = []
                if compute_wH.file_exists(g, n, p, q, n_part):
                    continue
                if dss:
                    r = q - p
                    prset.append((p, r))
                    if p != q and r != 0 and nonsym_case:
                        prset.append((p + 1, r - 1))
                    if p != 0:
                        prset.append((p - 1, r + 1))
                else:
                    r = dim - q
                    prset.append((p, r))
                    if p != q:
                        prset.append((p + 1, r))
                    if p != 0 and nonsym_case:
                        prset.append((p - 1, r))
                for pp, r in set(prset):
                    if check_only:
                        print('--------')
                        print(pp, r, n_part, dss)
                        with shelve.open(os.path.join(DOT_SAGE, f'admcycles/cohomology/as_bases_{g}_{n}_{pp}_{r}_{n_part}'), 'r') as file:
                            if 'finished' in file:
                                print('finished')
                            else:
                                print('finished not in file')
                    else:
                        if num_cpu is None:
                            if r != 0:
                                num_cpu = min(QQ((60, r)).floor() + 3, QQ((65 * 4, pp + 1)))
                            else:
                                num_cpu = min(63, QQ((65 * 4, pp + 1)))
                        run_tasks(as_basis_scheduler, (g, n, pp, r, n_part), hard_max_cpu=num_cpu, soft_max_cpu=num_cpu, bottleneck_scheduling=False, verbose=verbose)
    return


def full_scheduler_ct_rt(task_label, g, n, nr_push_rows, GK, rowdict, no_sym, moduli_type):
    # be sure to check if st case has already been done
    tasks = 0
    task_list = []
    total_dim = 3 * g - 3 + n
    inherited_dependencies = []
    if no_sym:
        parts = [(1,) * n]
    else:
        parts = [tuple(par) for par in Partitions(n)[:-1]]
    for n_part in parts:
        image_dic = {}
        asb_task_nrs = {}
        for p, q, pushforward in get_pq(g, n, nr_push_rows, GK, no_sym, rowdict=rowdict, moduli_type=moduli_type):
            if compute_wH.file_exists(g, n, p, q, n_part, moduli_type=moduli_type):
                continue
            if pushforward:
                r = q - p
                prs = [(p, r)]
                if r > 0:
                    prs.append((p + 1, r - 1))
                for pp, rr in prs:
                    prs2 = [(pp, rr)]
                    if pp > 0:
                        prs2.append((pp - 1, rr + 1))
                    im_deps = []
                    for p2, r2 in prs2:
                        if not (p2, r2) in asb_task_nrs:
                            asb_task_nrs[(p2, r2)] = task_label + str(tasks)
                            task_list.append((task_label + str(tasks), as_basis_scheduler, (g, n, p2, r2, n_part), True, ()))
                            tasks += 1
                        im_deps.append(asb_task_nrs[(p2, r2)])
                    image_dic[(pp, q, pushforward)] = task_label + str(tasks)
                    if len(n_part) == sum(n_part):
                        assert (compute_image.file_exists(g, n, pp, rr, False, 'sm'))
                    task_list.append((task_label + str(tasks), image_scheduler, (g, n, pp, rr, n_part, moduli_type, False), True, im_deps))
                    tasks += 1
            else:
                r = total_dim - q
                ps = [p]
                if p > 0:
                    ps.append(p - 1)
                for pp in ps:
                    ps2 = [pp]
                    if pp + r < total_dim:
                        ps2.append(pp + 1)
                    im_deps = []
                    for p2 in ps2:
                        if not (p2, r) in asb_task_nrs:
                            asb_task_nrs[(p2, r)] = task_label + str(tasks)
                            task_list.append((task_label + str(tasks), as_basis_scheduler, (g, n, p2, r, n_part), True, ()))
                            tasks += 1
                        im_deps.append(asb_task_nrs[(p2, r)])
                    image_dic[(pp, q, pushforward)] = task_label + str(tasks)
                    if len(n_part) == n:
                        assert (GK_image_rank.file_exists(g, n, pp, r, n_part, 'sm'))
                    task_list.append((task_label + str(tasks), GK_image_scheduler, (g, n, pp, r, n_part, moduli_type), True, im_deps))
                    tasks += 1

        for p, q, pushforward in get_pq(g, n, nr_push_rows, GK, no_sym, rowdict=rowdict, moduli_type=moduli_type):
            if compute_wH.file_exists(g, n, p, q, n_part, moduli_type=moduli_type):
                continue
            ps = [p]
            if pushforward:
                r = q - p
                if p < q:
                    ps.append(p + 1)
            else:
                r = total_dim - q
                if p > 0:
                    ps.append(p - 1)
            if not (p, r) in asb_task_nrs:
                asb_task_nrs[(p, r)] = task_label + str(tasks)
                task_list.append((task_label + str(tasks), as_basis_scheduler, (g, n, p, r, n_part), True, ()))
                tasks += 1
            dependencies = [asb_task_nrs[(p, r)]]
            dependencies += [image_dic[(pp, q, pushforward)] for pp in ps]
            task_list.append((task_label + str(tasks), compute_wH, (g, n, p, q, n_part, pushforward, moduli_type), False, dependencies))
            inherited_dependencies.append(task_label + str(tasks))
            tasks += 1
    return task_list, inherited_dependencies, False
