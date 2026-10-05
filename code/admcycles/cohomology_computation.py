from sage.env import DOT_SAGE
import os
from . import file_cache

from sage.combinat.all import Partitions
from sage.rings.all import QQ, PolynomialRing
from sage.combinat.sf.sf import SymmetricFunctions
from sage.combinat.integer_vector import IntegerVectors

from .mp_manager import set_context
from multiprocessing import Queue, Process, Pool, cpu_count

from .log_setup import log_setup
import logging

from . import DR
from .DR.symmetry import symmetrize_map
from .pushforward_spectral_sequence import pushforward_E2_rank
from .pullback_spectral_sequence import pullback_E2_rank
from .antisymmetry import generating_indices_in_cache
from .list_strata import list_strata_can
from .symmetry import less_symmetric_partitions
from .utils import get_marks_part


@file_cache.file_cached_function(
    directory=os.path.join(DOT_SAGE, "admcycles/cohomology"),
    key=file_cache.ignore_args_key([5]),
    filename=file_cache.ignore_args_filename())
def compute_wH(g, n, p, q, n_part, pushforward=True, moduli_type='sm'):
    r"""
    Compute E_2^{-p, q} of the pushforward spectral sequence or
    equivalently compute E_2^{p, q} of the pullback spctral sequence.
    w.l.o.g. we take q in complex dimension because the answer
    is 0 when it would be odd (in real dimension).
    """
    if n_part is None:
        raise ValueError("give trivial partition for non-symmetric case")
    if pushforward:
        return pushforward_E2_rank(g, n, p, q, n_part, moduli_type)
    else:
        return pullback_E2_rank(g, n, p, q, n_part, moduli_type)


def get_pq(g, n, nr_push_rows, nr_pull_rows, nonsym, rowdict={}, moduli_type='sm'):
    r"""
    Returns a list of p and q for which the spectral sequence does
    not trivially vanish by dimension argument.

    If ``nonsym`` is False then we assume the nonsymmetric case has already been
    computed and we only return those p and q for which the second page is nonzero.

    ``rowdict`` is a dictionary that maps a row number (the q for the pullback
    spectral sequence) to a tuple of two lists of p for which we want to do the
    computation using the pushforward (respectively pullback) spectral sequence.
    """
    dim = 3 * g - 3 + n
    if nr_push_rows is None:
        if nr_pull_rows is None:
            raise ValueError
        nr_push_rows = dim + 1 - nr_pull_rows
    if nr_pull_rows is None:
        nr_pull_rows = dim + 1 - nr_push_rows

    results = []
    k_boundary = 4 * g - 4 + n
    if n == 0:
        k_boundary -= 2
    if n == 1:
        k_boundary -= 1
    if g == 5 and n == 0:
        k_boundary = 12
    for q in range(dim + 1):
        if q >= nr_push_rows and dim - q >= nr_pull_rows:
            continue
        for p in range(0, q + 1):
            if not nonsym:
                if not compute_wH.file_exists(g, n, p, q, tuple([1] * n), moduli_type=moduli_type):
                    raise ValueError("first compute non-symmetric case")
                if not compute_wH(g, n, p, q, tuple([1] * n), moduli_type=moduli_type):
                    continue
            if q in rowdict:
                if p in rowdict[q][0]:
                    results.append((p, q, True))
                elif p in rowdict[q][1]:
                    results.append((p, q, False))
            else:
                results.append((p, q, q < nr_push_rows))
    return results


######################################
# doing the full computations
######################################

def compute_weight_graded_pieces(gns, soft_num_cpu=None, hard_num_cpu=None, pairing_chunksize=100, verbose=False, skip_symmetry=False, barrels_only=False, dss_precompute_image_matrix=False, slow_as_bases_precompute=False, moduli_type='sm'):
    r"""
    Goes through all the steps of the computation of the weight graded pieces of cohomology.

    INPUT:

    gns : a list of tuples ``(g, n, nr_push_rows, nr_pull_rows, rowdict)`` for which we do the computation.
      Here ``rowdict`` can be left out.

      ``nr_push_rows`` and ``nr_pull_rows`` determine which rows will be computed using
      the pushforward (respectively the pullback) spectral sequence.
      They correspond to q in the paper.
      One of them can be set to None and it will do all rows not covered by the other.

      ``rowdict`` is a dictionary that maps a row number (the q for the pullback
      spectral sequence) to a tuple of two lists of p for which we want to do the
      computation using the pushforward (respectively pullback) spectral sequence.

    soft_num_cpu : integer, a soft limit on the number of cores to be used
    hard_num_cpu : integer, a hard limit on the number of cores to be used
      New active processes will be started up to ``soft_num_cpu``.
      After that it starts new processes up to ``hard_num_cpu``, but only if
      there are free cores to take those tasks.

      if no cpu number is given, it is set to the number of cpu on the system

    pairing_chunksize : integer, the size of the chunks used in the computation of the perfect pairing.
      lower numbers are more memory efficient while larger numbers tend to be faster.

    moduli_type : accepts 'all', 'sm', 'rt', 'ct'. Note that for 'rt' and 'ct' it
      expects 'sm' to have already been computed.
      In the case of 'all' it will compute all 3 types.
      It also accepts a list of cases, which it will compute in order, e.g. ['sm', 'ct']
    """
    if moduli_type == 'all':
        moduli_type = ['sm', 'ct', 'rt']
    if type(moduli_type) is list:
        for mt in moduli_type:
            compute_weight_graded_pieces(gns, soft_num_cpu, hard_num_cpu, pairing_chunksize, verbose, skip_symmetry, barrels_only, dss_precompute_image_matrix, slow_as_bases_precompute, mt)
        return
    if soft_num_cpu is None:
        if hard_num_cpu is None:
            soft_num_cpu = cpu_count()
        else:
            soft_num_cpu = hard_num_cpu
    full_gns = []
    for args in gns:
        g, n, nr_push_rows, nr_pull_rows = args[:4]
        if len(args) == 5:
            rowdict = args[4]
        else:
            rowdict = {}
        dim = 3 * g - 3 + n
        if nr_push_rows is None:
            if nr_pull_rows is None:
                raise ValueError
            nr_push_rows = dim + 1 - nr_pull_rows
        elif nr_pull_rows is None:
            nr_pull_rows = dim + 1 - nr_push_rows
        full_gns.append((g, n, nr_push_rows, nr_pull_rows, rowdict))
    log_setup('scheduler')
    set_context()
    p = Process(target=precompute_things, args=(full_gns, soft_num_cpu, moduli_type))
    p.start()
    p.join()
    if p.exitcode != 0:
        raise ValueError
    logging.info('finished precomputing all_strata, symmetrize_map, and list_strata_can')
    compute_things(full_gns, True, soft_num_cpu, hard_num_cpu, pairing_chunksize, verbose, barrels_only, dss_precompute_image_matrix, slow_as_bases_precompute=slow_as_bases_precompute, moduli_type=moduli_type)
    if not skip_symmetry:
        compute_things(full_gns, False, soft_num_cpu, hard_num_cpu, pairing_chunksize, verbose, barrels_only, dss_precompute_image_matrix, slow_as_bases_precompute=slow_as_bases_precompute, moduli_type=moduli_type)
    return


def compute_things(gns, nonsymmetric, soft_num_cpu=None, hard_num_cpu=None, pairing_chunksize=100, verbose=False, barrels_only=False, dss_precompute_image_matrix=False, slow_as_bases_precompute=False, moduli_type='sm'):
    r"""
    Compute the weight spectral sequence in the (non)symmetric case after ``precompute things`` has been called.
    """
    from .relation_computation import compute_relations
    from .task_scheduling import compute_gns
    if soft_num_cpu is None:
        if hard_num_cpu is None:
            soft_num_cpu = cpu_count()
        else:
            soft_num_cpu = hard_num_cpu
    logging.info('computing cases gns = ' + str(gns))
    logging.info(f'symmetry included: {not nonsymmetric}')
    queue = Queue()
    p = Process(target=compute_missing_relations_gns, args=(gns, nonsymmetric, queue, soft_num_cpu, moduli_type))
    p.start()
    p.join()
    if p.exitcode != 0:
        raise ValueError
    missing_rels = queue.get()
    p = Process(target=compute_relations, args=(missing_rels, soft_num_cpu))
    p.start()
    p.join()
    if p.exitcode != 0:
        raise ValueError
    logging.info('finished computing missing relations')
    if not barrels_only:
        compute_gns(gns, nonsymmetric, dss_precompute_image_matrix, verbose=verbose, soft_num_cpu=soft_num_cpu, hard_num_cpu=hard_num_cpu, slow_as_bases_precompute=slow_as_bases_precompute, moduli_type=moduli_type)
    return


def precompute_things(gns, num_cpu, moduli_type):
    r'''
        precomputes ``all_strata``, ``symmetrize_map``, and ``list_strata_can``
    '''
    set_context()
    for g, n, nr_push_rows, nr_pull_rows, rowdict in gns:
        pqset = []
        total_dim = 3 * g - 3 + n
        for p, q, dss in get_pq(g, n, nr_push_rows, nr_pull_rows, True, rowdict=rowdict, moduli_type=moduli_type):
            if dss:
                r = q - p
                pqset += [(p - 1, r + 1), (p, r), (p + 1, r - 1)]
            else:
                r = total_dim - q
                pqset += [(p - 1, r), (p, r), (p + 1, r)]
        pqset = set([(a, b) for a, b in pqset if a >= 0 and b >= 0 and a + b <= total_dim])
        pset = set([a for a, b in pqset])
        for p in pset:
            if not list_strata_can.file_exists(g, n, p):
                print(f'calculating list_strata_can({g}, {n}, {p})')
                list_strata_can(g, n, p)
        poolargs = []
        for gamma_r, dim in pqset:
            poolargs.append((get_gnr_pq, g, n, gamma_r, dim, True))
        with Pool(processes=num_cpu, maxtasksperchild=100) as pool:
            resultlist = pool.map(star_func, poolargs)
            pool.close()
            pool.join()
        gnrset = set([x for y in resultlist for x in y])
        for g2, n2, r2, n_part, _, local_n in gnrset:
            marks = get_marks_part(n2, n_part)
            if not DR.all_strata.file_exists(g2, r2, marks):
                print(f'calculating all_strata({g2}, {r2}, {marks})')
                DR.all_strata(g2, r2, marks)
            nr2 = n_part.count(2)
            for par in Partitions(local_n):
                if len(par) == local_n:
                    continue
                new_part = [2] * nr2 + list(par) + [1] * (n2 - 2 * nr2 - local_n)
                new_part.sort(reverse=True)
                new_marks = less_symmetric_partitions(new_part)[n_part]
                if not symmetrize_map.file_exists(g2, r2, marks, new_marks, 3):
                    print(f'calculating symmetrize_map({g2}, {r2}, {marks}, {new_marks}, 3)')
                    symmetrize_map(g2, r2, marks, new_marks, 3)
    return


######################################
# missing bar relations
######################################

def compute_missing_relations_gns(gns, nonsymmetric, queue, num_cpu=16, moduli_type='sm'):
    r"""
    Aggregates results from ``list_missing_relations_data_E2``.
    """
    missing_rels = []
    for g, n, nr_push_rows, nr_pull_rows, rowdict in gns:
        missing_rels += list_missing_relations_data_E2(g, n, nr_push_rows, nr_pull_rows, nonsymmetric, rowdict, num_cpu=num_cpu, moduli_type=moduli_type)
    queue.put(missing_rels)
    return


def list_missing_relations_data_E2(g, n, nr_push_rows, nr_pull_rows, nonsymmetric, rowdict={}, num_cpu=1, moduli_type='sm'):
    r"""
    Returns a list of ``g, n, r, n_part, self_edges`` for which we need to compute
    (S_{g,n}^r/P_{g,n}^r)^((S_2 \wraith S_{``self_edges``}) \otimes (S_{``n_part``}/S_2^{``self_edges``}))
    """
    pqset = []
    total_dim = 3 * g - 3 + n
    for p, q, dss in get_pq(g, n, nr_push_rows, nr_pull_rows, nonsymmetric, rowdict=rowdict, moduli_type=moduli_type):
        if dss:
            r = q - p
            pqset += [(p - 1, r + 1), (p, r), (p + 1, r - 1)]
        else:
            r = total_dim - q
            pqset += [(p - 1, r), (p, r), (p + 1, r)]
    pqset = set([(a, b) for a, b in pqset if a >= 0 and b >= 0 and a + b <= total_dim])

    poolargs = []
    for gamma_r, dim in pqset:
        poolargs.append((get_gnr_pq, g, n, gamma_r, dim, True))
    with Pool(processes=num_cpu, maxtasksperchild=100) as pool:
        resultlist = pool.map(star_func, poolargs)
        pool.close()
        pool.join()
    gnrset = set([x for y in resultlist for x in y])
    result = []
    for g2, n2, r2, n_part, self_edges, local_n in gnrset:
        if nonsymmetric:
            if not generating_indices_in_cache(g2, n2, r2, n_part, self_edges):
                result.append((g2, n2, r2, n_part, self_edges))
            continue
        nr2 = n_part.count(2)
        for par in Partitions(local_n):
            n_part2 = [2] * nr2 + list(par) + [1] * (n2 - 2 * nr2 - local_n)
            n_part2.sort(reverse=True)
            n_part2 = tuple(n_part2)
            if not generating_indices_in_cache(g2, n2, r2, n_part2, self_edges):
                result.append((g2, n2, r2, n_part2, self_edges))
    return set(result)


def get_gnr_pq(g, n, gamma_r, dim, local_pts=False):
    gnr = []
    for gamma in list_strata_can(g, n, gamma_r):
        rmax = [3 * gv - 3 + gamma.num_legs(v) for v, gv in enumerate(gamma.genera())]
        for r_split in IntegerVectors(dim, len(rmax), outer=rmax):
            gnr += get_gnrs(gamma, r_split, local_pts)
    return gnr


def get_gnrs(gamma, r_split, local_pts=False):
    gnrs_list = []
    n = gamma.n()
    for v, gv in enumerate(gamma.genera()):
        nv = len(gamma.legs(v))
        self_edges = len(gamma.edges_between(v, v))
        n_part = [2] * self_edges + [1] * (nv - 2 * self_edges)
        if local_pts:
            local_n = len([l for l in gamma.legs(v) if l <= n])
            gnrs_list.append((gv, nv, r_split[v], tuple(n_part), self_edges, local_n))
        else:
            gnrs_list.append((gv, nv, r_split[v], tuple(n_part), self_edges))
    return gnrs_list


def star_func(func_args):
    return func_args[0](*func_args[1:])

######################################
# presenting the results:
######################################


def hodge_serre_poly(g, n, nr_push_rows=None, nr_pull_rows=None, compact_cohomology=True, irreducible_representations=True, euler_char=False, partially_computed=False, moduli_type='sm'):
    r"""
    Gathers precomputed weight graded pieces of cohomology into the Hodge Serre
    polynomial of M_{g,n}=M_{g,n}^sm, M_{g,n}^rt, or M_{g,n}^ct.
    If the weight graded pieces have not been computed yet use ``compute_weight_graded_pieces`` first.

    INPUT:

    irreducible_representations : boolean
      if True state the result in terms of the irreducible representations of S_n
      if False state the result in terms of the action by S_\lambda = \prod S_{\lambda_i}

    ``nr_push_rows`` and ``nr_pull_rows`` can be used to exclude some weights from the range.

    moduli_type : accepts 'sm', 'rt', 'ct'.
    """

    if nr_push_rows is None and nr_pull_rows is None:
        nr_push_rows = 0
    set_context()
    R = PolynomialRing(QQ, 2, ('t', 'L'))
    t, L = R.gens()
    if euler_char:
        t = -1
    m = SymmetricFunctions(R).monomial()
    hsp = 0
    dim = 3 * g - 3 + n
    for par in Partitions(n):
        for p, q, _ in get_pq(g, n, nr_push_rows, nr_pull_rows, len(par) == n, moduli_type=moduli_type):
            if not compute_wH.file_exists(g, n, p, q, tuple(par), moduli_type=moduli_type):
                assert (partially_computed)
                continue
            L_power = q
            t_power = 2 * q - p
            if compact_cohomology:
                L_power = dim - L_power
                t_power = 2 * dim - t_power
            term = compute_wH(g, n, p, q, tuple(par), moduli_type=moduli_type) * L ** L_power * t ** t_power
            if n > 0:
                term *= m(par)
            hsp += term

    if irreducible_representations and n > 0:
        s = SymmetricFunctions(R).schur()
        hsp = s(hsp)
    return hsp

####################################
# verify Pixton conjecture
####################################


def verify_Pixton_conjecture_everything(gns, num_cpu=10):
    from .relation_computation import verify_Pixton_conjecture
    r"""
    verify the Pixton conjecture in the cases appearing in the weight spectral sequence for the
    tuples in ``gns``. See the docstring for ``compute_everything``.

    When we want to verify the Pixton conjecture for
    (S_{g,n}^r/P_{g,n}^r)^((S_2 \wraith S_{``self_edges``}) \otimes (S_{``n_part``}/S_2^{``self_edges``}))
    it is enough to verify it for
    (S_{g,n}^r/P_{g,n}^r)^(S_{``n_part``}).
    This function verifies the latter in all relevant cases where the required data has been computed.
    The cases where the required data is missing are returned as output.

    OUTPUT:

    A list of cases for which we need to separately verify the Pixton conjecture.
    We have verified these cases separately using the function verify_Pixton_conjecture_modp in relations.py.
    We do not call verify_Pixton_conjecture_modp here because it can be memory and runtime intensive.
    """

    full_gns = []
    for args in gns:
        g, n, nr_push_rows, nr_pull_rows = args[:4]
        if len(args) == 5:
            rowdict = args[4]
        else:
            rowdict = {}
        dim = 3 * g - 3 + n
        if nr_push_rows is None:
            if nr_pull_rows is None:
                raise ValueError
            nr_push_rows = dim + 1 - nr_pull_rows
        elif nr_pull_rows is None:
            nr_pull_rows = dim + 1 - nr_push_rows
        full_gns.append((g, n, nr_push_rows, nr_pull_rows, rowdict))

    need_to_compute = []
    for g, n, nr_push_rows, nr_pull_rows, rowdict in full_gns:
        pqset = []
        total_dim = 3 * g - 3 + n
        for p, q, dss in get_pq(g, n, nr_push_rows, nr_pull_rows, True, rowdict=rowdict):
            if dss:
                r = q - p
                pqset += [(p - 1, r + 1), (p, r), (p + 1, r - 1)]
            else:
                r = total_dim - q
                pqset += [(p - 1, r), (p, r), (p + 1, r)]
        pqset = set([(a, b) for a, b in pqset if a >= 0 and b >= 0 and a + b <= total_dim])
        poolargs = []
        for gamma_r, dim in pqset:
            poolargs.append((get_gnr_pq, g, n, gamma_r, dim))
        with Pool(processes=num_cpu, maxtasksperchild=100) as pool:
            resultlist = pool.map(star_func, poolargs)
            pool.close()
            pool.join()
        gnrset = set([x[:-1] for y in resultlist for x in y])
        for gnrp in gnrset:
            if gnrp[0] < 2:
                continue
            if generating_indices_in_cache(*gnrp):
                verify_Pixton_conjecture(*gnrp)
            else:
                need_to_compute.append(gnrp)
    return need_to_compute
