r"""
Faber-Zagier relations and pairing in tautological ring
"""
from copy import copy
import itertools
from itertools import islice, zip_longest

# from memory_profiler import profile
from functools import lru_cache

from sage.misc.cachefunc import cached_function
from sage.modules.free_module import span
from sage.rings.integer_ring import ZZ
from sage.rings.rational_field import QQ
from sage.matrix.constructor import matrix
from sage.functions.other import floor
from sage.combinat.partition import Partitions
from sage.combinat.integer_vector import IntegerVectors
from sage.combinat.permutation import Permutations
from sage.modules.free_module_element import vector

from .algebra import multiply, insertion_pullback, kappa_multiple, psi_multiple, get_marks
from .graph import all_strata, num_strata, contraction_table, unpurify_map, single_stratum, autom_count, graph_count_automorphisms, R, X, Graph, num_of_stratum, graph_isomorphic
from .evaluation import socle_evaluation
from .moduli import MODULI_SM, MODULI_ST, MODULI_SMALL, dim_form
from .utils import get_memory_usage, dprint, remove_duplicates, subsequences, A_list, B_list, aut, simplify_sparse
from .symmetry import symmetrize_map, partial_unsymmetrize_vec, unsymmetrize_vec

from .. import file_cache
from sage.env import DOT_SAGE
import os

from multiprocessing import Pool


def gorenstein_precompute(g, r1, markings=(), moduli_type=MODULI_ST):
    r3 = dim_form(g, len(markings), moduli_type)
    r2 = r3 - r1
    all_strata(g, r1, markings, moduli_type)
    all_strata(g, r2, markings, moduli_type)
    contraction_table(g, r3, markings, moduli_type)
    unpurify_map(g, r3, markings, moduli_type)


def pairing_matrix(g, r1, markings=(), moduli_type=MODULI_ST):
    r"""
    Return the pairing matrix for the given genus, degree, markings and
    moduli type.

    EXAMPLES::

        sage: from admcycles.DR import pairing_matrix
        sage: pairing_matrix(1, 1, (1, 1))
        [[1/4, 1/6, 1/12, 2], [1/6, 1/12, 0, 2], [1/12, 0, -1/12, 2], [2, 2, 2, 0]]
    """
    r3 = dim_form(g, len(markings), moduli_type)
    r2 = r3 - r1
    ngens1 = num_strata(g, r1, markings, moduli_type)
    ngens2 = num_strata(g, r2, markings, moduli_type)
    ngens3 = num_strata(g, r3, markings, moduli_type)
    socle_evaluations = [socle_evaluation(
        i, g, markings, moduli_type) for i in range(ngens3)]
    pairings = [[0 for i2 in range(ngens2)] for i1 in range(ngens1)]
    sym = bool(r1 == r2)
    for i1 in range(ngens1):
        for i2 in range(ngens2):
            if sym and i1 > i2:
                pairings[i1][i2] = pairings[i2][i1]
                continue
            L = multiply(r1, i1, r2, i2, g, r3, markings, moduli_type)
            pairings[i1][i2] = sum([L[k] * socle_evaluations[k]
                                    for k in range(ngens3)])
    return pairings


def pairing_submatrix(S1, S2, g, r1, markings=(), moduli_type=MODULI_ST):
    r3 = dim_form(g, len(markings), moduli_type)
    r2 = r3 - r1
    # ngens1 = num_strata(g, r1, markings, moduli_type)
    # ngens2 = num_strata(g, r2, markings, moduli_type)
    ngens3 = num_strata(g, r3, markings, moduli_type)
    socle_evaluations = [socle_evaluation(
        i, g, markings, moduli_type) for i in range(ngens3)]
#    socle_evaluations = socle_evals(g, markings, moduli_type)
    pairings = [[0 for i2 in S2] for i1 in S1]
    sym = bool(r1 == r2 and S1 == S2)
    for i1 in range(len(S1)):
        for i2 in range(len(S2)):
            if sym and i1 > i2:
                pairings[i1][i2] = pairings[i2][i1]
                continue
            L = multiply(r1, S1[i1], r2, S2[i2], g, r3, markings, moduli_type)
            pairings[i1][i2] = sum([L[k] * socle_evaluations[k]
                                    for k in range(ngens3)])
    return pairings


def betti(g, r, marked_points=(), moduli_type=MODULI_ST):
    """
    This function returns the predicted rank of the codimension r grading
    of the tautological ring of the moduli space of stable genus g curves
    with marked points labeled by the multiset marked_points.

    g and r should be nonnegative integers and marked_points should be a
    tuple of positive integers.

    The parameter moduli_type determines which moduli space to use:
    - MODULI_ST: all stable curves (this is the default)
    - MODULI_CT: curves of compact type
    - MODULI_RT: curves with rational tails
    - MODULI_SM: smooth curves

    EXAMPLES::

        sage: from admcycles.DR import betti

    Check rank R^3(bar{M}_2) = 1::

        sage: betti(2, 3)
        1

    Check rank R^2(bar{M}_{2,3}) = 44::

        sage: betti(2, 2, (1,2,3))  # long time
        44

    Check rank R^2(bar{M}_{2,3})^{S_3} = 20::

        sage: betti(2, 2, (1,1,1))  # long time
        20

    Check rank R^2(bar{M}_{2,3})^{S_2} = 32 (S_2 interchanging markings 1 and 2)::

        sage: betti(2, 2, (1,1,2))  # long time
        32

    Check rank R^2(M^c_4) = rank R^3(M^c_4) = 6::

        sage: from admcycles.DR import MODULI_CT, MODULI_RT, MODULI_SM
        sage: betti(4, 2, (), MODULI_CT)
        6
        sage: betti(4, 3, (), MODULI_CT)  # long time
        6

    We can use this to check that rank R^8(M^rt_{17,2})^(S_2)=122 < R^9(M^rt_{17,2})^(S_2) = 123.
    Indeed, betti(17,8,(1,1),MODULI_RT) = 122 and betti(17,9,(1,1),MODULI_RT)=123
    Similarly, we have rank R^9(M_{20,1}) = 75 < rank R^10(M_{20,1}) = 76
    Indeed, betti(20,9,(1,),MODULI_SM) = 75 and betti(20,10,(1,),MODULI_SM) = 76.
    """
    L = list_all_FZ(g, r, marked_points, moduli_type)
    L.reverse()
    return (len(L[0]) - compute_rank(L))


def gorenstein(g, r, marked_points=(), moduli_type=MODULI_ST):
    """
    This function returns the rank of the codimension r grading of the
    Gorenstein quotient of the tautological ring of the moduli space of genus g
    curves with marked points labeled by the multiset marked_points.

    g and r should be nonnegative integers and marked_points should be a
    tuple of positive integers.

    The parameter moduli_type determines which moduli space to use:
    - MODULI_ST: all stable curves (this is the default)
    - MODULI_CT: curves of compact type
    - MODULI_RT: curves with rational tails

    EXAMPLES::

        sage: from admcycles.DR.relations import gorenstein

    Check rank Gor^3(bar{M}_{3}) = 10::

        sage: gorenstein(3, 3)  # long time
        10

    Check rank Gor^2(bar{M}_{2,2}) = 14::

        sage: gorenstein(2, 2, (1,2))  # long time
        14

    Check rank Gor^2(bar{M}_{2,2})^{S_2} = 11::

        sage: gorenstein(2, 2, (1,1))  # long time
        11

    Check rank Gor^2(M^c_{4}) = 6::

        sage: from admcycles.DR import MODULI_CT, MODULI_RT

        sage: gorenstein(4, 2, (), MODULI_CT)  # long time
        6

    Check rank Gor^4(M^rt_{8,2}) = 22::

        sage: gorenstein(8, 4, (1,2), MODULI_RT)  # long time
        22
    """
    gorenstein_precompute(g, r, marked_points, moduli_type)
    r3 = dim_form(g, len(marked_points), moduli_type)
    r2 = r3 - r
    S1 = good_generator_list(g, r, marked_points, moduli_type)
    S2 = good_generator_list(g, r2, marked_points, moduli_type)
    M = pairing_submatrix(tuple(S1), tuple(S2), g, r,
                          marked_points, moduli_type)
    return matrix(M).rank()


def recursive_betti(g, r, markings=(), moduli_type=MODULI_ST):
    """
    EXAMPLES::

        sage: from admcycles.DR.relations import recursive_betti
        sage: recursive_betti(2, 3)  # not tested
        ?
    """
    from .utils import dprint, dsave
    dprint("Start recursive_betti (%s,%s,%s,%s): %s", g, r,
           markings, moduli_type, floor(get_memory_usage()))
    n = len(markings)
    if r > dim_form(g, n, moduli_type):
        return 0
    ngen = num_strata(g, r, markings, moduli_type)
    dprint("%s gens", ngen)
    relations = []
    partial_sym_map = symmetrize_map(g, r, get_marks(n, 0), markings, moduli_type)
    for rel in [unsymmetrize_vec(br, g, r, get_marks(n, 0), moduli_type)
                for br in choose_basic_rels(g, r, n, moduli_type)]:
        rel2 = []
        for x in rel:
            rel2.append([partial_sym_map[x[0]], x[1]])
        rel2 = simplify_sparse(rel2)
        relations.append(rel2)
    for rel in interior_derived_rels(g, r, n, 0, moduli_type):
        rel2 = []
        for x in rel:
            rel2.append([partial_sym_map[x[0]], x[1]])
        rel2 = simplify_sparse(rel2)
        relations.append(rel2)
    dprint("%s gens, %s rels so far", ngen, len(relations))
    dprint("Middle recursive_betti (%s,%s,%s,%s): %s", g, r,
           markings, moduli_type, floor(get_memory_usage()))
    if moduli_type > MODULI_SM:
        for r0 in range(1, r):
            strata = all_strata(g, r0, markings, moduli_type)
            for G in strata:
                vertex_orbits = graph_count_automorphisms(G, True)
                for i in [orbit[0] for orbit in vertex_orbits]:
                    good = True
                    for j in range(G.M.ncols()):
                        if R(G.M[i, j][0]) != G.M[i, j]:
                            good = False
                            break
                    if good:
                        g2 = G.M[i, 0][0]
                        if 3 * (r - r0) < g2 + 1:
                            continue
                        d = G.degree(i)
                        if dim_form(g2, d, moduli_type) < r - r0:
                            continue
                        strata2 = all_strata(
                            g2, r - r0, tuple(range(1, d + 1)), moduli_type)
                        which_gen_list = [
                            -1 for num in range(len(strata2))]
                        for num in range(len(strata2)):
                            G_copy = Graph(G.M)
                            G_copy.replace_vertex_with_graph(i, strata2[num])
                            which_gen_list[num] = num_of_stratum(
                                G_copy, g, r, markings, moduli_type)
                        rel_list = [unsymmetrize_vec(br, g2, r - r0,
                                    get_marks(d, 0), moduli_type) for br in
                                    choose_basic_rels(g2, r - r0, d, moduli_type)]
                        rel_list += interior_derived_rels(g2,
                                                          r - r0, d, 0, moduli_type)
                        for rel0 in rel_list:
                            relation = []
                            for x in rel0:
                                num = x[0]
                                if which_gen_list[num] != -1:
                                    relation.append(
                                        [which_gen_list[num], x[1]])
                            relation = simplify_sparse(relation)
                            relations.append(relation)
    dprint("%s gens, %s rels", ngen, len(relations))
    dsave("sparse-%s-gens-%s-rels", ngen, len(relations))
    dprint("Middle recursive_betti (%s,%s,%s,%s): %s", g, r,
           markings, moduli_type, floor(get_memory_usage()))
    relations = remove_duplicates(relations)
    nrels = len(relations)
    dprint("%s gens, %s distinct rels", ngen, nrels)
    dsave("sparse-%s-distinct-rels", nrels)
    rank = 0
    D = {}
    for i, reli in enumerate(relations):
        for x in reli:
            D[i, x[0]] = x[1]
    if nrels:
        row_order, col_order = choose_orders_sparse(D, nrels, ngen)
        rank = compute_rank_sparse(D, row_order, col_order)
    dsave("sparse-answer-%s", ngen - rank)
    return ngen - rank


def FZ_rels(g, r, markings=(), moduli_type=MODULI_ST):
    r"""
    EXAMPLES::

        sage: from admcycles.DR.relations import FZ_rels
        sage: FZ_rels(2, 2)
        [
        (1, 0, 0, 0, 0, 0, -1/20, -1/480),
        (0, 1, 0, 0, 0, 0, -5/24, -1/96),
        (0, 0, 1, 0, 0, 0, -1/24, 0),
        (0, 0, 0, 1, 0, 0, -1/24, 0),
        (0, 0, 0, 0, 1, 0, -1, -1/12),
        (0, 0, 0, 0, 0, 1, -1, -1/24)
        ]
    """
    return span(FZ_matrix(g, r, markings, moduli_type)).basis()


# remove this and use rels_matrix instead?
def FZ_matrix(g, r, markings=(), moduli_type=MODULI_ST):
    r"""
    EXAMPLES::

        sage: from admcycles.DR.relations import FZ_matrix
        sage: from admcycles.DR.moduli import MODULI_SM, MODULI_RT, MODULI_CT, MODULI_ST
        sage: FZ_matrix(2, 2)
        [     60     -60      84       0       6       0       0       0]
        [ 473760 -100512   33984  -10080    6624  -10080    -288     -72]
        [ 115920  -12240   13536   -5040    1584   -5040    -144     -36]
        [      0       0     102     -30       0       0      -3       0]
        [      0       0      30      42       0       0      -3       0]
        [      0       0       0       0      66     -60      -6      -3]
        [      0       0       0       0      15       6     -21    -3/2]

        sage: FZ_matrix(2, 2, (1,), MODULI_CT)
        [     30     -30      30       0      42       0       0       0]
        [ 441000  -78120   61200 -138600   37296   -7920  -42840    1368]
        [ 204120  -27864  -39312   98280   20304    9072  -37800   -3672]
        [      0       0     -30      30       0      42       0       0]
        [  71820   -7020    9720  -41580    9288   -3240  -18900     756]
        [  13860    -900   -2520   16380    2520    3528  -16380   -1764]
        [      0       0       0       0      66     -30     -30      -6]
        [      0       0       0       0      15      21     -15     -21]
        [      0       0       0       0      15     -15      21     -21]

        sage: FZ_matrix(3, 2, (1, 2), MODULI_RT)
        [-251370   27162  -34020  -34020  145530   18900  145530   18036  -69930]
        [ -56700    4860   10584   -7560  -49140   -7560   41580   -8424   34020]
        [ -56700    4860   -7560   10584   41580   -7560  -49140   -8424   34020]
        [  -6930     450    1260    1260   -8190    1764   -8190     900   -6930]
        [  -6930     450    -900    -900    6930     900    6930     900   -6930]

        sage: FZ_matrix(3, 2, (1, 1), MODULI_SM)
        [-125685   13581  -34020  145530    9450]
        [ -56700    4860    3024   -7560   -7560]
        [  -3465     225    1260   -8190     882]
        [  -3465     225    -900    6930     450]
    """
    return matrix(list_all_FZ(g, r, markings, moduli_type))


def FZ_methods_sanity_check(g, r, n, moduli_type):
    r"""
    Check whether computing the FZ-relations via Pixton's 3-spin formula and
    by using new relations give the same result.

    TESTS::

        sage: import itertools
        sage: from admcycles.DR import FZ_methods_sanity_check, MODULI_SM, MODULI_RT, MODULI_CT, MODULI_ST
        sage: gn = [(0, 5), (1, 1), (1, 2), (1, 3), (2, 2), (3, 0), (4, 1)]
        sage: degrees = [0, 1, 2, 3]
        sage: moduli = [MODULI_SM, MODULI_RT, MODULI_CT, MODULI_ST]
        sage: for (g, n), r, moduli_type in itertools.product(gn, degrees, moduli):  # long time
        ....:     if not FZ_methods_sanity_check(g, r, n, moduli_type):
        ....:         print("ERROR: g={}, r={}, n={}, moduli_type={}".format(g, r, n, moduli_type))

        sage: all(FZ_methods_sanity_check(9, i, 0, MODULI_SM) for i in range(10))  # long time
        True
    """
    def echelon_without_zeros(M):
        M.echelonize()
        for i, r in enumerate(M.rows()):
            if r.is_zero():
                return M.matrix_from_rows(range(i))
        return M

    spin3 = rels_matrix(g, r, n, 0, moduli_type, True)
    newrels = rels_matrix(g, r, n, 0, moduli_type, False)
    return echelon_without_zeros(spin3) == echelon_without_zeros(newrels)


def list_all_FZ(g, r, markings=(), moduli_type=MODULI_ST):
    relations = copy(interior_FZ(g, r, markings, moduli_type))
    if moduli_type > MODULI_SM:
        relations += boundary_FZ(g, r, markings, moduli_type)
    if not relations:
        ngen = num_strata(g, r, markings, moduli_type)
        relations.append([0 for i in range(ngen)])
    return relations


def generate_all_FZ(g, r, markings=(), moduli_type=MODULI_ST, quiet=True, num_cpu=1):
    count = 0
    for rel in generate_interior_FZ(g, r, markings, moduli_type, num_cpu):
        count += 1
        if not quiet:
            print(f"Interior relation, total number: {count}")
        yield rel
    if moduli_type > MODULI_SM:
        for rel in generate_boundary_FZ(g, r, markings, moduli_type, num_cpu):
            count += 1
            if not quiet:
                print(f"Boundary relation, total number: {count}")
            yield rel
    if not count:
        ngen = num_strata(g, r, markings, moduli_type)
        yield [0 for i in range(ngen)]


def reduced_FZ_param_list(G, v, g, d, n):
    params = FZ_param_iter(n, tuple(range(1, d + 1)))
    graph_params = []
    M = matrix(R, 2, d + 1)
    M[0, 0] = -1
    for i in range(1, d + 1):
        M[0, i] = i
    for p in params:
        G_copy = Graph(G.M)
        M[1, 0] = -g - 1
        for j in p[0]:
            M[1, 0] += X**j
        for i in range(1, d + 1):
            M[1, i] = 1 + p[1][i - 1][1][0] * X
        G_p = Graph(M)
        G_copy.replace_vertex_with_graph(v, G_p)
        graph_params.append([p, G_copy])
    params_reduced = []
    graphs_seen = []
    for x in graph_params:
        x[1].compute_invariant()
        good = True
        for GG in graphs_seen:
            if graph_isomorphic(x[1], GG):
                good = False
                break
        if good:
            graphs_seen.append(x[1])
            params_reduced.append(x[0])
    return params_reduced


def FZ_param_iter(n, markings=()):
    r"""
    EXAMPLES::

        sage: from admcycles.DR.relations import FZ_param_list
        sage: FZ_param_list(3, ())
        [((3,), ()), ((1, 1, 1), ()), ((1,), ())]
    """
    if n < 0:
        return
    mmm = max((0,) + markings)
    markings_grouped = [0 for i in range(mmm)]
    for i in markings:
        markings_grouped[i - 1] += 1
    markings_best = []
    for i in range(mmm):
        if markings_grouped[i] > 0:
            markings_best.append([i + 1, markings_grouped[i]])
    for j in range(n // 2 + 1):
        for n_vec in IntegerVectors(n - 2 * j, 1 + len(markings_best)):
            S_list = [[list(sigma) for sigma in Partitions(n_vec[0])
                       if not any(l % 3 == 2 for l in sigma)]]
            # TODO: the line above should iterate directly over the set
            # of partitions with no parts of size = 2 (mod 3)
            for i in range(len(markings_best)):
                S_list.append(Partitions(
                    n_vec[i + 1] + markings_best[i][1], length=markings_best[i][1]).list())
                S_list[-1] = [[k - 1 for k in sigma] for sigma in S_list[-1]
                              if sum(1 for l in sigma if (l % 3) == 0) == 0]
            for S in itertools.product(*S_list):
                yield (tuple(S[0]), tuple([(markings_best[k][0], tuple(
                    S[k + 1])) for k in range(len(markings_best))]))
    return


def FZ_param_list(n, markings=()):
    r"""
    EXAMPLES::

        sage: from admcycles.DR.relations import FZ_param_list
        sage: FZ_param_list(3, ())
        [((3,), ()), ((1, 1, 1), ()), ((1,), ())]
    """
    if n < 0:
        return []
    final_list = []
    mmm = max((0,) + markings)
    markings_grouped = [0 for i in range(mmm)]
    for i in markings:
        markings_grouped[i - 1] += 1
    markings_best = []
    for i in range(mmm):
        if markings_grouped[i] > 0:
            markings_best.append([i + 1, markings_grouped[i]])
    for j in range(n // 2 + 1):
        for n_vec in IntegerVectors(n - 2 * j, 1 + len(markings_best)):
            S_list = [[list(sigma) for sigma in Partitions(n_vec[0])
                       if not any(l % 3 == 2 for l in sigma)]]
            # TODO: the line above should iterate directly over the set
            # of partitions with no parts of size = 2 (mod 3)
            for i in range(len(markings_best)):
                S_list.append(Partitions(
                    n_vec[i + 1] + markings_best[i][1], length=markings_best[i][1]).list())
                S_list[-1] = [[k - 1 for k in sigma] for sigma in S_list[-1]
                              if sum(1 for l in sigma if (l % 3) == 0) == 0]
            for S in itertools.product(*S_list):
                final_list.append((tuple(S[0]), tuple([(markings_best[k][0], tuple(
                    S[k + 1])) for k in range(len(markings_best))])))
    return final_list


def C_coeff(m, term):
    n = term - m // 3
    if n < 0:
        return 0
    if m % 3 == 0:
        return A_list[n]
    else:
        return B_list[n]


@cached_function
def dual_C_coeff(i, j, parity):
    total = ZZ.zero()
    k = parity % 2
    while k // 3 <= i:
        if k % 3 != 2:
            total += (-1)**(k // 3) * C_coeff(k, i) * C_coeff(-2 - k, j)
        k += 2
    return total


def poly_to_partition(F):
    mmm = F.degree()
    target_partition = []
    for i in range(1, mmm + 1):
        for j in range(F[i]):
            target_partition.append(i)
    return tuple(target_partition)


@cached_function
def kappa_coeff(sigma, kappa_0, target_partition):
    total = ZZ.zero()
    num_ones = sum(1 for i in sigma if i == 1)
    for i in range(0, num_ones + 1):
        for injection in Permutations(list(range(len(target_partition))), len(sigma) - i):
            term = (ZZ(num_ones).binomial(i) *
                    ZZ(kappa_0 + len(target_partition) + i - 1).binomial(i) *
                    ZZ(i).factorial())
            for j in range(len(sigma) - i):
                term *= C_coeff(sigma[j + i], target_partition[injection[j]])
            for j in range(len(target_partition)):
                if j in injection:
                    continue
                term *= C_coeff(0, target_partition[j])
            total += term
    total = (-1)**(len(target_partition) + len(sigma)) * \
        total / aut(list(target_partition))
    return total


# @cached_function
def FZ_kappa_factor(num, sigma, g, r, markings=(), moduli_type=MODULI_ST):
    G = single_stratum(num, g, r, markings, moduli_type)
    L = []
    nv = G.num_vertices()
    for i in range(1, nv + 1):
        L.append((2 * G.M[i, 0][0] + G.degree(i) -
                  2, G.M[i, 0] - G.M[i, 0][0]))
    LL = []
    tau = []
    for i in range(nv):
        mini = -1
        for j in range(nv):
            if (i == 0 or L[j] > LL[-1] or L[j] == LL[-1] and j > tau[-1]) and (mini == -1 or L[j] < L[mini]):
                mini = j
        tau.append(mini)
        LL.append(L[mini])
    factor_dict = FZ_kappa_factor2(tuple(LL), sigma)
    factor_vec = [0 for i in range(1 << nv)]
    for parity_key in factor_dict:
        parity = 0
        for i in range(nv):
            if parity_key[i] == 1:
                parity += 1 << tau[i]
        factor_vec[parity] = factor_dict[parity_key]
    return factor_vec


# @cached_function
def FZ_marking_factor(num, marking_vec, g, r, markings=(), moduli_type=MODULI_ST):
    G = single_stratum(num, g, r, markings, moduli_type)
    nv = G.num_vertices()
    ne = G.num_edges()
    num_parities = ZZ(2) ** nv
    PPP_list = []
    for marks in marking_vec:
        PPP_list.append(Permutations(marks[1]))
    PPP = itertools.product(*PPP_list)
    marking_factors = [0 for i in range(num_parities)]
    incident_vertices = []
    for mark_type in marking_vec:
        incident_vertices.append([])
        for k in range(1, ne + 1):
            if G.M[0, k] == mark_type[0]:
                for i in range(1, nv + 1):
                    if G.M[i, k] != 0:
                        incident_vertices[-1].append((i - 1, G.M[i, k][1]))
                        break
    for perms in PPP:
        parity = 0
        marking_factor = 1
        for marks_index in range(len(marking_vec)):
            for count in range(len(incident_vertices[marks_index])):
                marking_factor *= C_coeff(perms[marks_index][count],
                                          incident_vertices[marks_index][count][1])
                parity ^= (perms[marks_index][count] %
                           ZZ(2)) << incident_vertices[marks_index][count][0]
        marking_factors[parity] += marking_factor
    return marking_factors


@cached_function
def FZ_kappa_factor2(L, sigma):
    nv = len(L)
    mmm = max((0,) + sigma)
    sigma_grouped = [0 for i in range(mmm)]
    for i in sigma:
        sigma_grouped[i - 1] += 1
    S_list = []
    for i in sigma_grouped:
        S_list.append(IntegerVectors(i, nv))
    S = itertools.product(*S_list)
    kappa_factors = {}
    for parity in itertools.product(*[(0, 1) for i in range(nv)]):
        kappa_factors[tuple(parity)] = 0
    for assignment in S:
        assigned_sigma = [[] for j in range(nv)]
        for i in range(mmm):
            for j in range(nv):
                for k in range(assignment[i][j]):
                    assigned_sigma[j].append(i + 1)
        sigma_auts = 1
        parity = [0 for i in range(nv)]
        kappa_factor = ZZ.one()
        for j in range(nv):
            sigma_auts *= aut(assigned_sigma[j])
            parity[j] += sum(assigned_sigma[j])
            parity[j] %= ZZ(2)
            kappa_factor *= kappa_coeff(
                tuple(assigned_sigma[j]), L[j][0], poly_to_partition(L[j][1]))
        kappa_factors[tuple(parity)] += kappa_factor / sigma_auts
    return kappa_factors


@cached_function
def FZ_hedge_factor(num, g, r, markings=(), moduli_type=MODULI_ST):
    G = single_stratum(num, g, r, markings, moduli_type)
    nv = G.num_vertices()
    num_parities = ZZ(2) ** nv
    ne = G.num_edges()
    edge_list = []
    for k in range(1, ne + 1):
        if G.M[0, k] == 0:
            edge_list.append([k])
            for i in range(1, nv + 1):
                if G.M[i, k] != 0:
                    edge_list[-1].append(i)
                if G.M[i, k][0] == 2:
                    edge_list[-1].append(i)
    hedge_factors = [0 for i in range(num_parities)]
    for edge_parities in itertools.product(*[[0, 1] for i in edge_list]):
        parity = 0
        for i in range(len(edge_list)):
            if edge_parities[i] == 1:
                parity ^= 1 << (edge_list[i][1] - 1)
                parity ^= 1 << (edge_list[i][2] - 1)
        hedge_factor = 1
        for i in range(len(edge_list)):
            if edge_list[i][1] == edge_list[i][2]:
                hedge_factor *= dual_C_coeff(G.M[edge_list[i][1], edge_list[i][0]][1],
                                             G.M[edge_list[i][1], edge_list[i][0]][2], edge_parities[i] % ZZ(2))
            else:
                hedge_factor *= dual_C_coeff(G.M[edge_list[i][1], edge_list[i][0]][1],
                                             G.M[edge_list[i][2], edge_list[i][0]][1], edge_parities[i] % ZZ(2))
        hedge_factors[parity] += hedge_factor
    return hedge_factors


@lru_cache(maxsize=5000)
def FZ_coeff(num, FZ_param, g, r, markings=(), moduli_type=MODULI_ST):
    r"""
    EXAMPLES::

        sage: from admcycles.DR.graph import num_strata
        sage: from admcycles.DR.moduli import MODULI_ST
        sage: from admcycles.DR.relations import FZ_coeff
        sage: [FZ_coeff(i, ((3,), ()), 2, 2, (), MODULI_ST) for i in range(num_strata(2, 2))]
        [60, -60, 84, 0, 6, 0, 0, 0]
        sage: [FZ_coeff(i, ((1, 1, 1), ()), 2, 2, (), MODULI_ST) for i in range(num_strata(2, 2))]
        [473760, -100512, 33984, -10080, 6624, -10080, -288, -72]
        sage: [FZ_coeff(i, ((1,), ()), 2, 2, (), MODULI_ST) for i in range(num_strata(2, 2))]
        [115920, -12240, 13536, -5040, 1584, -5040, -144, -36]
    """
    sigma = FZ_param[0]
    marking_vec = FZ_param[1]
    G = single_stratum(num, g, r, markings, moduli_type)
    nv = G.num_vertices()
    graph_auts = autom_count(num, g, r, markings, moduli_type)
    h1_factor = ZZ(2) ** G.h1()
    num_parities = ZZ(2) ** nv

    marking_factors = FZ_marking_factor(
        num, marking_vec, g, r, markings, moduli_type)
    kappa_factors = FZ_kappa_factor(num, sigma, g, r, markings, moduli_type)
    hedge_factors = FZ_hedge_factor(num, g, r, markings, moduli_type)

    total = ZZ.zero()
    for i in range(num_parities):
        if marking_factors[i] == 0:
            continue
        for j in range(num_parities):
            total += marking_factors[i] * kappa_factors[j] * \
                hedge_factors[i ^ j ^ G.target_parity]

    total /= h1_factor * graph_auts
    return total


def interior_FZ(g, r, markings=(), moduli_type=MODULI_ST):
    r"""
    EXAMPLES::

        sage: from admcycles.DR.relations import interior_FZ
        sage: interior_FZ(2, 2)
        [(60, -60, 84, 0, 6, 0, 0, 0),
         (473760, -100512, 33984, -10080, 6624, -10080, -288, -72),
         (115920, -12240, 13536, -5040, 1584, -5040, -144, -36)]
    """
    return list(generate_interior_FZ(g, r, markings, moduli_type))


def generate_interior_FZ(g, r, markings=(), moduli_type=MODULI_ST, num_cpu=1, start=1, maxtasks=100):
    r"""
    EXAMPLES::

        sage: from admcycles.DR.relations import generate_interior_FZ
        sage: list(generate_interior_FZ(2, 2))
        [(60, -60, 84, 0, 6, 0, 0, 0),
         (473760, -100512, 33984, -10080, 6624, -10080, -288, -72),
         (115920, -12240, 13536, -5040, 1584, -5040, -144, -36)]

    TESTS::

        sage: L = list(generate_interior_FZ(2,2))
        sage: M = list(generate_interior_FZ(2,2,start=2))
        sage: (len(L), len(M))
        (3, 2)
        sage: M == L[1:]
        True
    """
    ngen = num_strata(g, r, markings, moduli_type)
    FZpl = FZ_param_iter(3 * r - g - 1, markings)
    for i in range(start - 1):
        next(FZpl)

    with Pool(processes=num_cpu, maxtasksperchild=int(maxtasks)) as pool:
        arglist = ((FZ_param, g, r, markings, moduli_type, ngen) for FZ_param in FZpl)

        imapresult = pool.imap(_interior_FZ_worker, arglist)

        for result in imapresult:
            yield result
        pool.close()
        pool.join()


def possibly_new_FZ(g, r, n=0, moduli_type=MODULI_ST):
    m = 3 * r - g - 1 - n
    if m < 0:
        return []
    dprint("Start posibly new FZ (%s,%s,%s,%s): %s", g, r, n, moduli_type,
           floor(get_memory_usage()))
    markings = (1,) * n
    ngen = num_strata(g, r, markings, moduli_type)
    relations = []
    for i in range(m + 1):
        if (m - i) % 2:
            continue
        for sigma in Partitions(i):
            # TODO: the line above should iterate directly over the set
            # of partitions with all parts of size = 1 (mod 3)
            if any(j % 3 != 1 for j in sigma):
                continue
            if n > 0:
                FZ_param = (tuple(sigma), ((1, markings),))
            else:
                FZ_param = (tuple(sigma), ())
            relation = []
            for j in range(ngen):
                coeff = FZ_coeff(j, FZ_param, g, r, markings, moduli_type)
                if coeff != 0:
                    relation.append([j, coeff])
            relations.append(relation)
    dprint("End possibly new FZ (%s,%s,%s,%s): %s", g, r, n, moduli_type,
           floor(get_memory_usage()))
    return relations


def boundary_FZ(g, r, markings=(), moduli_type=MODULI_ST):
    r"""
    EXAMPLES::

        sage: from admcycles.DR.relations import boundary_FZ
        sage: boundary_FZ(2, 2)
        [(0, 0, 102, -30, 0, 0, -3, 0),
         (0, 0, 30, 42, 0, 0, -3, 0),
         (0, 0, 0, 0, 66, -60, -6, -3),
         (0, 0, 0, 0, 15, 6, -21, -3/2)]
    """
    return (list(generate_boundary_FZ(g, r, markings, moduli_type)))


def big_boundary_FZparam(g, r, markings=(), moduli_type=MODULI_ST, record=True, start=1):
    r"""
    EXAMPLES::

        sage: from admcycles.DR.relations import boundary_FZ
        sage: boundary_FZ(2, 2)
        [(0, 0, 102, -30, 0, 0, -3, 0),
         (0, 0, 30, 42, 0, 0, -3, 0),
         (0, 0, 0, 0, 66, -60, -6, -3),
         (0, 0, 0, 0, 15, 6, -21, -3/2)]
    """
    from admcycles.admcycles import Graphtodecstratum
    if moduli_type <= MODULI_SM:
        return []
    filename = f"boundgen_{g}_{r}_{markings}_{moduli_type}.txt"
    if record:
        try:
            with open(filename, 'r') as file:
                max_stratum, max_rows = 0, 0
                for line in file:
                    max_stratum_temp, max_rows_temp, _, _ = eval(line)
                    if max_rows_temp > start - 1:
                        break
                    max_stratum, max_rows = max_stratum_temp, max_rows_temp
        except (FileNotFoundError, PermissionError, OSError):
            max_stratum, max_rows = 0, 0
    else:
        max_stratum, max_rows = 0, 0
    for i in range(max_rows):
        yield None  # give dummy outputs for the rows that will not be computed
    stratum_count = 0
    row_count = max_rows
    for r0 in range(1, r):
        strata = all_strata(g, r0, markings, moduli_type)
        for G in strata:
            stratum_count += 1
            if record and stratum_count <= max_stratum:
                continue
            vertex_orbits = graph_count_automorphisms(G, True)
            for i in [orbit[0] for orbit in vertex_orbits]:
                good = True
                for j in range(G.M.ncols()):
                    if R(G.M[i, j][0]) != G.M[i, j]:
                        good = False
                        break
                if good:
                    g2 = G.M[i, 0][0]
                    if 3 * (r - r0) < g2 + 1:
                        continue
                    d = G.degree(i)
                    if dim_form(g2, d, moduli_type) < r - r0:
                        continue
                    strata2 = all_strata(
                        g2, r - r0, tuple(range(1, d + 1)), moduli_type)
                    which_gen_list = [-1 for num in range(len(strata2))]
                    for num in range(len(strata2)):
                        G_copy = Graph(G.M)
                        G_copy.replace_vertex_with_graph(i, strata2[num])
                        which_gen_list[num] = num_of_stratum(
                            G_copy, g, r, markings, moduli_type)
                    rFZpl = reduced_FZ_param_list(
                        G, i, g2, d, 3 * (r - r0) - g2 - 1)
                    for FZ_param in rFZpl:
                        row_count += 1
                        yield (len(strata2), which_gen_list, FZ_param, g2, r0, d)
            if record:
                with open(filename, 'a') as file:
                    Gr = Graphtodecstratum(G)
                    file.write(f"({stratum_count}, {row_count}, '{Gr.gamma}', '{Gr.poly}')\n")


def _interior_FZ_worker(argtuple):
    FZ_param, g, r, markings, moduli_type, ngen = argtuple
    return vector(QQ, [FZ_coeff(i, FZ_param, g, r, markings, moduli_type)
                       for i in range(ngen)])


def _boundary_FZ_worker(arglist):
    (ngen, r, moduli_type), (len_strata2, which_gen_list, FZ_param, g2, r0, d) = arglist
    relation = [0] * ngen
    for num in range(len_strata2):
        if which_gen_list[num] != -1:
            relation[which_gen_list[num]] += FZ_coeff(num, FZ_param, g2, r - r0, tuple(
                range(1, d + 1)), moduli_type)
    return vector(QQ, relation, sparse=True)


def generate_boundary_FZ(g, r, markings=(), moduli_type=MODULI_ST, num_cpu=1, chunksize=100, start=1, quiet=True, record=True, maxtasks=100):
    r"""
    EXAMPLES::

        sage: from admcycles.DR.relations import boundary_FZ
        sage: boundary_FZ(2, 2)
        [(0, 0, 102, -30, 0, 0, -3, 0),
         (0, 0, 30, 42, 0, 0, -3, 0),
         (0, 0, 0, 0, 66, -60, -6, -3),
         (0, 0, 0, 0, 15, 6, -21, -3/2)]
    """
    ngen = num_strata(g, r, markings, moduli_type)
    big_FZ_param = big_boundary_FZparam(g, r, markings, moduli_type, record=record, start=start)
    for i in range(start - 1):
        next(big_FZ_param)
    count = start

    with Pool(processes=num_cpu, maxtasksperchild=int(maxtasks)) as pool:
        arggen = zip_longest((), big_FZ_param, fillvalue=(ngen, r, moduli_type))

        while True:
            arglist = tuple(islice(arggen, chunksize))
            if not arglist:
                return None

            imapresult = pool.imap(_boundary_FZ_worker, arglist)

            for result in imapresult:
                if not quiet:
                    print(count)
                yield result
                count += 1
        pool.close()
        pool.join()


def rels_matrix(g, r, n, symm, moduli_type, usespin, quiet=True, num_cpu=1):
    r"""
    Returns a matrix containing all FZ-relations for given ``g``, ``r``, ``n``, ``moduli_type``.
    The relations are invariant under the symmetry action on the first ``symm`` points.
    When ``usespin`` is True the relations are computed using Pixton's 3-spin formula.
    When ``usespin`` is False the relations are computed by deriving old relations and
    combining them with (possibly) new relations.

    TESTS::

      sage: from admcycles.DR import rels_matrix
      sage: sum(rels_matrix(2, 2, 4, 2, 1, False).echelon_form().column(-1))  # long time
      38
      sage: from admcycles.DR import rels_matrix, MODULI_RT, betti
      sage: def betti2(g, n, r):
      ....:     M = rels_matrix(g, r, n, n, MODULI_RT, False)
      ....:     return M.ncols() - M.rank()
      sage: [betti2(5, 2, i) for i in range(6)]  # long time
      [1, 3, 6, 6, 3, 1]
      sage: [betti(5, i, (1, 1), MODULI_RT) for i in range(6)]  # long time
      [1, 3, 6, 6, 3, 1]

    Check for https://gitlab.com/modulispaces/admcycles/-/issues/105::

        sage: from admcycles.DR import MODULI_ST
        sage: rels_matrix(9, 3, 0, 0, MODULI_ST, False).ncols()
        356
    """
    # m = get_memory_usage()
    if usespin:
        if symm != 0:
            print("FZ_matrix not implemented with symmetry")
            return
        rel = matrix(generate_all_FZ(g, r, get_marks(n, symm), moduli_type, quiet, num_cpu))
        # dprint("memory diff matrix computation for g = %s, n = %s, r = %s, moduli_type = %s, 3spin = %s : %s",
        #        g, r, n, moduli_type, usespin, floor(get_memory_usage() - m))
        return rel
    drels = derived_rels(g, r, n, symm, moduli_type)
    pnrels = possibly_new_FZ(g, r, n, moduli_type)
    if symm != n:
        if symm == 0:
            pnrels = [unsymmetrize_vec(p, g, r, get_marks(n, symm),
                                       moduli_type) for p in pnrels]
        else:
            pnrels = [partial_unsymmetrize_vec(p, g, r, get_marks(n, symm),
                      get_marks(n, n), moduli_type) for p in pnrels]
    allrels = drels + pnrels
    ngen = num_strata(g, r, get_marks(n, symm), moduli_type)
    rel = matrix(QQ, len(allrels), ngen, sparse=True)
    for i, r in enumerate(allrels):
        for (j, c) in r:
            rel[i, j] = c
    # dprint("memory diff relation matrix computation for g = %s, n = %s, r = %s, moduli_type = %s, 3spin = %s: %s",
    #        g, r, n, moduli_type, usespin, floor(get_memory_usage() - m))
    dprint("matrix has %s rows and %s columns", rel.nrows(), rel.ncols())
    return rel


@file_cache.file_cached_function(
    directory=os.path.join(DOT_SAGE, "admcycles/newrels"),
    env_var="ADMCYCLES_CACHE_DIR",
    key=file_cache.ignore_args_key([]),
    filename=file_cache.ignore_args_filename())
def pullback_derived_rels(g, r, n, symm, moduli_type=MODULI_ST):
    r"""
    Returns a list of relations that are derived from relations with
    less points by pulling back along the forgetfulmap that forgets a point.
    """
    if r == 0:
        return []
    dprint("Start pullback_derived (%s,%s,%s,%s): %s", g,
           r, n, moduli_type, floor(get_memory_usage()))
    answer = []
    for n0 in range(n):
        if dim_form(g, n0, moduli_type) >= r:
            basic_rels = choose_basic_rels(g, r, n0, moduli_type)
            for rel in basic_rels:
                for vec in subsequences(n, n - n0, symm):
                    local_symm = max(symm, 1) - vec.count(1)
                    if local_symm < n0:
                        rel2 = partial_unsymmetrize_vec(rel, g, r, get_marks(n0, local_symm),
                                                        get_marks(n0, n0), moduli_type)
                    else:
                        rel2 = copy(rel)
                    for i in range(n - n0):
                        rel2 = insertion_pullback(
                            rel2, vec[i], g, r, n0 + i, local_symm, moduli_type, False)
                        if vec[i] == 1:
                            local_symm += 1
                    answer.append(simplify_sparse(rel2))
        else:
            if moduli_type == MODULI_ST and not ((g == 0 and n0 < 3) or (g == 1 and n0 == 0)):
                continue
            basic_rels = choose_basic_rels(g, r, n0, MODULI_SMALL)
            k = r - dim_form(g, n0, moduli_type)
            for rel in basic_rels:
                for vec2 in subsequences(n, n - n0 - k + 1, symm):
                    local_symm2 = max(symm, 1) - vec2.count(1)
                    for vec in subsequences(n0 + k - 1, k - 1, local_symm2):
                        local_symm = max(local_symm2, 1) - vec.count(1)
                        if local_symm < n0:
                            rel2 = partial_unsymmetrize_vec(rel, g, r, get_marks(n0, local_symm),
                                                            get_marks(n0, n0), MODULI_SMALL)
                        else:
                            rel2 = copy(rel)
                        for i in range(k - 1):
                            rel2 = insertion_pullback(
                                rel2, vec[i], g, r, n0 + i, local_symm, MODULI_SMALL, False)
                            if vec[i] == 1:
                                local_symm += 1
                        local_symm = local_symm2
                        rel2 = insertion_pullback(
                            rel2, vec2[0], g, r, n0 + k - 1, local_symm, moduli_type, True)
                        if vec2[0] == 1:
                            local_symm += 1
                        for i in range(n - n0 - k):
                            rel2 = insertion_pullback(
                                rel2, vec2[i + 1], g, r, n0 + k + i, local_symm, moduli_type, False)
                            if vec2[i + 1] == 1:
                                local_symm += 1
                        answer.append(simplify_sparse(rel2))
    dprint("End pullback_derived (%s,%s,%s,%s): %s", g,
           r, n, moduli_type, floor(get_memory_usage()))
    answer = remove_duplicates(answer)
    return answer


@file_cache.file_cached_function(
    directory=os.path.join(DOT_SAGE, "admcycles/newrels"),
    env_var="ADMCYCLES_CACHE_DIR",
    key=file_cache.ignore_args_key([]),
    filename=file_cache.ignore_args_filename())
def interior_derived_rels(g, r, n, symm, moduli_type=MODULI_ST):
    r"""
    Returns a list of relations that are derived from relations with
    lower codimension by multlication with psi- and kappa-classes.
    """
    dprint("Start interior_derived (%s,%s,%s,%s): %s", g,
           r, n, moduli_type, floor(get_memory_usage()))
    answer = copy(pullback_derived_rels(g, r, n, symm, moduli_type))
    for r0 in range(r):
        local_symm = max(symm - (r - r0), 0)
        if local_symm < symm:
            symm_map = symmetrize_map(g, r, get_marks(n, local_symm), get_marks(n, symm), moduli_type)
        pullback_rels = [partial_unsymmetrize_vec(v, g, r0, get_marks(n, local_symm), get_marks(n, n), moduli_type) for v in choose_basic_rels(g, r0, n, moduli_type)]
        pullback_rels += pullback_derived_rels(g, r0, n, local_symm, moduli_type)
        for rel in pullback_rels:
            for i in range(r - r0 + 1):
                for sigma in Partitions(i):
                    for tau in IntegerVectors(r - r0 - i, n - local_symm):
                        rel2 = copy(rel)
                        rcur = r0
                        for m in range(n - local_symm):
                            for mm in range(tau[m]):
                                rel2 = psi_multiple(
                                    rel2, get_marks(n, local_symm)[-m - 1], g, rcur, n, local_symm, moduli_type)
                                rcur += 1
                        for m in sigma:
                            rel2 = kappa_multiple(
                                rel2, m, g, rcur, n, local_symm, moduli_type)
                            rcur += m
                        if local_symm < symm:
                            rel2 = [[symm_map[y[0]], y[1]] for y in rel2]
                        answer.append(simplify_sparse(rel2))
    dprint("End interior_derived (%s,%s,%s,%s): %s", g,
           r, n, moduli_type, floor(get_memory_usage()))
    answer = remove_duplicates(answer)
    return answer


@file_cache.file_cached_function(
    directory=os.path.join(DOT_SAGE, "admcycles/newrels"),
    env_var="ADMCYCLES_CACHE_DIR",
    key=file_cache.ignore_args_key([]),
    filename=file_cache.ignore_args_filename())
def derived_rels(g, r, n, symm, moduli_type=MODULI_ST):
    r"""
    Returns a list of relations that are derived from relations with
    lower genus, codimension, and/or number of points.
    This is done by taking a Graph and inserting a relation at a vertex.
    """
    dprint("Start derived (%s,%s,%s,%s): %s", g, r,
           n, moduli_type, floor(get_memory_usage()))
    if dim_form(g, n, moduli_type) < r:
        return []
    markings = get_marks(n, symm)
    answer = copy(interior_derived_rels(g, r, n, symm, moduli_type))
    if moduli_type <= MODULI_SM:
        return answer
    for r0 in range(1, r):
        strata = all_strata(g, r0, markings, moduli_type)
        for G in strata:
            vertex_orbits = graph_count_automorphisms(G, True)
            for i in [orbit[0] for orbit in vertex_orbits]:
                good = True
                for j in range(G.M.ncols()):
                    if R(G.M[i, j][0]) != G.M[i, j]:
                        good = False
                        break
                if good:
                    localsymm = 0
                    for j in range(G.M.ncols()):
                        if G.M[i, j][0] == 1 and G.M[0, j][0] == 1:
                            localsymm += 1
                    g2 = G.M[i, 0][0]
                    if 3 * (r - r0) < g2 + 1:
                        continue
                    d = G.degree(i)
                    if dim_form(g2, d, moduli_type) < r - r0:
                        continue
                    strata2 = all_strata(
                        g2, r - r0, get_marks(d, localsymm), moduli_type)
                    which_gen_list = [
                        -1 for num in range(len(strata2))]
                    for num in range(len(strata2)):
                        G_copy = Graph(G.M)
                        G_copy.replace_vertex_with_graph(i, strata2[num])
                        which_gen_list[num] = num_of_stratum(
                            G_copy, g, r, markings, moduli_type)
                    rel_list = [partial_unsymmetrize_vec(br, g2, r - r0, get_marks(d, localsymm), get_marks(d, d), moduli_type) for br in choose_basic_rels(g2, r - r0, d, moduli_type)]
                    rel_list += interior_derived_rels(g2, r - r0, d, localsymm, moduli_type)
                    for rel0 in rel_list:
                        relation = []
                        for x0, x1 in rel0:
                            if which_gen_list[x0] != -1:
                                relation.append([which_gen_list[x0], x1])
                        relation = simplify_sparse(relation)
                        answer.append(relation)
    answer = remove_duplicates(answer)
    dprint("End derived (%s,%s,%s,%s): %s", g, r, n,
           moduli_type, floor(get_memory_usage()))
    return answer


@file_cache.file_cached_function(
    directory=os.path.join(DOT_SAGE, "admcycles/newrels"),
    env_var="ADMCYCLES_CACHE_DIR",
    key=file_cache.ignore_args_key([]),
    filename=file_cache.ignore_args_filename())
def choose_basic_rels(g, r, n, moduli_type):
    r"""
    Return a basis of new relations of the tautological ring invariant under symmetry.

    EXAMPLES::

        sage: from admcycles.DR.moduli import MODULI_SM, MODULI_RT, MODULI_CT, MODULI_ST
        sage: from admcycles.DR.relations import choose_basic_rels
        sage: choose_basic_rels(2, 2, 0, MODULI_ST)
        [[[0, 115920],
          [1, -12240],
          [2, 13536],
          [3, -5040],
          [4, 1584],
          [5, -5040],
          [6, -144],
          [7, -36]]]
    """
    if 3 * r < g + n + 1:
        return []
    sym_ngen = num_strata(g, r, tuple([1 for i in range(n)]), moduli_type)
    if moduli_type == MODULI_SMALL and r > dim_form(g, n, MODULI_SM):
        sym_possible_rels = [[[i, 1]] for i in range(sym_ngen)]
    else:
        sym_possible_rels = possibly_new_FZ(g, r, n, moduli_type)
    if not sym_possible_rels:
        return []
    dprint("Start basic_rels (%s,%s,%s,%s): %s", g, r,
           n, moduli_type, floor(get_memory_usage()))
    previous_rels = derived_rels(g, r, n, n, moduli_type)
    nrels = len(previous_rels)
    dprint("%s gens, %s oldrels", sym_ngen, nrels)
    D = {}
    for i in range(nrels):
        for x in previous_rels[i]:
            D[i, x[0]] = x[1]
    if nrels > 0:
        row_order, col_order = choose_orders_sparse(D, nrels, sym_ngen)
        previous_rank = compute_rank_sparse(D, row_order, col_order)
        dprint("rank %s", previous_rank)
    else:
        previous_rank = 0
        row_order = []
        col_order = list(range(sym_ngen))
    answer = []
    for j in range(len(sym_possible_rels)):
        for x in sym_possible_rels[j]:
            D[nrels, x[0]] = x[1]
        row_order.append(nrels)
        nrels += 1
        if compute_rank_sparse(D, row_order, col_order) > previous_rank:
            answer.append(sym_possible_rels[j])
            previous_rank += 1
        dprint("rank %s", previous_rank)
    dprint("End basic_rels (%s,%s,%s,%s): %s", g, r,
           n, moduli_type, floor(get_memory_usage()))
    dprint("%s,%s,%s,%s: rank %s", g, r, n,
           moduli_type, sym_ngen - previous_rank)
    # if moduli_type > -1:
    #     dsave("sparse-%s,%s,%s,%s|%s,%s,%s", g, r, n, moduli_type,
    #           len(answer), sym_ngen - previous_rank, floor(get_memory_usage()))
    # if moduli_type >= 0 and sym_ngen-previous_rank != betti(g,r,tuple([1 for i in range(n)]),moduli_type):
    #  dprint("ERROR: %s,%s,%s,%s",g,r,n,moduli_type)
    #  return
    return answer


# TODO: use matrix(D, sparse=True).rank()
# be careful that building the matrix is what costs most of the time!
def compute_rank_sparse(D, row_order, col_order):
    r"""
    Return the rank of the sparse matrix ``D`` given as a dictionary.

    EXAMPLES::

        sage: from admcycles.DR.relations import compute_rank_sparse
        sage: compute_rank_sparse({(0, 1): 1, (1, 0): 2}, [0 ,1], [0, 1])
        2
    """
    count = 0
    nrows = len(row_order)
    ncols = len(col_order)
    row_order_rank = [-1 for i in range(nrows)]
    col_order_rank = [-1 for i in range(ncols)]
    for i in range(nrows):
        row_order_rank[row_order[i]] = i
    for i in range(ncols):
        col_order_rank[col_order[i]] = i

    row_contents = [set() for i in range(nrows)]
    col_contents = [set() for i in range(ncols)]
    for x in D:
        row_contents[x[0]].add(x[1])
        col_contents[x[1]].add(x[0])

    for i in row_order:
        S = []
        for j in row_contents[i]:
            S.append(j)
        if not S:
            continue
        count += 1
        S.sort(key=lambda x: col_order_rank[x])
        j = S[0]
        T = []
        for ii in col_contents[j]:
            if row_order_rank[ii] > row_order_rank[i]:
                T.append(ii)
        for k in S[1:]:
            rat = D[i, k] / QQ(D[i, j])
            for ii in T:
                if (ii, k) not in D:
                    D[ii, k] = 0
                    row_contents[ii].add(k)
                    col_contents[k].add(ii)
                D[ii, k] -= rat * D[ii, j]
                if D[ii, k] == 0:
                    D.pop((ii, k))
                    row_contents[ii].remove(k)
                    col_contents[k].remove(ii)
        for ii in T:
            D.pop((ii, j))
            row_contents[ii].remove(j)
            col_contents[j].remove(ii)
    return count


def num_new_rels(g, r, n=0, moduli_type=MODULI_ST):
    return len(choose_basic_rels(g, r, n, moduli_type))


def goren_rels(g, r, markings=(), moduli_type=MODULI_ST):
    r"""
    Return the kernel of the pairing in degree ``r``.

    EXAMPLES::

        sage: from admcycles.DR.relations import goren_rels
        sage: goren_rels(3, 2)  # long time
        [
        (1, 0, 0, -41/21, 4/35, 0, 0, 0, -5/42, 41/504, 1/105, -11/140, 1/5040),
        (0, 1, 0, -89/7, -11/35, 0, 0, 0, -5/7, 103/168, -1/7, -47/70, -1/140),
        (0, 0, 1, -1, -7/5, 0, 0, 0, 0, 0, -1/10, 0, 0),
        (0, 0, 0, 0, 0, 1, 0, 0, 0, -1/24, 0, 0, 0),
        (0, 0, 0, 0, 0, 0, 1, 0, 0, -1/24, 0, 0, 0),
        (0, 0, 0, 0, 0, 0, 0, 1, -2, 1, -7/5, -7/5, -1/10)
        ]
    """
    gorenstein_precompute(g, r, markings, moduli_type)
    r3 = dim_form(g, len(markings), moduli_type)
    r2 = r3 - r
    S1 = tuple(range(num_strata(g, r, markings, moduli_type)))
    S2 = tuple(good_generator_list(g, r2, markings, moduli_type))
    M = pairing_submatrix(S1, S2, g, r, markings, moduli_type)
    return matrix(M).kernel().basis()


@cached_function
def good_generator_list(g, r, markings=(), moduli_type=MODULI_ST):
    r"""
    Return a subset of indices whose corresponding strata generate
    the ``r``-th degree part of the tautological ring.

    EXAMPLES::

        sage: from admcycles.DR.moduli import MODULI_SM, MODULI_RT, MODULI_CT, MODULI_ST
        sage: from admcycles.DR.relations import good_generator_list
        sage: good_generator_list(3, 1, (), MODULI_ST)
        [0, 1, 2]
        sage: good_generator_list(3, 2, (), MODULI_ST)
        [1, 3, 4, 8, 9, 10, 11, 12]
        sage: good_generator_list(3, 3, (), MODULI_ST)
        [9, 22, 30, 31, 32, 35, 36, 37, 38, 39]
        sage: good_generator_list(3, 4, (), MODULI_ST)
        [86, 87, 109, 110, 111, 112, 113, 114, 117, 118, 119, 120]
        sage: good_generator_list(3, 5, (), MODULI_ST)
        [237, 238, 239, 257, 258, 259, 260, 261]
        sage: good_generator_list(3, 6, (), MODULI_ST)
        [373, 374, 375, 376, 377]
    """
    gens = all_strata(g, r, markings, moduli_type)
    good_gens = []
    ngens = len(gens)
    for num in range(ngens):
        G = gens[num]
        good = True
        for i in range(1, G.M.nrows()):
            g = G.M[i, 0][0]
            codim = 0
            for d in range(1, r + 1):
                if G.M[i, 0][d] != 0 and 3 * d > g:
                    good = False
                    break
                codim += d * G.M[i, 0][d]
            if not good:
                break
            for j in range(1, G.M.ncols()):
                codim += G.M[i, j][1]
                codim += G.M[i, j][2]
            if codim > 0 and codim >= g:
                good = False
                break
        if good:
            good_gens.append(num)
    return good_gens


def choose_orders_sparse(D, nrows, ncols):
    row_nums = [0 for i in range(nrows)]
    col_nums = [0 for j in range(ncols)]
    for key in D:
        row_nums[key[0]] += 1
        col_nums[key[1]] += 1
    row_order = list(range(nrows))
    col_order = list(range(ncols))
    row_order.sort(key=lambda x: row_nums[x])
    col_order.sort(key=lambda x: col_nums[x])
    return row_order, col_order


def choose_orders(L):
    rows = len(L)
    if rows == 0:
        return [], []
    cols = len(L[0])
    row_nums = [0 for i in range(rows)]
    col_nums = [0 for j in range(cols)]
    for i in range(rows):
        for j in range(cols):
            if L[i][j] != 0:
                row_nums[i] += 1
                col_nums[j] += 1
    row_order = list(range(rows))
    col_order = list(range(cols))
    row_order.sort(key=lambda x: row_nums[x])
    col_order.sort(key=lambda x: col_nums[x])
    return row_order, col_order


# TODO: use matrix(L).rank()
# be careful that building the matrix is what costs most of the time!
def compute_rank(L):
    r"""
    Return the rank of the matrix ``L`` given as a list of lists.

    EXAMPLES::

        sage: from admcycles.DR.relations import compute_rank
        sage: compute_rank([[1, 2], [3, 4]])
        2
        sage: compute_rank([[1, 2], [2, 4]])
        1
        sage: compute_rank([[0, 0], [0, 0]])
        0
    """
    count = 0
    for i in range(len(L)):
        S = [j for j in range(len(L[0])) if L[i][j] != 0]
        if not S:
            continue
        count += 1
        j = S[0]
        T = [ii for ii in range(i + 1, len(L))
             if L[ii][j] != 0]
        for k in S[1:]:
            rat = L[i][k] / L[i][j]
            for ii in T:
                L[ii][k] -= rat * L[ii][j]
        for ii in range(i + 1, len(L)):
            L[ii][j] = 0
    return count


def compute_rank2(L, row_order, col_order):
    count = 0
    for irow in range(len(row_order)):
        i = row_order[irow]
        S = [j for j in col_order if L[i][j] != 0]
        if not S:
            continue
        count += 1
        j = S[0]
        T = [ii for ii in row_order[irow + 1:]
             if L[ii][j] != 0]
        for k in S[1:]:
            rat = L[i][k] / L[i][j]
            for ii in T:
                L[ii][k] -= rat * L[ii][j]
        for ii in T:
            L[ii][j] = 0
    return count
