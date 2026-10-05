from .stable_graph import StableGraph
from sage.modules.free_module_element import vector
from .symmetry import general_generating_indices, tautgens_sym
from .list_strata import list_strata_can, get_strata_list_inds
from .antisymmetry import antisym_gens, generating_indices_as, prod_basis_iter, get_graph_data, as_basis_rank, prod_to_as_basis, vertex_data_iter, dec_to_basis_as, genstobasis_as, as_basis_iter, use_as_gens, symmetrize_as_basis_Sn_action, symmetrize_graph, dec_to_as
from sage.matrix.constructor import matrix
from sage.matrix.special import block_matrix
from sage.rings.all import QQ
from itertools import combinations
import itertools
from .admcycles import Pixtongraph
from sage.groups.perm_gps.permgroup_named import SymmetricGroup
from .moduli import get_moduli
from . import DR
from collections import defaultdict
from .utils import get_marks_part
from .pushforward_spectral_sequence import get_vertex_symmetric_action
from . import file_cache
import os
from sage.env import DOT_SAGE


def pullback_E2_rank(g, n, p, q, n_part, moduli_type='sm'):
    r"""
    Compute the rank of E_2^{p, q} for
    Deligne's pullback spectral sequence
    w.l.o.g. we take q in complex dimension because the answer
    is 0 when it would be odd (in real dimension).
    """
    total_dim = 3 * g - 3 + n
    r = total_dim - q
    if p + r > total_dim:
        raise ValueError('answer is trivial here')
    if p == 0:
        return GK_kernel_rank(g, n, p, r, n_part, moduli_type)
    return GK_kernel_rank(g, n, p, r, n_part, moduli_type) - GK_image_rank(g, n, p - 1, r, n_part, moduli_type)


@file_cache.file_cached_function(
    directory=os.path.join(DOT_SAGE, "admcycles/cohomology/GK/loop"),
    key=file_cache.ignore_args_key([]),
    filename=file_cache.ignore_args_filename())
def diff_loop_single_vertex(g, n, r, n_part, self_edges):
    r"""
    For a graph with a single vertex, compute the
    image when adding a loop.
    """
    assert (g > 0 and 3 * g - 3 + n > r)
    # unlike in many other parts of the code, here there
    # is a real difference between self_edges=0 and self_edges=1

    # by relabeling I am introducing a potential -1 factor, but it is uniform for this particular map
    if n_part:
        assert (max(n_part) <= 2)
    threshold = self_edges * 2
    relabel_dict = {n + 1: threshold + 1, n + 2: threshold + 2}
    for i in range(1, n + 1):
        relabel_dict[i] = i + 2 * (i > threshold)

    g2 = g - 1

    irr = StableGraph([g2], [list(range(1, n + 3))], [(n + 1, n + 2)])

    result = []
    source_as_gens = use_as_gens(g, n, r, n_part, self_edges)
    if source_as_gens:
        gen_ind = generating_indices_as(g, n, r, n_part, self_edges)
        as_gens = antisym_gens(g, n, r, n_part, self_edges)
    else:
        gen_ind = general_generating_indices(g, n, r, n_part)
    for ind in gen_ind:
        if source_as_gens:
            as_ind, c = as_gens[ind][0]
            decst = tautgens_sym(g, n, r, n_part)[as_ind]
        else:
            decst = tautgens_sym(g, n, r, n_part)[ind]
        image = []
        for (dec0,) in irr.boundary_pullback(decst).dimension_filter().terms:
            dec = dec0.relabel(relabel_dict)
            image.append(dec)
        result.append(image)
    return result


@file_cache.file_cached_function(
    directory=os.path.join(DOT_SAGE, "admcycles/cohomology/GK/loop"),
    key=file_cache.ignore_args_key([]),
    filename=file_cache.ignore_args_filename())
def diff_loop_single_vertex_relabel(g, n, r, n_part, self_edges, relabel_tuple):
    r"""
    Takes the output of ``diff_loop_single_vertex`` and applies the relabeling
    given by ``relabel_tuple``.
    The resulting classes are then expressed in terms of a basis for
    (S_{g,n}^r/P_{g,n}^r)^((S_2 \wraith S_{``self_edges``}) \otimes (S_{``n_part``}/S_2^{``self_edges``}))
    """
    n_part2 = tuple(sorted(n_part + (2,), reverse=True))
    g2 = g - 1
    n2 = n + 2
    se2 = self_edges + 1

    relabel_dict = {i: j for i, j in relabel_tuple}
    result = []
    for decs in diff_loop_single_vertex(g, n, r, n_part, self_edges):
        vecs = []
        for dec in decs:
            coeff = dec.poly.coeff[0]
            if relabel_dict:
                rdec = dec.relabel(relabel_dict)
            else:
                rdec = dec
            vec = dec_to_basis_as(rdec, g2, n2, r, n_part2, se2, sparse_list=False)
            if vec:
                vecs.append(coeff * vec)
        if vecs:
            result.append(tuple((i, c) for i, c in enumerate(sum(vecs)) if c != 0))
        else:
            result.append(())
    return result


def split_iter(g, n, se):
    r"""
    Iterates over the ways a vertex can split.
    """
    for g1 in range(0, QQ((g, 2)).floor() + 1):
        g2 = g - g1
        min_n1 = (g1 == 0) * 2
        if g1 == g2:
            max_n1 = QQ((n, 2)).floor()
        else:
            max_n1 = n - (g2 == 0) * 2
        for n1 in range(min_n1, max_n1 + 1):
            if g1 == g2 and n == 2 * n1 and n1 != 0:
                for part_S1 in combinations(range(1, n), n1 - 1):
                    S1 = part_S1 + (n,)
                    S2 = tuple(i for i in range(1, n) if i not in S1)
                    yield g1, g2, S1, S2
            else:
                for S1 in combinations(range(1, n + 1), n1):
                    S2 = tuple(i for i in range(1, n + 1) if i not in S1)
                    yield g1, g2, S1, S2
    return


def labeling_split(n_part, S):
    markings = get_marks_part(sum(n_part), n_part)
    new_markings = [markings[i - 1] for i in S]

    part_dict = defaultdict(list)
    for m in range(1, len(n_part) + 1):
        cc = [i + 1 for i, m2 in enumerate(new_markings) if m == m2]
        if cc:
            part_dict[len(cc)].append(cc)
    p_list = list(part_dict.items())
    p_list.sort(reverse=True)
    new_part = []
    new_markings2 = []
    for p, L in p_list:
        for x in L:
            new_markings2 += x
            new_part.append(p)
    relabel_dict = {m: i + 1 for i, m in enumerate(new_markings2) if m != i + 1}

    return tuple(new_part) + (1,), relabel_dict


def self_edges_split(S1, S2, n_part, self_edges):
    r"""
    Given a splitting, returns the splitting of self edges.
    """
    # unlike in many other parts of the code, here there
    # is a real difference between self_edges=0 and self_edges=1
    threshold = sum(i for i in n_part if i > 2)
    se1 = 0
    se2 = 0
    for i in range(self_edges):
        e1 = threshold + 1 + 2 * i
        e2 = e1 + 1
        if e1 in S1 and e2 in S1:
            se1 += 1
        elif e1 in S2 and e2 in S2:
            se2 += 1
    return se1, se2


@file_cache.file_cached_function(
    directory=os.path.join(DOT_SAGE, "admcycles/cohomology/GK/split"),
    key=file_cache.ignore_args_key([]),
    filename=file_cache.ignore_args_filename())
def diff_split_single_vertex(g, n, r, n_part, self_edges, g1, S1):
    r"""
    For a graph with a single vertex, compute the image when splitting
    the vertex in such a way that one of the new vertices has
    genus ``g1`` and the subset of marked points given by ``S1``.

    Consider the graph obtained by adding an edge at a vertex v,
    restricted to the inverse image of v under the gluing map.
    We need to divide by the size of the automorphism group.
    The automorphism group is nontrivial when we add
    a loop or when a vertex without half edges gets split
    into two parts of equal genus. Both cases come with an
    authomorphism group of order 2.
    After rescaling by 2, it is equivalent to instead multiply by
    2 when we have a split vertex that does not split symmetrically.
    We do that in this function.

    Note that this correction is not apparent from our paper.
    It comes from the difference in convention for the
    definition of a decorated stratum class. In the paper
    there is a division by the size of the automorphism group.
    The convention in admcycles is to not divide by
    the size of the automorphism group.
    """
    if n_part:
        # for the purpose of the current split_iter implementation
        assert (max(n_part) <= 2 and n_part.count(2) == self_edges)
    vertex_data = (g, n, r, n_part, self_edges)

    g2 = g - g1
    S2 = tuple(i for i in range(1, n + 1) if i not in S1)

    graph = StableGraph([g1, g2], [list(S1) + [n + 1], list(S2) + [n + 2]], [(n + 1, n + 2)])
    n_part1, relabel_dict1 = labeling_split(n_part, S1)
    n_part2, relabel_dict2 = labeling_split(n_part, S2)
    se1, se2 = self_edges_split(S1, S2, n_part, self_edges)

    # this does not affect the computation of weight graded pieces
    # but it is required for the square map to be zero
    if n == 0 and 2 * g1 == g:
        initial_coeff = 1
    else:
        initial_coeff = 2

    source_as_gens = use_as_gens(g, n, r, n_part, self_edges)

    result = [[] for _ in range(r + 1)]
    for (basis_num,) in prod_basis_iter((vertex_data,)):
        image = [[] for _ in range(r + 1)]
        if source_as_gens:
            dec_n, c = antisym_gens(*vertex_data)[generating_indices_as(*vertex_data)[basis_num]][0]
            assert (c > 0)
        else:
            dec_n = general_generating_indices(*vertex_data[:-1])[basis_num]
        dec = tautgens_sym(g, n, r, n_part)[dec_n]
        for new_decs in graph.boundary_pullback(dec).dimension_filter().terms:
            dec1 = new_decs[0]
            dec2 = new_decs[1]
            if relabel_dict1:
                dec1 = dec1.relabel(relabel_dict1)
            if relabel_dict2:
                dec2 = dec2.relabel(relabel_dict2)
            coeff = initial_coeff * dec1.poly.coeff[0] * dec2.poly.coeff[0]
            r1 = dec1.poly.deg(0) + dec1.gamma.num_edges()
            image[r1].append((dec1, dec2, coeff))
        for i in range(r + 1):
            result[i].append(tuple(image[i]))
    return result


@file_cache.file_cached_function(
    directory=os.path.join(DOT_SAGE, "admcycles/cohomology/GK/split"),
    key=file_cache.ignore_args_key([]),
    filename=file_cache.ignore_args_filename())
def diff_split_single_vertex_relabel(g, n, r, n_part, self_edges, g1, S1, r1, relabel_tuple1, relabel_tuple2):
    r"""
    Takes the output of ``diff_split_single_vertex`` restricted to multidegree (r1, r - r1)
    and applies the relabeling given by ``relabel_tuple1`` and ``relabel_tuple2``.
    The resulting classes are then expressed in terms of a basis for
    (S_{g,n}^r/P_{g,n}^r)^((S_2 \wraith S_{``self_edges``}) \otimes (S_{``n_part``}/S_2^{``self_edges``}))
    """
    g2 = g - g1
    S2 = tuple(i for i in range(1, n + 1) if i not in S1)
    n_part1, relabel_dict1 = labeling_split(n_part, S1)
    n_part2, relabel_dict2 = labeling_split(n_part, S2)
    se1, se2 = self_edges_split(S1, S2, n_part, self_edges)
    r2 = r - r1

    n1 = len(S1) + 1
    n2 = len(S2) + 1

    relabel_dict1 = {i: j for i, j in relabel_tuple1}
    relabel_dict2 = {i: j for i, j in relabel_tuple2}
    result = []
    for stuff in diff_split_single_vertex(g, n, r, n_part, self_edges, g1, S1)[r1]:
        image = defaultdict(int)
        for (dec1, dec2, coeff) in stuff:
            if relabel_dict1:
                dec1 = dec1.relabel(relabel_dict1)
            if relabel_dict2:
                dec2 = dec2.relabel(relabel_dict2)
            sparse_vec1 = dec_to_basis_as(dec1, g1, n1, r1, n_part1, se1)
            sparse_vec2 = dec_to_basis_as(dec2, g2, n2, r2, n_part2, se2)
            for (s1, c1), (s2, c2) in itertools.product(sparse_vec1, sparse_vec2):
                image[(s1, s2)] += c1 * c2 * coeff
        result.append(image)
    return result


@file_cache.file_cached_function(
    directory=os.path.join(DOT_SAGE, "admcycles/cohomology/GK/basis_relabel"),
    key=file_cache.ignore_args_key([]),
    filename=file_cache.ignore_args_filename())
def relabel_basis_dict(g, n, r, n_part, se, relabel_dict_tuple):
    r"""
    Stores the relabeling action on the basis of
    (S_{g,n}^r/P_{g,n}^r)^((S_2 \wraith S_{``self_edges``}) \otimes (S_{``n_part``}/S_2^{``self_edges``}))
    """
    rbd = []
    relabel_dict = {i: j for i, j in relabel_dict_tuple}
    if not use_as_gens(g, n, r, n_part, se):
        for num in general_generating_indices(g, n, r, n_part):
            dec = tautgens_sym(g, n, r, n_part)[num]
            rbd.append(dec_to_basis_as(dec.relabel(relabel_dict), g, n, r, n_part, se))
        return rbd

    markings = get_marks_part(n, n_part)
    moduli_st = get_moduli('st', DRpy=True)
    dta = dec_to_as(g, n, r, n_part, se)

    for num in generating_indices_as(g, n, r, n_part, se):
        vec_list = []
        for num2, c in antisym_gens(g, n, r, n_part, se)[num]:
            dec = tautgens_sym(g, n, r, n_part)[num2]
            dec = dec.relabel(relabel_dict)
            dec_num = DR.num_of_stratum(Pixtongraph(dec.gamma, dec.poly[0][0], dec.poly[0][1], n_part=n_part), g, r, markings, moduli_type=moduli_st)
            dtad = dta[dec_num]
            if dtad is None:
                continue
            as_num, c2 = dtad
            vec_list.append((c * c2) * genstobasis_as(g, n, r, n_part, se, sparse_list=False)[as_num])
        rbd.append([ic for ic in enumerate(sum(vec_list)) if ic[1] != 0])
    return rbd


def vertex_symmetric_action(gamma):
    r"""
    Returns combinatorial data describing the ordering of the marked
    points at each vertex of a graph.
    """
    nv_parts = []
    local_gs = []
    for v, vlegs in enumerate(gamma.legs()):
        sev = gamma.edges_between(v, v)
        nv = len(vlegs)
        non_se = nv - 2 * len(sev)
        nv_parts.append(tuple([2] * len(sev) + [1] * non_se))
        p = []
        for e in sev:
            for e_i in e:
                p.append(vlegs.index(e_i) + 1)
        for l in range(1, nv + 1):
            if l not in p:
                p.append(l)
        local_gs.append(SymmetricGroup(nv)(p).inverse())
    return nv_parts, local_gs


def get_diff_split_targets(g, n, gamma_r, ind, r, scheduling=False):
    r"""
    Returns a list of indices for graphs that are obtained
    by splitting a vertex of the graph of index ``ind``.

    When ``scheduling`` is set to True, return extra data that is used when
    setting up multiprocessing in order to determine task dependencies.
    """
    gamma = list(list_strata_can(g, n, gamma_r))[ind]
    num_vert = gamma.num_verts()
    nv_parts, _, _, pre_local_gs, _ = get_vertex_symmetric_action(g, n, gamma_r, ind, n_part=[1] * n)
    result = []
    if scheduling:
        loop_result = []
    for v in range(num_vert):
        reordered_markings = pre_local_gs[v].inverse()(gamma.legs(v))
        reorder_dict = {b: a for a, b in zip(gamma.legs(v), reordered_markings) if not a == b}
        reorder_dict_inv = {a: b for a, b in zip(gamma.legs(v), reordered_markings) if not a == b}
        for g1, g2, S1, S2 in split_iter(gamma.genera(v), gamma.num_legs(v), len(gamma.edges_between(v, v))):
            new_gamma = gamma.copy(mutable=True)
            if reorder_dict:
                new_gamma = new_gamma.relabel({}, reorder_dict).copy(mutable=True)
            new_gamma.degenerate_sep(v, g1, tuple(gamma.legs(v)[i - 1] for i in S1))
            if reorder_dict:
                new_gamma = new_gamma.relabel({}, reorder_dict_inv).copy(mutable=True)
            _, local_gs = vertex_symmetric_action(new_gamma)
            if scheduling:
                relabel_dict, _, _, target_data = graph_canonicalization_with_data(new_gamma, local_gs)
                for _, vd in vertex_data_iter(gamma, r, nv_parts):
                    vertex_data = vd
                    g0, n0, r0, _, _ = vertex_data[v]
                    if 3 * g0 - 3 + n0 == r0:
                        continue
                    sv_relabel_params_without_r1 = ((*vertex_data[v], g1, S1), (tuple(relabel_dict[v].items()), tuple(relabel_dict[-1].items())))
                    basis_ind_dict_params = []
                    for i in range(num_vert):
                        if i == v or not relabel_dict[i]:
                            continue
                        basis_ind_dict_params.append((*vertex_data[i], tuple(relabel_dict[i].items())))
                    result.append((target_data[3], sv_relabel_params_without_r1, basis_ind_dict_params))
            else:
                target_ind = graph_canonicalization_with_data(new_gamma, local_gs)[3][3]
                result.append(target_ind)
        if scheduling:
            if gamma.genera(v) == 0:
                continue
            new_gamma = gamma.copy(mutable=True)
            new_gamma.degenerate_nonsep(v)
            _, local_gs = vertex_symmetric_action(new_gamma)
            relabel_dict = graph_canonicalization_with_data(new_gamma, local_gs)[0]
            for _, vd in vertex_data_iter(gamma, r, nv_parts):
                vertex_data = vd
                g0, n0, r0, n_part0, se0 = vertex_data[v]
                if g0 == 0 or 3 * g0 - 3 + n0 == r0:
                    continue
                sv_relabel_params = (*vertex_data[v], tuple(relabel_dict[v].items()))
                basis_ind_dict_params = []
                for i, rd in enumerate(relabel_dict):
                    if i == v or not rd:
                        continue
                    basis_ind_dict_params.append((*vertex_data[i], tuple(relabel_dict[i].items())))
                loop_result.append((sv_relabel_params, basis_ind_dict_params))

    if scheduling:
        return result, loop_result
    return set(result)


@file_cache.file_cached_function(
    directory=os.path.join(DOT_SAGE, "admcycles/cohomology/GK/diff_combined"),
    key=file_cache.ignore_args_key([]),
    filename=file_cache.ignore_args_filename())
def GK_image_single_gamma(g, n, gamma_r, ind, r, moduli_type='sm'):
    r"""
    Computes the image of the differential restricted to a single graph.
    """
    dlpb = diff_loop_product_basis(g, n, gamma_r, ind, r)
    split_target_inds = get_diff_split_targets(g, n, gamma_r, ind, r)
    if moduli_type != 'sm':
        split_target_inds = [x for x in split_target_inds if x in get_strata_list_inds(g, n, gamma_r + 1, moduli_type)]
    dssts = [(target, diff_split_single_target(g, n, gamma_r, ind, r, target)) for target in split_target_inds]

    total_image = []
    for basis_elem in as_basis_iter(g, n, gamma_r, ind, r):
        image = {}
        for r_split, S, basis_coeff in basis_elem:
            for target_ind, vec in dlpb[(r_split, S)].items():
                try:
                    image[target_ind] += basis_coeff * vec
                except KeyError:
                    image[target_ind] = basis_coeff * vec
            for target_ind, dsst in dssts:
                try:
                    vv = dsst[(r_split, S)]
                except KeyError:
                    # this should correspond to the case where it is zero
                    continue
                try:
                    image[target_ind] += basis_coeff * vv
                except KeyError:
                    image[target_ind] = basis_coeff * vv
        total_image.append(image)

    indices = {}
    current = 0
    for i in get_strata_list_inds(g, n, gamma_r + 1, moduli_type):
        indices[i] = current
        current += as_basis_rank(g, n, gamma_r + 1, i, r)
    ncols = current
    rows = []
    for image_dict in total_image:
        row = vector(QQ, ncols)
        for i, vec in image_dict.items():
            indi = indices[i]
            for j, c in enumerate(vec):
                row[indi + j] += c
        rows.append(row)
    M = matrix(rows)
    del (rows)
    M.echelonize()
    M = M.matrix_from_rows(range(M.rank()))
    if not M:
        return matrix(QQ, 0, ncols)
    return M


@file_cache.file_cached_function(
    directory=os.path.join(DOT_SAGE, "admcycles/cohomology/GK/split"),
    key=file_cache.ignore_args_key([]),
    filename=file_cache.ignore_args_filename())
def diff_split_single_target(g, n, gamma_r, ind, r, target_ind):
    r"""
    Computes the contribution of the differential on the E_1 page.
    The domain is the product basis on H^r(M_\Gamma).
    We restrict the image to a specific graph \Gamma'.
    We require that \Gamma' can be obtained by splitting a vertex of \Gamma.
    """
    gamma = list_strata_can(g, n, gamma_r)[ind]
    num_vert = gamma.num_verts()
    nv_parts, _, _, pre_local_gs, _ = get_vertex_symmetric_action(g, n, gamma_r, ind, n_part=[1] * n)

    target_gamma = list_strata_can(g, n, gamma_r + 1)[target_ind]
    nontrivial_aut_target = len(target_gamma.leg_automorphism_group()) != 1
    if nontrivial_aut_target:
        basismap = prod_to_as_basis(g, n, gamma_r + 1, target_ind, r)

    result = {}
    for v in range(num_vert):
        reordered_markings = pre_local_gs[v].inverse()(gamma.legs(v))
        reorder_dict = {b: a for a, b in zip(gamma.legs(v), reordered_markings) if not a == b}
        reorder_dict_inv = {a: b for a, b in zip(gamma.legs(v), reordered_markings) if not a == b}
        for g1, g2, S1, S2 in split_iter(gamma.genera(v), gamma.num_legs(v), len(gamma.edges_between(v, v))):
            new_gamma = gamma.copy(mutable=True)
            if reorder_dict:
                new_gamma = new_gamma.relabel({}, reorder_dict).copy(mutable=True)
            new_gamma.degenerate_sep(v, g1, tuple(gamma.legs(v)[i - 1] for i in S1))
            if reorder_dict:
                new_gamma = new_gamma.relabel({}, reorder_dict_inv).copy(mutable=True)
            _, local_gs = vertex_symmetric_action(new_gamma)
            relabel_dict, dicv_inv, c0, graph_data = graph_canonicalization_with_data(new_gamma, local_gs)
            if graph_data[3] != target_ind:
                continue

            for r_split, vertex_data in vertex_data_iter(gamma, r, nv_parts):
                g0, n0, r0, _, _ = vertex_data[v]
                if 3 * g0 - 3 + n0 == r0:
                    continue
                other_v_data = [vd for i, vd in enumerate(vertex_data) if i != v]
                relabel_basis_dict_dict = {i: relabel_basis_dict(*vertex_data[i], tuple(relabel_dict[i].items())) for i in range(num_vert) if i != v and relabel_dict[i]}
                for r1 in range(r_split[v] + 1):
                    r2 = r_split[v] - r1
                    pre_can_target_r_split = []
                    for v2 in range(num_vert):
                        if v2 == v:
                            pre_can_target_r_split.append(r1)
                        else:
                            pre_can_target_r_split.append(r_split[v2])
                    pre_can_target_r_split.append(r2)
                    target_r_split = tuple(pre_can_target_r_split[dicv_inv[v3]] for v3 in range(num_vert + 1))

                    for basis_ind, dsreldict in enumerate(diff_split_single_vertex_relabel(*vertex_data[v], g1, S1, r1, tuple(relabel_dict[v].items()), tuple(relabel_dict[-1].items()))):
                        for (s1, s2), kk in dsreldict.items():
                            for S in prod_basis_iter(other_v_data):
                                pre_S = []
                                LL = []
                                for v2 in range(num_vert):
                                    if v2 == v:
                                        pre_S.append(basis_ind)
                                        LL.append([(s1, 1)])
                                    else:
                                        v3 = v2 - (v2 > v)
                                        pre_S.append(S[v3])
                                        if relabel_dict[v2]:
                                            LL.append(relabel_basis_dict_dict[v2][S[v3]])
                                        else:
                                            LL.append([(S[v3], 1)])
                                pre_S = tuple(pre_S)
                                LL.append([(s2, 1)])
                                for BB in itertools.product(*LL):
                                    coeff = c0 * kk
                                    pre_can_target_S = []
                                    for s, c in BB:
                                        coeff *= c
                                        pre_can_target_S.append(s)
                                    target_S = tuple(pre_can_target_S[dicv_inv[v3]] for v3 in range(num_vert + 1))
                                    if nontrivial_aut_target:
                                        target_in_basisvec = coeff * basismap[(target_r_split, target_S)]
                                    else:
                                        target_in_basisvec = vector([coeff if key[0][:2] == (target_r_split, target_S) else 0 for key in as_basis_iter(*graph_data, r)])
                                    try:
                                        result[(r_split, pre_S)] += target_in_basisvec
                                    except KeyError:
                                        result[(r_split, pre_S)] = target_in_basisvec
    return result


def graph_canonicalization_with_data(gamma, pre_local_gs, graph_has_relabeling=False):
    r"""
    Puts a graph into canonical form and computes the induced reordering
    of vertices and half-edges.
    """
    temp_gamma = gamma.copy()
    num_vert = gamma.num_verts()
    dicv, dicl = gamma.set_canonical_label(certificate=True, sortlegs=True)
    dicv_inv = {j: i for i, j in dicv.items()}
    legdics = []
    for v2 in range(num_vert):
        legd = {}
        for i, l in enumerate(temp_gamma.legs(v2)):
            try:
                l2 = dicl[l]
            except KeyError:
                l2 = l
            new_i = gamma.legs(dicv[v2]).index(l2)
            legd[i + 1] = new_i + 1
        legdics.append(legd)
    p = []
    for e0, e1 in temp_gamma._edges:
        f0 = dicl[e0]
        for i, f in enumerate(gamma._edges):
            if f0 in f:
                p.append(i)
                break
    A = SymmetricGroup(list(range(len(gamma._edges))))
    c0 = A(p).sign()

    graph_data = get_graph_data(gamma)

    _, _, _, local_gs, _ = get_vertex_symmetric_action(*graph_data, n_part=[1] * graph_data[1])
    new_legdics = []
    for v in range(num_vert):
        nv = gamma.num_legs(dicv[v])
        if graph_has_relabeling:
            pgv = pre_local_gs[v]
            gv = local_gs[dicv[v]].inverse()
        else:
            pgv = pre_local_gs[v].inverse()
            gv = local_gs[dicv[v]]
        legd = {}
        for l in range(1, nv + 1):
            new_l = pgv(l)
            if new_l in legdics[v]:
                new_l = legdics[v][new_l]
            new_l = gv(new_l)
            if new_l != l:
                legd[l] = new_l

        mybool = True
        while mybool:
            mybool = False
            for i, j in legd.items():
                if i == j:
                    continue
                ni = gv.inverse()(i)
                nj = gv.inverse()(j)
                li = gamma.legs(dicv[v])[ni - 1]
                lj = gamma.legs(dicv[v])[nj - 1]
                if (li, lj) in gamma._edges or (lj, li) in gamma._edges:
                    for k, l in legd.items():
                        if l == i:
                            break
                    legd[k] = j
                    legd[i] = i
                    mybool = True
                    break
        new_legdics.append({i: j for i, j in legd.items() if i != j})
    for ld in new_legdics:
        for i in ld.values():
            assert (i in ld)
    legdics = new_legdics

    return legdics, dicv_inv, c0, graph_data


@file_cache.file_cached_function(
    directory=os.path.join(DOT_SAGE, "admcycles/cohomology/GK/loop"),
    key=file_cache.ignore_args_key([]),
    filename=file_cache.ignore_args_filename())
def diff_loop_product_basis(g, n, gamma_r, ind, r):
    r"""
    Computes the image for adding a loop to a specific graph.
    The domain is the product basis on H^r(M_\Gamma).
    But the result is expressed in terms of the basis on
    (H^r(M_\Gamma)\otimes Det(E_\Gamma))^Aut(\Gamma).
    """
    gamma = list(list_strata_can(g, n, gamma_r))[ind]
    num_vert = gamma.num_verts()
    nv_parts, _, _, _, _ = get_vertex_symmetric_action(g, n, gamma_r, ind, n_part=[1] * n)

    result = defaultdict(dict)
    for r_split, vertex_data in vertex_data_iter(gamma, r, nv_parts):
        for v in range(num_vert):
            g0, n0, r0, n_part0, se0 = vertex_data[v]
            if g0 == 0 or 3 * g0 - 3 + n0 == r0:
                continue

            new_gamma = gamma.copy(mutable=True)
            new_gamma.degenerate_nonsep(v)
            _, local_gs = vertex_symmetric_action(new_gamma)
            relabel_dict, dicv_inv, c0, graph_data = graph_canonicalization_with_data(new_gamma, local_gs)
            target_r_split = tuple(r_split[dicv_inv[v3]] for v3 in range(num_vert))
            target_ind = graph_data[3]
            nontrivial_aut_target = len(new_gamma.leg_automorphism_group()) != 1

            dlsvr = diff_loop_single_vertex_relabel(*vertex_data[v], tuple(relabel_dict[v].items()))

            relabel_basis_dict_dict = {i: relabel_basis_dict(*vertex_data[i], tuple(relabel_dict[i].items())) for i in range(num_vert) if i != v and relabel_dict[i]}
            if nontrivial_aut_target:
                basismap = prod_to_as_basis(*graph_data, r)

            for S in prod_basis_iter(vertex_data):
                LL = []
                for v2 in range(num_vert):
                    if v == v2:
                        LL.append(dlsvr[S[v]])
                    else:
                        if relabel_dict[v2]:
                            LL.append(relabel_basis_dict_dict[v2][S[v2]])
                        else:
                            LL.append([(S[v2], 1)])
                for BB in itertools.product(*LL):
                    coeff = c0
                    pre_can_target_S = []
                    for s, c in BB:
                        coeff *= c
                        pre_can_target_S.append(s)
                    target_S = tuple(pre_can_target_S[dicv_inv[v3]] for v3 in range(num_vert))
                    if nontrivial_aut_target:
                        target_in_basisvec = coeff * basismap[(target_r_split, target_S)]
                    else:
                        target_in_basisvec = vector([coeff if key[0][:2] == (target_r_split, target_S) else 0 for key in as_basis_iter(*graph_data, r)])
                    try:
                        result[(r_split, S)][target_ind] += target_in_basisvec
                    except KeyError:
                        result[(r_split, S)][target_ind] = target_in_basisvec
    return result


@file_cache.file_cached_function(
    directory=os.path.join(DOT_SAGE, "admcycles/cohomology/GK"),
    key=file_cache.ignore_args_key([]),
    filename=file_cache.ignore_args_filename())
def GK_image(g, n, gamma_r, r, n_part, moduli_type='sm'):
    r"""
    Computes the image of the differential on the E_1 page.
    """
    if n_part is None:
        raise ValueError('give the trivial partition instead of `None`')
    if gamma_r < 0 or r < 0 or gamma_r + r == 3 * g - 3 + n:
        raise ValueError('this case is trivial and should be dealt with elsewhere')

    if len(n_part) == n:
        graph_inds = get_strata_list_inds(g, n, gamma_r, moduli_type)
        Ms = [[GK_image_single_gamma(g, n, gamma_r, ind, r, moduli_type)] for ind in graph_inds]
    else:
        matrices = defaultdict(list)
        for ind in get_strata_list_inds(g, n, gamma_r + 1, moduli_type):
            if GK_symmetrized_graph_image.file_exists(g, n, gamma_r + 1, ind, r, n_part, moduli_type):
                new_vecs, sym_ind = GK_symmetrized_graph_image(g, n, gamma_r + 1, ind, r, n_part, moduli_type)
                matrices[sym_ind].append(matrix(new_vecs))
            else:
                assert (as_basis_rank(g, n, gamma_r + 1, ind, r) == 0)
        Ms = [[sum(M_list) for M_list in matrices.values()]]
    M = block_matrix(Ms, subdivide=False)
    del (Ms)
    M.echelonize()
    M = M.matrix_from_rows(range(M.rank()))
    return M


@file_cache.file_cached_function(
    directory=os.path.join(DOT_SAGE, "admcycles/cohomology/GK"),
    key=file_cache.ignore_args_key([]),
    filename=file_cache.ignore_args_filename())
def GK_image_non_echelon(g, n, gamma_r, r, n_part):
    r"""
    Computes the image of the differential on the E1 page but does not calculate
    the row echelon form.
    """
    if n_part is None:
        raise ValueError('give the trivial partition instead of `None`')
    if gamma_r < 0 or r < 0 or gamma_r + r == 3 * g - 3 + n:
        raise ValueError('this case is trivial and should be dealt with elsewhere')

    if len(n_part) == n:
        nr_graphs = len(list_strata_can(g, n, gamma_r))
        Ms = [[GK_image_single_gamma(g, n, gamma_r, ind, r)] for ind in range(nr_graphs)]
    else:
        nr_graphs = len(list_strata_can(g, n, gamma_r + 1))
        matrices = defaultdict(list)
        for ind in range(nr_graphs):
            if GK_symmetrized_graph_image.file_exists(g, n, gamma_r + 1, ind, r, n_part):
                new_vecs, sym_ind = GK_symmetrized_graph_image(g, n, gamma_r + 1, ind, r, n_part)
                matrices[sym_ind].append(matrix(new_vecs))
            else:
                assert (as_basis_rank(g, n, gamma_r + 1, ind, r) == 0)
        Ms = [[sum(M_list) for M_list in matrices.values()]]
    M = block_matrix(Ms, subdivide=False)
    return M


def GK_image_echelonize(g, n, gamma_r, r, n_part):
    r"""
    Computes the row echelon form for the output of ``GK_image_non_echelon`` and
    stores it under ``GK_image``.
    """
    M = GK_image_non_echelon(g, n, gamma_r, r, n_part)
    M.echelonize(algorithm='flint')
    M = M.matrix_from_rows(range(M.rank()))
    M = GK_image.set_cache(M, g, n, gamma_r, r, n_part)
    try:
        GK_image_non_echelon.remove_file(g, n, gamma_r, r, n_part)
    except Exception:
        pass
    return


@file_cache.file_cached_function(
    directory=os.path.join(DOT_SAGE, "admcycles/cohomology/GK"),
    key=file_cache.ignore_args_key([]),
    filename=file_cache.ignore_args_filename())
def GK_image_rank(g, n, gamma_r, r, n_part, moduli_type='sm'):
    r"""
    Computes the rank of the image of the differential on the E_1 page.
    """
    if gamma_r >= 3 * g - 3 + n - r:
        return 0
    return GK_image(g, n, gamma_r, r, n_part, moduli_type).rank()


def GK_kernel_rank(g, n, gamma_r, r, n_part, moduli_type='sm'):
    r"""
    Computes the rank of the kernel of the differential on the E_1 page.
    """
    rank = 0
    new_graphs = []
    for i in get_strata_list_inds(g, n, gamma_r, moduli_type):
        new_i = symmetrize_graph(g, n, gamma_r, i, n_part)
        if new_i in new_graphs:
            continue
        new_graphs.append(new_i)
        rank += as_basis_rank(g, n, gamma_r, i, r, n_part)
    rank -= GK_image_rank(g, n, gamma_r, r, n_part, moduli_type)
    return rank


@file_cache.file_cached_function(
    directory=os.path.join(DOT_SAGE, "admcycles/cohomology/GK/sym"),
    key=file_cache.ignore_args_key([7, 8]),
    filename=file_cache.ignore_args_filename())
def GK_symmetrized_graph_image(g, n, gamma_r, ind, r, n_part, moduli_type, index1=None, index2=None):
    r"""
    Symmetrizes the image for a specific graph.
    That is, each element is sent to a representative of its S_{n_part} orbit.
    """
    if index1 is None or index2 is None:
        raise ValueError("should have already computed this")
    vecs = GK_image(g, n, gamma_r - 1, r, tuple([1] * n), moduli_type).matrix_from_columns(range(index1, index2)).rows()
    return symmetrize_as_basis_Sn_action(g, n, gamma_r, ind, r, n_part, vecs)
