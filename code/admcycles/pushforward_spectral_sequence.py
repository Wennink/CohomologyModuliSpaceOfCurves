from collections import defaultdict
import itertools
import os
from sage.env import DOT_SAGE
from sage.matrix.constructor import matrix
from sage.misc.cachefunc import cached_function
from sage.matrix.special import block_matrix
from sage.modules.free_module_element import vector
from sage.rings.all import QQ
from sage.groups.perm_gps.permgroup_named import SymmetricGroup
from .admcycles import prodtautclass, generating_indices
from .utils import get_marks_part
from .symmetry import general_generating_indices
from .list_strata import list_strata_can, get_strata_list_inds
from .antisymmetry import symmetrize_as_basis_Sn_action, prod_to_as_basis, as_basis_rank, symmetric_canonicalization_data, as_basis_iter, dec_to_basis_as, sym_elem_to_dic, symmetrize_graph, vertex_data_iter, prod_basis_iter, prod_basis_elem_iter, get_graph_data
from . import file_cache


def pushforward_E2_rank(g, n, p, q, n_part, moduli_type='sm'):
    r"""
    Compute the rank of E_2^{-p, q} for
    Deligne's pushforward spectral sequence
    w.l.o.g. we take q in complex dimension because the answer
    is 0 when it would be odd (in real dimension).
    """
    r = q - p
    if r < 0:
        raise ValueError('answer is trivial here')
    if r == 0:
        if len(n_part) == n:
            return compute_kernel_rank(g, n, p, r, moduli_type)
        return compute_kernel_rank_sym(g, n, p, r, n_part, moduli_type)
    if len(n_part) == n:
        return compute_kernel_rank(g, n, p, r, moduli_type) - compute_image_rank(g, n, p + 1, r - 1, moduli_type)
    return compute_kernel_rank_sym(g, n, p, r, n_part, moduli_type) - compute_image_rank_sym(g, n, p + 1, r - 1, n_part, moduli_type)


@file_cache.file_cached_function(
    directory=os.path.join(DOT_SAGE, "admcycles/cohomology/weight_seq/sym"),
    key=file_cache.ignore_args_key([7, 8]),
    filename=file_cache.ignore_args_filename())
def symmetrize_graph_contribution(g, n, gamma_r, ind, r, n_part, moduli_type, index1=None, index2=None):
    r"""
    Symmetrizes the image for a specific graph.
    That is, each element is sent to a representative of its S_{n_part} orbit.
    """
    if index1 is None or index2 is None:
        raise ValueError("should have already computed this")
    vecs = compute_image(g, n, gamma_r + 1, r - 1, moduli_type=moduli_type).matrix_from_columns(range(index1, index2)).rows()
    return symmetrize_as_basis_Sn_action(g, n, gamma_r, ind, r, n_part, vecs)


# would be nice to clean this up and combine it with ``get_vertex_symmetric_action_canon``
# note that they do return different results
def get_vertex_symmetric_action(g, n, gamma_r, ind, n_part, canonalized=True):
    r"""
    Returns combinatorial data describing the reordering of the marked
    points at each vertex that occurs when symmetrizing a graph.
    """
    gamma = list(list_strata_can(g, n, gamma_r))[ind]
    result_parts = []
    result_markings = []
    result_markings_canon = []
    result_local_gs = []
    result_local_gs_canon = []
    new_marks = get_marks_part(n, n_part)
    if canonalized:
        _, dicv, dicl = symmetric_canonicalization_data(g, n, gamma_r, ind, n_part)
        inv_dicv = {j: i for i, j in dicv.items()}
    for pre_v in range(len(gamma.legs())):
        if canonalized:
            v = inv_dicv[pre_v]
        else:
            v = pre_v
        legs = gamma.legs(v)
        num_legs = len(legs)
        legdic = {}
        number_mp = -1
        for i, l in enumerate(legs):
            if l > n:
                # am assuming legs are always ordered to the extend that actual marks come first
                number_mp = i
                break
            try:
                legdic[new_marks[l - 1]].append(i)
            except KeyError:
                legdic[new_marks[l - 1]] = [i]
        if not legs:
            number_mp = 0
        elif number_mp == -1:
            number_mp = i + 1
        nr_unique_mp = len(legdic)
        new_legs = [0] * number_mp + list(range(nr_unique_mp + 1, nr_unique_mp + 1 + num_legs - number_mp))
        # we just input the legs, but in a different order so that the result will be standardized
        # e.g. it gives (1,2,2) and so I put (2,1,1)
        # this is a permutation of the true result, but it shouldn't matter for the rank as long as we're consistent
        new_nr = 1
        new_part = []
        max_legs = [(-len(va), k, va) for k, va in legdic.items()]
        max_legs.sort()
        for lenml, k, ml in max_legs:
            for l in ml:
                new_legs[l] = new_nr
            new_nr += 1
            new_part.append(-lenml)
        new_part += [1] * (num_legs - sum(new_part))
        if canonalized:
            new_legs_canon = [new_legs[dicl[v][i + 1] - 1] if i + 1 in dicl[v] else l for i, l in enumerate(new_legs)]

        self_edges = gamma.edges_between(v, v)
        if self_edges:
            try:
                # number of the first nonsym (not counting self_edges)
                num = new_part.index(1) + 1
            except ValueError:
                num = 1
            nr_self_edges = len(self_edges)
            nr1 = new_part.count(1)
            new_part = new_part[:-nr1] + [2] * nr_self_edges + [1] * (nr1 - 2 * nr_self_edges)
            self_edge_L_canon = []
            for x in self_edges:
                edge_nrs = []
                for y in x:
                    z = legs.index(y)
                    if z + 1 in dicl[v]:
                        z = dicl[v][z + 1] - 1
                    edge_nrs.append(new_legs_canon[z])
                edge_nrs.sort()
                self_edge_L_canon += edge_nrs
            self_edge_L = [new_legs[legs.index(x)] for y in self_edges for x in y]
            for i in range(num_legs):
                if new_legs[i] < num:
                    continue
                not_self_edge = True
                broken = 1
                for j, he in enumerate(self_edge_L):
                    if new_legs[i] == he:
                        new_legs[i] = num + QQ((j, 2)).floor()
                        not_self_edge = False
                        break
                    if new_legs[i] < he:
                        broken = 0
                        break
                if not_self_edge:
                    new_legs[i] += nr_self_edges - (j + broken)
            for i in range(num_legs):
                if new_legs_canon[i] < num:
                    continue
                not_self_edge = True
                broken = 1
                for j, he in enumerate(self_edge_L_canon):
                    if new_legs_canon[i] == he:
                        new_legs_canon[i] = num + QQ((j, 2)).floor()
                        not_self_edge = False
                        break
                    if new_legs_canon[i] < he:
                        broken = 0
                        break
                if not_self_edge:
                    new_legs_canon[i] += nr_self_edges - (j + broken)
        dicmap_canon = []
        ordered_new_legs = get_marks_part(num_legs, new_part)
        seen = defaultdict(int)
        for l in new_legs_canon:
            val = ordered_new_legs.index(l) + 1
            dicmap_canon.append(val + seen[val])
            seen[val] += 1

        dicmap = []
        seen = defaultdict(int)
        for l in new_legs:
            val = ordered_new_legs.index(l) + 1
            dicmap.append(val + seen[val])
            seen[val] += 1

        result_parts.append(tuple(new_part))
        result_markings.append(tuple(new_legs))
        result_markings_canon.append(tuple(new_legs_canon))
        result_local_gs.append(SymmetricGroup(num_legs)(dicmap))
        result_local_gs_canon.append(SymmetricGroup(num_legs)(dicmap_canon))
    # currently not using all the outputs
    return result_parts, result_markings, result_markings_canon, result_local_gs, result_local_gs_canon


@file_cache.file_cached_function(
    directory=os.path.join(DOT_SAGE, "admcycles/cohomology/weight_seq"),
    key=file_cache.ignore_args_key([]),
    filename=file_cache.ignore_args_filename())
def compute_image_rank_sym(g, n, gamma_r, r, n_part, moduli_type='sm'):
    r"""
    computes the rank of the image of the differential on the E_1 page
    invariant under the S_{n_part}-action.
    """
    if gamma_r == 0:
        return 0
    if gamma_r < 0 or r < 0:
        raise ValueError('this case should be avoided')

    matrices = defaultdict(list)
    for i in get_strata_list_inds(g, n, gamma_r - 1, moduli_type):
        if symmetrize_graph_contribution.file_exists(g, n, gamma_r - 1, i, r + 1, n_part, moduli_type):
            new_vecs, sym_ind = symmetrize_graph_contribution(g, n, gamma_r - 1, i, r + 1, n_part, moduli_type)
            matrices[sym_ind].append(matrix(new_vecs))
        else:
            assert (as_basis_rank(g, n, gamma_r - 1, i, r + 1) == 0)
    summed_matrices = [sum(Ms) for Ms in matrices.values()]
    del (matrices)
    sym_image = block_matrix([summed_matrices], subdivide=False)
    return sym_image.rank()


def compute_kernel_rank_sym(g, n, gamma_r, r, n_part, moduli_type='sm'):
    r"""
    computes the rank of the image of the differential on the E_1 page
    invariant under the S_{n_part}-action.
    """
    if gamma_r == 0:
        return len(general_generating_indices(g, n, r, n_part=n_part))
    if gamma_r < 1:
        return 0
    rank = 0
    new_graphs = []
    for i in get_strata_list_inds(g, n, gamma_r, moduli_type):
        new_i = symmetrize_graph(g, n, gamma_r, i, n_part)
        if new_i in new_graphs:
            continue
        new_graphs.append(new_i)
        rank += as_basis_rank(g, n, gamma_r, i, r, tuple(n_part))
    rank -= compute_image_rank_sym(g, n, gamma_r, r, n_part, moduli_type)
    return rank


def edge_contraction_data(gamma, ind):
    target_G = gamma.copy()
    e = gamma._edges[ind]
    av, edge_graph, vnum, dicv = target_G.contract_edge(e, adddata=True)
    relabel_dic = {j: i + 1 for i, j in enumerate(target_G.legs(av))}
    edge_G_n = len(relabel_dic)
    for e0, e1 in edge_graph.edges():
        if e0 <= edge_G_n or e1 <= edge_G_n:
            ml = edge_graph._maxleg
            relabel_dic[e0] = ml + 1
            relabel_dic[e1] = ml + 2
            edge_graph._maxleg += 2
    new_edge_graph = edge_graph.relabel({}, relabel_dic, inplace=False)
    temp_G = target_G.copy()
    dicv2, dicl = target_G.set_canonical_label(certificate=True, sortlegs=True)
    legdics = []
    for v in range(target_G.num_verts()):
        legd = {}
        for i, l in enumerate(temp_G.legs(v)):
            try:
                l2 = dicl[l]
            except KeyError:
                l2 = l
            new_i = target_G.legs(dicv2[v]).index(l2)
            if new_i != i:
                legd[i + 1] = new_i + 1
        legdics.append(legd)
    edge_G = new_edge_graph.relabel({}, legdics[av])
    dicv2_inv = {j: i for i, j in dicv2.items()}
    new_legdics = [legdics[dicv2_inv[i]] for i in range(len(legdics))]
    dicv_combined_inv = {dicv2[dicv[v]]: v for v in range(gamma.num_verts()) if v not in vnum}
    p = []
    for e0, e1 in gamma._edges:
        if (e0, e1) == e:
            continue
        f0 = dicl[e0]
        for i, f in enumerate(target_G._edges):
            if f0 in f:
                p.append(i)
                break
    if len(p) != len(target_G._edges):
        raise ValueError
    A = SymmetricGroup(list(range(len(target_G._edges))))
    coeff_sign = A(p).sign() * (-1) ** ind
    return (dicv2[av], target_G, edge_G, vnum, dicv_combined_inv, new_legdics, coeff_sign)


@file_cache.file_cached_function(
    directory=os.path.join(DOT_SAGE, "admcycles/cohomology/weight_seq/diffmap"),
    key=file_cache.ignore_args_key([]),
    filename=file_cache.ignore_args_filename())
def diffmap_prod_basis_single_target(g, n, gamma_r, ind, e_i, r):
    r"""
    Computes the contribution to differential on the E_1 page
    obtained from contracting the edge ``e_i``.
    The domain is the product basis on H^r(M_\Gamma).
    """
    gamma = list(list_strata_can(g, n, gamma_r))[ind]
    av, target_G, edge_G, vnum, inv_dicv, legdics, coeff_sign = edge_contraction_data(gamma, e_i)
    target_G_data = get_graph_data(target_G)
    num_vert = target_G.num_verts()
    nv_parts, _, _, local_gs, _ = get_vertex_symmetric_action(*target_G_data, n_part=[1] * n)
    pre_nv_parts, _, _, pre_local_gs, _ = get_vertex_symmetric_action(g, n, gamma_r, ind, n_part=[1] * n)
    result = {}
    nontrivial_aut = len(gamma.leg_automorphism_group()) != 1
    nontrivial_aut_target = len(target_G.leg_automorphism_group()) != 1
    if nontrivial_aut:
        pre_dics_inv = [sym_elem_to_dic(pre_local_gs[pre_v].inverse()) for pre_v in range(len(gamma.genera()))]
    if nontrivial_aut_target:
        basismap = prod_to_as_basis(*target_G_data, r + 1)
        dics = [sym_elem_to_dic(local_gs[v]) for v in range(num_vert)]

    target_rank = as_basis_rank(*target_G_data, r + 1)

    exemptions = [inv_dicv[v] for v in range(num_vert) if (not v == av) and len(target_G.edges_between(v, v)) >= 2 and legdics[v] == {}]

    for r_split, vertex_data in vertex_data_iter(gamma, r, pre_nv_parts):
        target_r_split = tuple([r_split[inv_dicv[v]] if v != av else 1 + sum([r_split[vv] for vv in vnum]) for v in range(num_vert)])
        target_v_data = []
        for v, tgv in enumerate(target_G.genera()):
            target_v_data.append((tgv, target_G.num_legs(v), target_r_split[v], nv_parts[v], len(target_G.edges_between(v, v))))
        for S in prod_basis_iter(vertex_data):
            target_in_basisvec = vector(QQ, target_rank)
            for dec_list, prod_coeff in prod_basis_elem_iter(S, vertex_data, exemptions):
                S3_list = []
                for v, gv in enumerate(target_G.genera()):
                    if v == av:
                        L = []
                        for pre_v in vnum:
                            L.append(dec_list[pre_v])
                            if nontrivial_aut and pre_dics_inv[pre_v]:
                                L[-1] = L[-1].relabel(pre_dics_inv[pre_v])
                        edge_ptc = prodtautclass(edge_G, [L])
                        edge_push_tc = edge_ptc.pushforward()
                        edge_push_dec = list(edge_push_tc._terms.values())[0]
                        if nontrivial_aut_target and dics[v]:
                            edge_push_dec = edge_push_dec.relabel(dics[v])

                        S3_list.append(dec_to_basis_as(edge_push_dec, *target_v_data[v]))
                    elif legdics[v]:
                        dec = dec_list[inv_dicv[v]]
                        if nontrivial_aut and pre_dics_inv[inv_dicv[v]]:
                            dec = dec.relabel(pre_dics_inv[inv_dicv[v]])
                        dec = dec.relabel(legdics[v])
                        if nontrivial_aut_target and dics[v]:
                            dec = dec.relabel(dics[v])
                        S3_list.append(dec_to_basis_as(dec, *target_v_data[v]))
                    else:
                        S3_list.append(((S[inv_dicv[v]], 1),))

                for S3 in itertools.product(*S3_list):
                    coeff = coeff_sign * prod_coeff
                    target_S = []
                    for s3, c3 in S3:
                        coeff *= c3
                        target_S.append(s3)
                    target_S = tuple(target_S)
                    if nontrivial_aut_target:
                        target_in_basisvec += coeff * basismap[(target_r_split, target_S)]
                    else:
                        # consider a sparse implementation
                        target_in_basisvec += vector([coeff if key[0][:2] == (target_r_split, target_S) else 0 for key in as_basis_iter(*target_G_data, r + 1)])
            result[(r_split, S)] = target_in_basisvec

    return target_G_data[3], result


@file_cache.file_cached_function(
    directory=os.path.join(DOT_SAGE, "admcycles/cohomology/weight_seq/diffmap"),
    key=file_cache.ignore_args_key([]),
    filename=file_cache.ignore_args_filename())
def precompute_matrix_image_single_gamma(g, n, gamma_r, ind, r):
    r"""
    Precomputes the matrix for the image of a single graph in order to save memory later.
    """
    keys = [diffmap_prod_basis_single_target(g, n, gamma_r, ind, i, r)[0] for i in range(gamma_r)]
    maps = [diffmap_prod_basis_single_target(g, n, gamma_r, ind, i, r)[1] for i in range(gamma_r)]
    key_dict = defaultdict(list)
    for i, k in enumerate(keys):
        key_dict[k].append(i)
    vec_lists = [[] for _ in range(len(key_dict))]
    for basis_elem in as_basis_iter(g, n, gamma_r, ind, r):
        for r_split_l, S_l, basis_coeff in basis_elem:
            r_split = tuple(r_split_l)
            S = tuple(S_l)
            for j, i_list in enumerate(key_dict.values()):
                vec_lists[j].append(basis_coeff * sum([maps[i][(r_split, S)] for i in i_list]))

    if len(vec_lists[0]) == 0:
        return []
    M = block_matrix([[matrix(rows) for rows in vec_lists]], subdivide=False)
    return M


@file_cache.file_cached_function(
    directory=os.path.join(DOT_SAGE, "admcycles/cohomology/weight_seq/diffmap"),
    key=file_cache.ignore_args_key([5, 6]),
    filename=file_cache.ignore_args_filename())
def compute_image_single_gamma(g, n, gamma_r, ind, r, delete_files=False, precompute_matrix=False):
    r"""
    Computes the image of the differential restricted to a single graph.
    """
    if precompute_matrix:
        M = precompute_matrix_image_single_gamma(g, n, gamma_r, ind, r)
    else:
        keys = [diffmap_prod_basis_single_target(g, n, gamma_r, ind, i, r)[0] for i in range(gamma_r)]
        maps = [diffmap_prod_basis_single_target(g, n, gamma_r, ind, i, r)[1] for i in range(gamma_r)]
        key_dict = defaultdict(list)
        for i, k in enumerate(keys):
            key_dict[k].append(i)
        vec_lists = [[] for _ in range(len(key_dict))]
        for basis_elem in as_basis_iter(g, n, gamma_r, ind, r):
            temp = [0 for _ in range(len(key_dict))]
            for r_split_l, S_l, basis_coeff in basis_elem:
                r_split = tuple(r_split_l)
                S = tuple(S_l)
                for j, i_list in enumerate(key_dict.values()):
                    temp[j] += basis_coeff * sum([maps[i][(r_split, S)] for i in i_list])
            for j in range(len(key_dict)):
                vec_lists[j].append(temp[j])
        if len(vec_lists[0]) == 0:
            return []
        M = block_matrix([[matrix(rows) for rows in vec_lists]], subdivide=False)
    M.echelonize()

    indices = [0]
    for vec_list in vec_lists:
        indices.append(indices[-1] + len(vec_list[0]))

    new_image = []
    for rr in M.rows():
        if rr.is_zero():
            break
        im_elem = {}
        for i, key in enumerate(key_dict.keys()):
            im_elem[key] = vector(rr[indices[i]: indices[i + 1]])
        new_image.append(im_elem)
    if delete_files:
        try:
            for i in range(gamma_r):
                if precompute_matrix:
                    diffmap_prod_basis_single_target.remove_file(g, n, gamma_r, ind, i, r)
                precompute_matrix_image_single_gamma.remove_file(g, n, gamma_r, ind, i, r)
        except Exception:
            pass
    return new_image


@file_cache.file_cached_function(
    directory=os.path.join(DOT_SAGE, "admcycles/cohomology/weight_seq"),
    key=file_cache.ignore_args_key([4]),
    filename=file_cache.ignore_args_filename())
def compute_image(g, n, gamma_r, r, delete_files=False, moduli_type='sm'):
    r"""
    Computes the image of the differential on the E_1 page.
    """
    if gamma_r < 1 or r < 0:
        return 0

    indices = {}
    current = 0
    for i in get_strata_list_inds(g, n, gamma_r - 1, moduli_type):
        indices[i] = current
        current += as_basis_rank(g, n, gamma_r - 1, i, r + 1)
    ncols = current

    rows = []
    for ind in get_strata_list_inds(g, n, gamma_r, moduli_type):
        for im_elem in compute_image_single_gamma(g, n, gamma_r, ind, r, delete_files=delete_files):
            row = vector(QQ, ncols)
            for i, vec in im_elem.items():
                indi = indices[i]
                for i, c in enumerate(vec):
                    row[indi + i] += c
            rows.append(row)
    if rows:
        M = matrix(rows)
    else:
        M = matrix(0, ncols)
    if delete_files:
        print('not deleting file atm for compute_image_single_gamma')
    return M


@cached_function
def compute_image_rank(g, n, gamma_r, r, moduli_type='sm'):
    r"""
    Computes the rank of the image of the differential on the E_1 page.
    """
    if gamma_r < 1 or r < 0:
        return 0
    M = compute_image(g, n, gamma_r, r, moduli_type=moduli_type)
    result = M.rank()
    return result


def compute_kernel_rank(g, n, gamma_r, r, moduli_type='sm'):
    r"""
    Computes the rank of the kernel of the differential on the E_1 page.
    """
    if gamma_r == 0:
        return len(generating_indices(g, n, r))
    if gamma_r < 1:
        return 0
    rank = 0
    for i in get_strata_list_inds(g, n, gamma_r, moduli_type):
        rank += as_basis_rank(g, n, gamma_r, i, r)
    rank -= compute_image_rank(g, n, gamma_r, r, moduli_type)
    return rank
