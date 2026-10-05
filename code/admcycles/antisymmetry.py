import itertools
from collections import defaultdict

from sage.matrix.constructor import matrix
from sage.misc.cachefunc import cached_function
from sage.combinat.integer_vector import IntegerVectors
from sage.modules.free_module_element import vector
from sage.rings.all import QQ
from sage.groups.perm_gps.permgroup_named import SymmetricGroup

from .admcycles import Pixtongraph, prodtautclass, genstobasis
from .list_strata import list_strata_can
from .moduli import get_moduli
from .stable_graph import StableGraph
from .symmetry import get_marks_part, tautgens_single, tautgens_sym, general_generating_indices, general_genstobasis, genstobasis_Sn
from .DR.symmetry import symmetrize_map
from . import DR

from . import file_cache
import shelve
import os
from sage.env import DOT_SAGE


def dec_to_basis_as(dec, g, n, r, n_part, self_edges, sparse_list=True):
    r"""
    Expresses the decstratum ``dec`` in terms of the basis given by
    ``generating_indices_as`` or ``general_generating_indices``,
    depending on the result of ``use_as_gens``
    """
    moduli_st = get_moduli('st', DRpy=True)
    dec_num = DR.num_of_stratum(Pixtongraph(dec.gamma, dec.poly[0][0], dec.poly[0][1], n_part=n_part), g, r, get_marks_part(n, n_part), moduli_type=moduli_st)
    if not use_as_gens(g, n, r, n_part, self_edges):
        result = general_genstobasis(g, n, r, n_part)[dec_num]
        if sparse_list:
            return [(i, c) for i, c in enumerate(result) if c != 0]
        else:
            return result
    else:
        dtad = dec_to_as(g, n, r, n_part, self_edges)[dec_num]
        if dtad is None:
            # note that this gives type errors if not sparse list
            return []
        as_num, c2 = dtad
        result = genstobasis_as(g, n, r, n_part, self_edges)[as_num]
        if sparse_list:
            return [(i, c * c2) for i, c in enumerate(result) if c != 0]
        else:
            return c2 * result


def dec_to_basis_iter(input_decs, vertex_data):
    S_list = []
    for v, dec in enumerate(input_decs):
        S_list.append(dec_to_basis_as(dec, *vertex_data[v]))
    for S in itertools.product(*S_list):
        yield S
    return


def sym_elem_to_dic(s):
    dic = {}
    for i in s.parent().domain():
        i_m = s(i)
        if i_m != i:
            dic[i] = i_m
    return dic


def get_graph_data(G):
    g, n, r = G.g(), G.n(), len(G.edges())
    for i, GG in enumerate(list_strata_can(g, n, r)):
        if G == GG:
            return (g, n, r, i)
    raise ValueError


def symmetric_canonicalization_data(g, n, gamma_r, ind, n_part):
    r"""
    Returns the difference in the ordering of the combinatorial data between
    the canonical form of a graph and the canonical form of its symmetrization
    """
    gamma = list(list_strata_can(g, n, gamma_r))[ind]
    gamma2 = gamma.copy(mutable=True)
    new_markings = get_marks_part(n, n_part)
    for leg_v in gamma2._legs:
        for i in range(len(leg_v)):
            if leg_v[i] <= n:
                leg_v[i] = new_markings[leg_v[i] - 1]
    temp_gamma = gamma2.copy()
    dicv, dicl = gamma2.set_canonical_label_symm(certificate=True, sortlegs=True)
    # dicl could have self_edge relabeling, which is unnecessary but should also be harmless
    p = []
    for e0, e1 in gamma._edges:
        f0 = dicl[e0]
        for i, f in enumerate(gamma2._edges):
            if f0 in f:
                p.append(i)
                break
    A = SymmetricGroup(list(range(len(gamma2._edges))))

    legdics = []
    for v in range(temp_gamma.num_verts()):
        leg_pos = {}
        gam2legs = gamma2.legs(dicv[v])
        for l in set(gam2legs):
            leg_pos[l] = iter([i for i, a in enumerate(gam2legs) if a == l])
        legd = {}
        for i, l in enumerate(temp_gamma.legs(v)):
            try:
                l2 = dicl[l]
            except KeyError:
                l2 = l
            new_i = next(leg_pos[l2])
            if new_i != i:
                legd[i + 1] = new_i + 1
        legdics.append(legd)

    return A(p).sign(), dicv, legdics


def symmetrize_graph(g, n, gamma_r, ind, n_part):
    r"""
    Returns the index of the symmetrized graph at index ``ind`` of ``list_strata_can``
    """
    gamma = list(list_strata_can(g, n, gamma_r))[ind]
    v_num = len(gamma.genera())
    markings = tuple(range(1, n + 1))
    gamma_num = DR.num_of_stratum(Pixtongraph(gamma, [[]] * v_num, {}), g, gamma_r, markings, moduli_type=get_moduli('st', DRpy=True))
    new_markings = get_marks_part(n, n_part)
    symmap = symmetrize_map(g, gamma_r, markings, new_markings, moduli_type=get_moduli('st', DRpy=True))
    return symmap[gamma_num]


def get_sym_graph_canon(g, n, gamma_r, n_part, ind):
    r"""
    Returns the symmetrized canonical version of the graph of the decstratum at index ``ind``
    """
    gamma = tautgens_single(g, n, gamma_r, ind, moduli='st', n_part=n_part, sym_labels=True).gamma.copy(mutable=True)
    gamma.set_canonical_label_symm(sortlegs=True)
    return gamma


def get_graph_sym_canon_arranged(g, n, gamma_r, ind, n_part):
    r"""
    Returns the symmetrization of a graph with the data ordered like
    the canonical form of the graph before symmetrization.
    """
    gamma = list(list_strata_can(g, n, gamma_r))[ind]
    gamma2 = gamma.copy(mutable=True)
    new_markings = get_marks_part(n, n_part)
    for leg_v in gamma2._legs:
        for i in range(len(leg_v)):
            if leg_v[i] <= n:
                leg_v[i] = new_markings[leg_v[i] - 1]
    inv_dicv, dicl = gamma2.set_canonical_label_symm(certificate=True, sortlegs=True)
    # dicl could have self_edge relabeling, which is unnecessary but should also be harmless
    dicv = {i: j for j, i in inv_dicv.items()}

    num_vert = gamma.num_verts()
    V = [gamma._genera[dicv[v]] for v in range(num_vert)]
    E = []
    for e in gamma._edges:
        new_edge = []
        for e_i in e:
            if e_i in dicl:
                new_edge.append(dicl[e_i])
            else:
                new_edge.append(e_i)
        new_edge.sort()
        E.append(tuple(new_edge))
    E.sort()
    L = []
    for v in range(num_vert):
        new_legs = []
        for l in gamma.legs(v):
            if l in dicl:
                new_legs.append(dicl[l])
            else:
                new_legs.append(l)
        new_legs.sort()
        L.append(new_legs)
    L = [L[dicv[v]] for v in range(num_vert)]
    return StableGraph(V, L, E)


def get_vertex_symmetric_action_canon(g, n, gamma_r, ind, n_part, n_part_canon):
    r"""
    Returns combinatorial data describing the reordering of the marked
    points at each vertex that occurs when symmetrizing a graph.
    """
    gamma = get_graph_sym_canon_arranged(g, n, gamma_r, ind, n_part_canon)
    result_parts = []
    result_markings = []
    result_local_gs = []
    new_marks = get_marks_part(n, n_part)
    for v in range(len(gamma.legs())):
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
        # we input the legs, but in a different order so that the result will be standardized
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
        ordered_new_legs = get_marks_part(num_legs, new_part)

        dicmap = []
        seen = defaultdict(int)
        for l in new_legs:
            val = ordered_new_legs.index(l) + 1
            dicmap.append(val + seen[val])
            seen[val] += 1

        result_parts.append(tuple(new_part))
        result_markings.append(tuple(new_legs))
        result_local_gs.append(SymmetricGroup(num_legs)(dicmap))
    return result_parts, result_markings, result_local_gs


def symmetrize_as_basis_Sn_action(g, n, gamma_r, ind, r, n_part, vecs):
    r"""
    Takes a list of vectors ``vecs`` on (H^r(M_\Gamma)\otimes Det(E_\Gamma))^Aut(\Gamma).
    The output is the symmetrization of these vectors.
    That is, each element is sent to a representative of its S_{n_part} orbit.
    """
    gamma = get_graph_sym_canon_arranged(g, n, gamma_r, ind, n_part)
    sym_ind = symmetrize_graph(g, n, gamma_r, ind, n_part)
    # we need to canonicalalize in order to use the basismap
    can_sym_gamma = get_sym_graph_canon(g, n, gamma_r, n_part, sym_ind)
    num_vert = len(gamma.genera())
    sym_sign, dicv, legdics = symmetric_canonicalization_data(g, n, gamma_r, ind, n_part)
    inv_dicv = {i: j for j, i in dicv.items()}

    pre_nparts, _, _ = get_vertex_symmetric_action_canon(g, n, gamma_r, ind, [1] * n, n_part)
    _, _, pre_local_gs = get_vertex_symmetric_action_canon(g, n, gamma_r, ind, [1] * n, [1] * n)
    nv_parts, markings, local_gs = get_vertex_symmetric_action_canon(g, n, gamma_r, ind, n_part, n_part)
    nontrivial_aut = len(can_sym_gamma.leg_automorphism_group()) != 1
    if nontrivial_aut:
        basismap = prod_to_as_basis(g, n, gamma_r, ind, r, tuple(n_part))
    pre_se_dics_inv = [sym_elem_to_dic(pre_local_gs[pre_v].inverse()) for pre_v in range(num_vert)]
    se_dics = [sym_elem_to_dic(local_gs[v]) for v in range(num_vert)]
    basis_dic = {}
    moduli = get_moduli('st', DRpy=True)
    length = as_basis_rank(g, n, gamma_r, ind, r, tuple(n_part))
    for ind2, basis_elem in enumerate(as_basis_iter(g, n, gamma_r, ind, r)):
        new_basis_elem = vector(QQ, length)
        for pre_r_split, S, basis_coeff in basis_elem:
            r_split = tuple([pre_r_split[inv_dicv[v]] for v in range(len(pre_r_split))])
            vertex_data = []
            for v, gv in enumerate(gamma.genera()):
                vertex_data.append((gv, gamma.num_legs(v), r_split[v], pre_nparts[v], len(gamma.edges_between(v, v))))
            S_inv = tuple([S[inv_dicv[v]] for v in range(len(S))])
            for dec_list, prod_coeff in prod_basis_elem_iter(S_inv, vertex_data):
                # we are using that the local point ordering is preserved for a canonical graph
                new_S_lists = []
                for v in range(len(gamma.genera())):
                    inv_v = inv_dicv[v]
                    dec = dec_list[v]
                    if pre_se_dics_inv[inv_v]:
                        dec = dec.relabel(pre_se_dics_inv[inv_v])
                    dec = dec.relabel(legdics[inv_v])
                    dec = dec.copy(mutable=True)
                    gv, nv, rv, _, se_v = vertex_data[v]
                    v_part = nv_parts[v]
                    v_legs = get_marks_part(nv, v_part)

                    if se_dics[v]:
                        dec = dec.relabel(se_dics[v])

                    G = Pixtongraph(dec.gamma, dec.poly[0][0], dec.poly[0][1])
                    for j in range(G.M.ncols()):
                        if G.M[0, j] > 0:
                            G.M[0, j] = v_legs[int(G.M[0, j]) - 1]

                    stratum_nr = DR.num_of_stratum(G, gv, rv, tuple(sorted(v_legs)), moduli_type=get_moduli(moduli, DRpy=True))
                    if use_as_gens(gv, nv, rv, v_part, se_v):
                        dtad = dec_to_as(gv, nv, rv, v_part, se_v)[stratum_nr]
                        if dtad is None:
                            new_S_lists.append([])
                        else:
                            as_num, c2 = dtad
                            new_S_lists.append([(a, b * c2) for a, b in enumerate(genstobasis_as(gv, nv, rv, v_part, se_v)[as_num]) if b != 0])
                    else:
                        new_S_lists.append([(a, b) for a, b in enumerate(general_genstobasis(gv, nv, rv, v_part)[stratum_nr]) if b != 0])
                r_split2 = r_split
                for SC in itertools.product(*new_S_lists):
                    new_S = []
                    coeff = prod_coeff
                    for a, b in SC:
                        new_S.append(a)
                        coeff *= b
                    new_S = tuple(new_S)
                    if nontrivial_aut:
                        basis_vector = basismap[(r_split2, new_S)]
                    else:
                        basis_vector = vector([1 if key[0][:2] == (r_split2, new_S) else 0 for key in as_basis_iter(g, n, gamma_r, ind, r, n_part)])
                    new_basis_elem += basis_coeff * sym_sign * coeff * basis_vector

        try:
            basis_dic[tuple(new_basis_elem)].append(ind2)
        except KeyError:
            basis_dic[tuple(new_basis_elem)] = [ind2]

    new_vecs = []
    for vec in vecs:
        new_vec = vector(QQ, length)
        for basis_elem, inds in basis_dic.items():
            new_vec += sum([vec[i] for i in inds]) * vector(basis_elem)
        new_vecs.append(new_vec)
    return new_vecs, sym_ind

##############
# as basis
##############


def vertex_data_iter(gamma, r, nv_parts):
    r"""
    Yield the combinatorial data at each vertex
    The partitions of n(v) induced by the action of S_lambda on the graph are expected as inputs
    """
    num_vert = gamma.num_verts()
    rmax = [3 * gamma.genera(i) - 3 + gamma.num_legs(i) for i in range(num_vert)]
    for r_split in IntegerVectors(r, num_vert, outer=rmax):
        vertex_data = []
        for v, gv in enumerate(gamma.genera()):
            vertex_data.append((gv, gamma.num_legs(v), r_split[v], nv_parts[v], len(gamma.edges_between(v, v))))
        yield tuple(r_split), vertex_data
    return


def use_as_gens(g, n, r, n_part, self_edges):
    r"""
    Determine whether to compute the action by the wraith group or not.
    """
    if self_edges < 2:
        return False
    if (g, n, r, n_part, self_edges) in ((1, 8, 4, (2, 2, 2, 2), 4),
                                         (0, 10, 4, (2, 2, 2, 2, 2), 5), (0, 9, 4, (2, 2, 2, 2, 1), 4)):
        return True
    if 2 * r > 3 * g - 3 + n:
        return False
    return True


def prod_basis_iter(vertex_data):
    r"""
    Iterates over the product basis
    """
    S_list = []
    for v in range(len(vertex_data)):
        if use_as_gens(*vertex_data[v]):
            gen_ind = generating_indices_as(*vertex_data[v])
        else:
            gen_ind = general_generating_indices(*vertex_data[v][:-1])
        S_list.append(range(len(gen_ind)))
    for S in itertools.product(*S_list):
        yield tuple(S)
    return


def prod_basis_elem_iter(S, vertex_data, exemptions=()):
    r"""
    Converts the output of ``prod_basis_iter`` into a linear combination of decstratum classes
    """
    num_vert = len(vertex_data)
    sevs = [v for v in range(num_vert) if use_as_gens(*vertex_data[v]) and v not in exemptions]
    tgs = [tautgens_sym(*vertex_data[v][:-1]) for v in range(num_vert)]
    dec_dict = {v: tgs[v][general_generating_indices(*vertex_data[v][:-1])[S[v]]] for v in range(num_vert) if v not in sevs}
    S2_list = [antisym_gens(*vertex_data[v])[generating_indices_as(*vertex_data[v])[S[v]]] for v in sevs]
    inv_sevs = {v: i for i, v in enumerate(sevs)}
    for S2 in itertools.product(*S2_list):
        decs = []
        coeff = 1
        for v in range(num_vert):
            if v in sevs:
                nn, cc = S2[inv_sevs[v]]
                decs.append(tgs[v][nn])
                coeff *= cc
            elif v in exemptions:
                decs.append(None)
            else:
                decs.append(dec_dict[v])
        yield decs, coeff
    return


def comp_as_basis(g, n, gamma_r, n_part, ind, r):
    r"""
    computes antisymmetric basis
    r - the codimension (not counting the edges of gamma)
    """
    sym_ind = symmetrize_graph(g, n, gamma_r, ind, n_part)
    gamma = get_sym_graph_canon(g, n, gamma_r, n_part, sym_ind)
    num_vert = gamma.num_verts()
    antisym_dic = {}
    nv_parts, _, local_gs = get_vertex_symmetric_action_canon(g, n, gamma_r, ind, n_part, n_part)

    anti_aut_gamma = [(g, gamma.leg_automorphism_induce(g).inverse(), gamma.leg_automorphism_induced_edge_aut(g).sign()) for g in gamma.leg_automorphism_group()]
    num_auts = len(anti_aut_gamma)

    if num_auts == 1:
        raise ValueError("I shouldn't be computing this in this case, or compute it more simply")
    for r_split, vertex_data in vertex_data_iter(gamma, r, nv_parts):
        for S in prod_basis_iter(vertex_data):
            sym_in_basis = {}
            for L, prod_coeff in prod_basis_elem_iter(S, vertex_data):
                ptc = prodtautclass(gamma, [L])
                for gl, gvi, plusminus in anti_aut_gamma:
                    new_r_split = tuple([r_split[gvi(i)] for i in range(num_vert)])
                    new_decs = ptc.apply_action_Sn(gl, local_gs).terms[0]
                    v_data_input = [vertex_data[gvi(pre_v)] for pre_v in range(num_vert)]
                    for S2 in dec_to_basis_iter(new_decs, v_data_input):
                        coeff = QQ((plusminus, num_auts))
                        coeff *= prod_coeff
                        prod_basis_element = []
                        for i, b in S2:
                            coeff *= b
                            prod_basis_element.append(i)
                        try:
                            sym_in_basis[(new_r_split, tuple(prod_basis_element))] += coeff
                        except KeyError:
                            sym_in_basis[(new_r_split, tuple(prod_basis_element))] = coeff
                # can get rid of copies here, which would be more memory efficient than adding many of the same rows to the matrix
            antisym_dic[(r_split, S)] = sym_in_basis

    # now we calculate the basis
    matrix_dic = {}
    columns = []
    for i, sym_in_basis in enumerate(antisym_dic.values()):
        for key, coeff in sym_in_basis.items():
            try:
                j = columns.index(key)
            except ValueError:
                j = len(columns)
                columns.append(key)
            matrix_dic[(i, j)] = coeff
    M = matrix(len(antisym_dic), len(columns), matrix_dic)
    N = M.echelon_form()
    antisym_basis = []
    for row in N.rows():
        if row.is_zero():
            break
        antisym_basis.append([(columns[j][0], columns[j][1], coeff) for j, coeff in enumerate(row) if coeff != 0])
    pivots = N.pivots()
    prod_basis_to_as_basis = {}
    for prod_basis_key, row in zip(antisym_dic.keys(), M.rows()):
        prod_basis_to_as_basis[prod_basis_key] = vector(QQ, [row[i] for i in pivots])

    return antisym_basis, prod_basis_to_as_basis


def as_basis(g, n, gamma_r, ind, r, n_part=None):
    r"""
    Stores a basis for the 'antisymmetric basis'.
    With this we mean a basis for (H^r(M_\Gamma)\otimes Det(E_\Gamma))^Aut(\Gamma).
    (The 'anti' refers to the minus signs coming from the action of Aut(\Gamma) on Det(E_\Gamma) )
    """
    if n_part is None:
        n_part = (1,) * n
    with shelve.open(os.path.join(DOT_SAGE, f'admcycles/cohomology/as_bases_{g}_{n}_{gamma_r}_{r}_{n_part}'), 'r') as file:
        asb = file['asb' + str(ind)]
    return asb


def prod_to_as_basis(g, n, gamma_r, ind, r, n_part=None):
    r"""
    Stores a map from the product basis
    \sum_{r=r_1,...,r_n} \prod (S_{g_i,n_i}^r_i/P_{g_i,n_i}^r_i)^S_{n_part}
    onto the ``as_basis``
    """
    if n_part is None:
        n_part = (1,) * n
    with shelve.open(os.path.join(DOT_SAGE, f'admcycles/cohomology/as_bases_{g}_{n}_{gamma_r}_{r}_{n_part}'), 'r') as file:
        ptasb = file['ptasb' + str(ind)]
    return ptasb


def as_basis_iter(g, n, gamma_r, ind, r, n_part=None):
    r"""
    Iterates over the antisymmetric basis.
    If the action of Aut(\Gamma) is trivial it iterates over the product basis.
    """
    if n_part is None:
        n_part = (1,) * n
    sym_ind = symmetrize_graph(g, n, gamma_r, ind, n_part)
    gamma = get_sym_graph_canon(g, n, gamma_r, n_part, sym_ind)
    if len(gamma.leg_automorphism_group()) == 1:
        nv_parts = get_vertex_symmetric_action_canon(g, n, gamma_r, ind, n_part, n_part)[0]
        num_vert = gamma.num_verts()
        rmax = [3 * gamma.genera(i) - 3 + gamma.num_legs(i) for i in range(num_vert)]
        for r_split in IntegerVectors(r, num_vert, outer=rmax):
            S_list = []
            for v in range(num_vert):
                gen_ind = range(len(general_generating_indices(gamma.genera(v), gamma.num_legs(v), r_split[v], n_part=nv_parts[v])))
                S_list.append(gen_ind)
            for S in itertools.product(*S_list):
                yield ((tuple(r_split), tuple(S), 1),)
    else:
        for x in as_basis(g, n, gamma_r, ind, r, n_part):
            yield x
    return


@cached_function
def as_basis_rank(g, n, gamma_r, ind, r, n_part=None):
    r"""
    Returns the rank of the antisymmetric basis.
    If the action of Aut(\Gamma) is trivial it returns the rank of the product basis.
    """
    if n_part is None:
        n_part = (1,) * n
    sym_ind = symmetrize_graph(g, n, gamma_r, ind, n_part)
    gamma = get_sym_graph_canon(g, n, gamma_r, n_part, sym_ind)
    if len(gamma.leg_automorphism_group()) == 1:
        rank = 0
        nv_parts = get_vertex_symmetric_action_canon(g, n, gamma_r, ind, n_part, n_part)[0]
        num_vert = gamma.num_verts()
        rmax = [3 * gamma.genera(i) - 3 + gamma.num_legs(i) for i in range(num_vert)]
        for r_split in IntegerVectors(r, num_vert, outer=rmax):
            prod_rank = 1
            for v in range(num_vert):
                prod_rank *= len(general_generating_indices(gamma.genera(v), gamma.num_legs(v), r_split[v], n_part=nv_parts[v]))
            rank += prod_rank
        return rank
    if len(n_part) < n and as_basis_rank(g, n, gamma_r, ind, r) == 0:
        return 0
    with shelve.open(os.path.join(DOT_SAGE, f'admcycles/cohomology/as_bases_{g}_{n}_{gamma_r}_{r}_{n_part}'), 'r') as file:
        gr = file['gr' + str(ind)]
    return gr

####
# compute antisymmetry for a single vertex with self edges
####


@file_cache.file_cached_function(
    directory=os.path.join(DOT_SAGE, "admcycles/cohomology/as_gens"),
    key=file_cache.ignore_args_key([]),
    filename=file_cache.ignore_args_filename())
def antisym_gens(g, n, r, n_part, self_edges, moduli='st'):
    r"""
    Stores generators for
    (S_{g,n}^r/P_{g,n}^r)^((S_2 \wraith S_{``self_edges``}) \otimes (S_{``n_part``}/S_2^{``self_edges``}))
    """
    raise ValueError('not in cache')


@file_cache.file_cached_function(
    directory=os.path.join(DOT_SAGE, "admcycles/cohomology/as_gens"),
    key=file_cache.ignore_args_key([]),
    filename=file_cache.ignore_args_filename())
def dec_to_as(g, n, r, n_part, self_edges, moduli='st'):
    r"""
    Stores how to map an element of (S_{g,n}^r/P_{g,n}^r)^S_{``n_part``} to the generators from ``antisym_gens``
    """
    raise ValueError('not in cache')


def compute_as_gens(g, n, r, n_part, self_edges, moduli='st', force_recompute=False):
    r"""
    Computes the results for ``antisym_gens`` and ``dec_to_as`` and stores the results in those functions.
    """
    count = 0
    n_part2 = []
    for p in n_part:
        if count < self_edges and p == 2:
            count += 1
            continue
        n_part2.append(p)

    g2 = g + self_edges
    n2 = n - 2 * self_edges

    if force_recompute or not (antisym_gens.file_exists(g, n, r, n_part, self_edges, moduli) and dec_to_as.file_exists(g, n, r, n_part, self_edges, moduli)):
        as_gens, dtas = as_generators(g2, n2, self_edges, n_part2, r, moduli)
        antisym_gens.set_cache(as_gens, g, n, r, n_part, self_edges, moduli)
        dec_to_as.set_cache(dtas, g, n, r, n_part, self_edges, moduli)
    return


def as_generators(g, n, gamma_r, n_part, r, moduli='st'):
    r"""
    Computes the results for ``antisym_gens`` and ``dec_to_as``
    """
    ind = 0
    sym_ind = symmetrize_graph(g, n, gamma_r, ind, n_part)
    gamma = get_sym_graph_canon(g, n, gamma_r, n_part, sym_ind)
    nv_parts, _, local_gs = get_vertex_symmetric_action_canon(g, n, gamma_r, ind, n_part, n_part)

    anti_aut_gamma = [(g, gamma.leg_automorphism_induce(g).inverse(), gamma.leg_automorphism_induced_edge_aut(g).sign()) for g in gamma.leg_automorphism_group_no_self_edge_auto()]
    num_auts = len(anti_aut_gamma)
    moduli_DR = get_moduli(moduli, DRpy=True)

    if num_auts == 1:
        raise ValueError("I shouldn't be computing this in this case, or compute it more simply")

    gv = g - gamma_r
    nv = n + 2 * gamma_r
    nv_part = tuple(sorted([2] * gamma_r + list(n_part), reverse=True))
    markings = get_marks_part(nv, nv_part)

    dec_to_as = [None] * len(DR.all_strata(gv, r, markings))
    antisym_gens = []

    # could just enumerate over all_strata and convert locally
    for i, dec in enumerate(tautgens_sym(gv, nv, r, nv_part)):
        if not dec_to_as[i] is None:
            continue
        ptc = prodtautclass(gamma, [[dec]])
        sym_in_gens = {}
        for gl, gvi, plusminus in anti_aut_gamma:
            newdec = ptc.apply_action_Sn(gl, local_gs).terms[0][0]
            dec_num = DR.num_of_stratum(Pixtongraph(newdec.gamma, newdec.poly[0][0], newdec.poly[0][1], n_part=nv_part), gv, r, markings, moduli_type=moduli_DR)
            coeff = QQ((plusminus, num_auts))
            try:
                sym_in_gens[dec_num] += coeff
            except KeyError:
                sym_in_gens[dec_num] = coeff

        as_gen = [x for x in sym_in_gens.items() if x[1] != 0]
        if not as_gen:
            continue
        for dn, c in as_gen:
            dec_to_as[dn] = (len(antisym_gens), (-1) ** (c < 0))
        antisym_gens.append(tuple(as_gen))

    return tuple(antisym_gens), tuple(dec_to_as)


@file_cache.file_cached_function(
    directory=os.path.join(DOT_SAGE, "admcycles/cohomology/as_gens"),
    env_var="ADMCYCLES_CACHE_DIR",
    key=file_cache.ignore_args_key([]),
    filename=file_cache.ignore_args_filename())
def generating_indices_as(g, n, r, n_part, self_edges, moduli='st'):
    r"""
    Stores indices of ``antisym_gens`` that form a basis.
    """
    if sorted(n_part, reverse=True) != list(n_part):
        raise ValueError('wrong n_part order')
    raise ValueError(f'not in cache for g={g}, n={n}, r={r}, n_part={n_part}, self_edges={self_edges}, moduli={moduli}')


@file_cache.file_cached_function(
    directory=os.path.join(DOT_SAGE, "admcycles/cohomology/as_gens"),
    env_var="ADMCYCLES_CACHE_DIR",
    pickle_wrappers=(file_cache.rational_vectors_to_py, file_cache.py_to_rational_vectors))
def genstobasis_as(g, n, r, n_part, self_edges, moduli='st'):
    r"""
    Stores a map from the generators in ``antisym_gens`` to the basis given by ``generating_indices_as``.
    """
    if sorted(n_part, reverse=True) != list(n_part):
        raise ValueError('wrong n_part order')
    raise ValueError(f'not in cache for g={g}, n={n}, r={r}, n_part={n_part}, self_edges={self_edges}, moduli={moduli}')


def generating_indices_in_cache(g, n, r, n_part, self_edges=0, moduli='st', as_only=False):
    r"""
    Returns whether a basis has been computed.
    The output is a boolean
    """
    if as_only or use_as_gens(g, n, r, n_part, self_edges):
        return genstobasis_as.file_exists(g, n, r, n_part, self_edges)
    if len(n_part) == n:
        return genstobasis.file_exists(g, n, r, moduli)
    return genstobasis_Sn.file_exists(g, n, r, n_part, moduli)
