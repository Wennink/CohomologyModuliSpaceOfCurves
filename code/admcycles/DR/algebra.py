r"""
Multiplication in the strata algebra.
"""

import itertools

from sage.misc.cachefunc import cached_function
from sage.rings.integer_ring import ZZ
from sage.modules.free_module_element import vector

from .graph import Graph, R, X, all_strata, all_pure_strata, num_strata, single_stratum, unpurify_map, contraction_table, pure_strata_autom_count, automorphism_cosets, graph_isomorphic, num_of_stratum
from .moduli import MODULI_SM, MODULI_CT, MODULI_ST, MODULI_SMALL, dim_form
from .utils import simplify_sparse, setparts_with_auts


def get_marks(n, symm):
    if symm == 0:
        return tuple(range(1, n + 1))
    return (1,) * symm + tuple(range(2, n - symm + 2))


@cached_function
def multiply(r1, i1, r2, i2, g, rmax, markings=(), moduli_type=MODULI_ST):
    r"""
    Return the result of the multiplication of the ``(r1, i1)``-th generator
    with the ``(r2, i2)`` one.

    The output is a list representing the coefficients with respect to the
    generators in rank ``r1+r2``.

    EXAMPLES::

        sage: from admcycles.DR.graph import num_strata
        sage: from admcycles.DR.algebra import multiply
        sage: r1 = 1
        sage: r2 = 2
        sage: for i1 in range(num_strata(2, r1)):
        ....:     for i2 in range(num_strata(2, r2)):
        ....:         print(i1, i2, multiply(r1, i1, r2, i2, 2, r1 + r2))
        0 0 [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        0 1 [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        0 2 [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        0 3 [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        0 4 [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        0 5 [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
        0 6 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
        0 7 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
        1 0 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        1 1 [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        1 2 [0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        1 3 [0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        1 4 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0]
        1 5 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        1 6 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0]
        1 7 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0]
        2 0 [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        2 1 [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        2 2 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
        2 3 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
        2 4 [0, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0, 1, 0, 0, 0]
        2 5 [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, -2, 0, 0, 0, 1, 0, 0]
        2 6 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
        2 7 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8, 0, 4]
    """
    unpurify = unpurify_map(g, r1 + r2, markings, moduli_type)
    gens = all_strata(g, r1 + r2, markings, moduli_type)
    ngens = num_strata(g, r1 + r2, markings, moduli_type)
    answer = [0 for i in range(ngens)]
    pure_strata = [all_pure_strata(g, r, markings, moduli_type)
                   for r in range(rmax + 1)]
    contraction_dict = contraction_table(g, rmax, markings, moduli_type)
    G1 = single_stratum(i1, g, r1, markings, moduli_type)
    G2 = single_stratum(i2, g, r2, markings, moduli_type)
    G1copy = Graph(G1.M)
    G2copy = Graph(G2.M)
    G1copy.purify()
    G2copy.purify()
    pure_r1 = G1copy.num_edges() - len(markings)
    pure_r2 = G2copy.num_edges() - len(markings)
    found = False
    for i in range(len(pure_strata[pure_r1])):
        if G1copy.M == pure_strata[pure_r1][i].M:
            G1_key = (pure_r1, i)
            found = True
            break
    assert found, "G1 purification failed"
    found = False
    for i in range(len(pure_strata[pure_r2])):
        if G2copy.M == pure_strata[pure_r2][i].M:
            G2_key = (pure_r2, i)
            found = True
            break
    assert found, "G2 purification failed"
    if G1_key > G2_key:
        return multiply(r2, i2, r1, i1, g, rmax, markings, moduli_type)

    if (G1_key, G2_key) not in contraction_dict:
        return answer
    for L in contraction_dict[(G1_key, G2_key)]:
        H = pure_strata[L[0][0]][L[0][1]]
        Hloops = []
        if moduli_type > MODULI_CT:
            for i in range(1, H.M.nrows()):
                for j in range(1, H.M.ncols()):
                    if H.M[i, j][0] == 2:
                        Hloops.append((i, j))
        auts = pure_strata_autom_count(
            L[0][1], g, L[0][0], markings, moduli_type)
        B = L[1]
        if len(B) == pure_r1 and len(B) == pure_r2:
            auts *= 2
        aut_cosets1 = automorphism_cosets(i1, g, r1, markings, moduli_type)
        aut_cosets2 = automorphism_cosets(i2, g, r2, markings, moduli_type)
        auts /= aut_cosets1[0] * aut_cosets2[0]
        for isom1 in aut_cosets1[1]:
            for isom2 in aut_cosets2[1]:
                Hcopy = Graph(H.M)
                vmap1 = [0 for i in range(G1.M.nrows())]
                for i in range(1, G1.M.nrows()):
                    vmap1[i] = L[2][0][L[4][0][isom1[0]
                                               [i - 1] - 1] - 1]
                emap1 = [0 for i in range(G1.M.ncols())]
                for i in range(1, G1.M.ncols()):
                    emap1[i] = L[2][1][L[4][1][isom1[1]
                                               [i - 1] - 1] - 1]
                vmap2 = [0 for i in range(G2.M.nrows())]
                for i in range(1, G2.M.nrows()):
                    vmap2[i] = L[3][0][L[5][0][isom2[0]
                                               [i - 1] - 1] - 1]
                emap2 = [0 for i in range(G2.M.ncols())]
                for i in range(1, G2.M.ncols()):
                    emap2[i] = L[3][1][L[5][1][isom2[1]
                                               [i - 1] - 1] - 1]

                psilooplist = []
                psiindexlist = []
                loop_factor = ZZ.one()
                for i in range(1, G1.M.nrows()):
                    for j in range(1, G1.M.ncols()):
                        if G1.M[i, j][0] != 0:
                            if G1.M[i, j][0] == 1:
                                if G1.M[i, j][1] != 0:
                                    jj = emap1[j]
                                    for ii in vmap1[i]:
                                        if H.M[ii, jj] != 0:
                                            Hcopy.M[ii, jj] += G1.M[i, j][1] * X
                                            break
                            elif G1.M[i, j][1] == 0:
                                loop_factor *= 2
                            else:
                                jj = emap1[j]
                                psilooplist.append([[G1.M[i, j][1], G1.M[i, j][2]], [
                                                   G1.M[i, j][2], G1.M[i, j][1]]])
                                psiindexlist.append([jj])
                                for ii in vmap1[i]:
                                    for k in range(H.M[ii, jj][0]):
                                        psiindexlist[-1].append(ii)
                for i in range(1, G2.M.nrows()):
                    for j in range(1, G2.M.ncols()):
                        if G2.M[i, j][0] != 0:
                            if G2.M[i, j][0] == 1:
                                if G2.M[i, j][1] != 0:
                                    if G2.M[i, j][0] == 1:
                                        jj = emap2[j]
                                        for ii in vmap2[i]:
                                            if H.M[ii, jj] != 0:
                                                Hcopy.M[ii,
                                                        jj] += G2.M[i, j][1] * X
                                                break
                            elif G2.M[i, j][1] == 0:
                                loop_factor *= 2
                            else:
                                jj = emap2[j]
                                psilooplist.append([[G2.M[i, j][1], G2.M[i, j][2]], [
                                                   G2.M[i, j][2], G2.M[i, j][1]]])
                                psiindexlist.append([jj])
                                for ii in vmap2[i]:
                                    for k in range(H.M[ii, jj][0]):
                                        psiindexlist[-1].append(ii)

                Klocationlist = []
                Kindexlist = []
                for i in range(1, G1.M.nrows()):
                    for r in range(1, rmax + 1):
                        for k in range(G1.M[i, 0][r]):
                            Klocationlist.append(vmap1[i])
                            Kindexlist.append(r)
                for i in range(1, G2.M.nrows()):
                    for r in range(1, rmax + 1):
                        for k in range(G2.M[i, 0][r]):
                            Klocationlist.append(vmap2[i])
                            Kindexlist.append(r)

                psilist = []
                for j in B:
                    S = [i for i in range(1, H.M.nrows()) if H.M[i, j][0] != 0]
                    if len(S) == 2:
                        psilist.append([[S[0], j], [S[1], j]])
                    else:
                        psilooplist.append([[0, 1], [1, 0]])
                        psiindexlist.append([j, S[0], S[0]])

                for psiloopvals in itertools.product(*psilooplist):
                    for Klocs in itertools.product(*Klocationlist):
                        for psilocs in itertools.product(*psilist):
                            Hcopycopy = Graph(Hcopy.M)
                            for i in range(len(psiindexlist)):
                                Hcopycopy.M[psiindexlist[i][1],
                                            psiindexlist[i][0]] += psiloopvals[i][0] * X
                                if psiindexlist[i][1] == psiindexlist[i][2]:
                                    Hcopycopy.M[psiindexlist[i][1],
                                                psiindexlist[i][0]] += psiloopvals[i][1] * X**2
                                else:
                                    Hcopycopy.M[psiindexlist[i][2],
                                                psiindexlist[i][0]] += psiloopvals[i][1] * X
                            for i in range(len(Kindexlist)):
                                Hcopycopy.M[Klocs[i],
                                            0] += X**Kindexlist[i]
                            for i in psilocs:
                                Hcopycopy.M[i[0], i[1]] += X
                            for k in Hloops:
                                if Hcopycopy.M[k][2] > Hcopycopy.M[k][1]:
                                    Hcopycopy.M[k] += (Hcopycopy.M[k]
                                                       [2] - Hcopycopy.M[k][1]) * (X - X**2)
                            Hcopycopy.compute_invariant()
                            for which_gen in unpurify[L[0]]:
                                if graph_isomorphic(Hcopycopy, gens[which_gen]):
                                    answer[which_gen] += (-1)**len(B) * \
                                        loop_factor / auts
                                    break
    return answer


def check_associativity(g, r1, r2, r3, markings=(), moduli_type=MODULI_ST):
    r"""
    Check associativity of the strata algebra.

    If it fails a :class:`ValueError` is raised.

    EXAMPLES::

        sage: from admcycles.DR.algebra import check_associativity
        sage: check_associativity(2, 1, 1, 1)
    """
    ngens1 = num_strata(g, r1, markings, moduli_type)
    ngens2 = num_strata(g, r2, markings, moduli_type)
    ngens3 = num_strata(g, r3, markings, moduli_type)
    for i1, i2, i3 in itertools.product(range(ngens1), range(ngens2), range(ngens3)):
        a = multiply(r1, i1, r2, i2, g, r1 + r2 +
                     r3, markings, moduli_type)
        answer1 = vector(
            [0 for i in range(num_strata(g, r1 + r2 + r3, markings, moduli_type))])
        for j in range(num_strata(g, r1 + r2, markings, moduli_type)):
            if a[j] == 0:
                continue
            answer1 += a[j] * vector(multiply(r1 + r2, j, r3,
                                              i3, g, r1 + r2 + r3, markings, moduli_type))
        a = multiply(r1, i1, r3, i3, g, r1 + r2 +
                     r3, markings, moduli_type)
        answer2 = vector(
            [0 for i in range(num_strata(g, r1 + r2 + r3, markings, moduli_type))])
        for j in range(num_strata(g, r1 + r3, markings, moduli_type)):
            if a[j] == 0:
                continue
            answer2 += a[j] * vector(multiply(r1 + r3, j, r2,
                                              i2, g, r1 + r2 + r3, markings, moduli_type))
        if answer1 != answer2:
            raise ValueError("i1=%s i2=%s i3=%s" % (i1, i2, i3))


@cached_function
def kappa_conversion(sigma):
    r"""
    EXAMPLES::

        sage: from admcycles.DR.algebra import kappa_conversion
        sage: kappa_conversion((1, 1, 1))
        [[3*X, 1], [X^2 + X, 3], [X^3, 2]]
    """
    answer = []
    for spart in setparts_with_auts(list(sigma)):
        coeff = spart[1]
        poly = R(0)
        for part in spart[0]:
            coeff *= ZZ(len(part) - 1).factorial()
            poly += X**sum(part)
        answer.append([poly, coeff])
    return answer


@cached_function
def kappa_conversion_inverse(sigma):
    r"""
    EXAMPLES::

        sage: from admcycles.DR.algebra import kappa_conversion_inverse
        sage: kappa_conversion_inverse((1, 1, 1))
        [[3*X, 1], [X^2 + X, -3], [X^3, 1]]
    """
    answer = []
    for spart in setparts_with_auts(list(sigma)):
        coeff = spart[1] * (-1)**(len(sigma) - len(spart[0]))
        poly = R(0)
        for part in spart[0]:
            poly += X**sum(part)
        answer.append([poly, coeff])
    return answer


@cached_function
def convert_to_monomial_basis(num, g, r, markings=(), moduli_type=MODULI_ST):
    r"""
    EXAMPLES::

        sage: from admcycles.DR.algebra import convert_to_monomial_basis

        sage: convert_to_monomial_basis(1, 2, 3, (1, 2, 3))
        [(1, 1), (0, 1)]
        sage: convert_to_monomial_basis(2, 2, 3, (1, 2, 3))
        [(2, 1), (1, 3), (0, 2)]
    """
    answer = []
    G = single_stratum(num, g, r, markings, moduli_type)
    genus_vec = []
    kappa_vec = []
    for i in range(1, G.M.nrows()):
        genus_vec.append(G.M[i, 0][0])
        kappa_vec.append([])
        for j in range(1, r + 1):
            for k in range(G.M[i, 0][j]):
                kappa_vec[-1].append(j)
        kappa_vec[-1] = kappa_conversion(tuple(kappa_vec[-1]))
    for choice in itertools.product(*kappa_vec):
        coeff = 1
        GG = Graph(G.M)
        for i in range(1, G.M.nrows()):
            GG.M[i, 0] = genus_vec[i - 1] + choice[i - 1][0]
            coeff *= choice[i - 1][1]
        answer.append((num_of_stratum(GG, g, r, markings, moduli_type), coeff))
    return answer


# NOTE: this function is not used anywhere
@cached_function
def convert_to_pushforward_basis(num, g, r, markings=(), moduli_type=MODULI_ST):
    answer = []
    G = single_stratum(num, g, r, markings, moduli_type)
    genus_vec = []
    kappa_vec = []
    for i in range(1, G.M.nrows()):
        genus_vec.append(G.M[i, 0][0])
        kappa_vec.append([])
        for j in range(1, r + 1):
            for k in range(G.M[i, 0][j]):
                kappa_vec[-1].append(j)
        kappa_vec[-1] = kappa_conversion_inverse(
            tuple(kappa_vec[-1]))
    for choice in itertools.product(*kappa_vec):
        coeff = 1
        GG = Graph(G.M)
        for i in range(1, G.M.nrows()):
            GG.M[i, 0] = genus_vec[i - 1] + choice[i - 1][0]
            coeff *= choice[i - 1][1]
        answer.append((num_of_stratum(GG, g, r, markings, moduli_type), coeff))
    return answer


def convert_vector_to_monomial_basis(vec, g, r, markings=(), moduli_type=MODULI_ST):
    r"""
    EXAMPLES::

        sage: from admcycles.DR.moduli import MODULI_SM, MODULI_RT, MODULI_CT, MODULI_ST
        sage: from admcycles.DR.algebra import convert_vector_to_monomial_basis
        sage: convert_vector_to_monomial_basis(vec=(-24504480, 1663200, -36000), g=8, r=3, markings=(), moduli_type=MODULI_SM)
        [-22913280, 1555200, -36000]
        sage: convert_vector_to_monomial_basis(vec=(0, 0, -15, 0, 15, 15, 0, 0, 0), g=2, r=2, markings=(1, 2), moduli_type=MODULI_RT)
        [0, 0, -15, 0, 15, 15, 0, 0, 0]
        sage: convert_vector_to_monomial_basis(vec=(71820, -7020, 9720, -41580, 9288, -3240, -18900, 756), g=2, r=2, markings=(1,), moduli_type=MODULI_CT)
        [64800, -7020, 9720, -41580, 9288, -3240, -18900, 756]
        sage: convert_vector_to_monomial_basis(vec=(81/2, -45/2, -45/2, -45/2, 9/2, 9/2, 9/2, -27/2, -9/4), g=1, r=1, markings=(1, 2, 3), moduli_type=MODULI_ST)
        [81/2, -45/2, -45/2, -45/2, 9/2, 9/2, 9/2, -27/2, -9/4]
    """
    l = len(vec)
    vec2 = [0 for i in range(l)]
    for i in range(l):
        if vec[i] != 0:
            for x in convert_to_monomial_basis(i, g, r, markings, moduli_type):
                vec2[x[0]] += x[1] * vec[i]
    return vec2


# NOTE: this function is not used anywhere
def convert_vector_to_pushforward_basis(vec, g, r, markings=(), moduli_type=MODULI_ST):
    l = len(vec)
    vec2 = [0 for i in range(l)]
    for i in range(l):
        if vec[i] != 0:
            for x in convert_to_pushforward_basis(i, g, r, markings, moduli_type):
                vec2[x[0]] += x[1] * vec[i]
    return vec2


# very inefficient in terms of memory, calling a cached function a lot of times
# but only once for each parameter configuration
# would be better to just loop over all_strata
def convert_to_monomial_basis_contributions(g, r, markings=(), moduli_type=MODULI_ST):
    num_st = num_strata(g, r, markings, moduli_type)
    dic = [[] for _ in range(num_st)]
    for num in range(num_st):
        for i, c in convert_to_monomial_basis(num, g, r, markings, moduli_type):
            dic[i].append((num, c))
    return dic


def kappa_multiple(vec, which_kappa, g, r, n, symm, moduli_type=MODULI_ST):
    r"""
    Return the multiplication of the sparse vector ``vec`` by a kappa-class.
    """
    vec2 = []
    for num, coeff in vec:
        for num2, coeff2 in single_kappa_multiple(num, which_kappa, g, r, n, symm, moduli_type):
            vec2.append([num2, coeff * coeff2])
    return simplify_sparse(vec2)


# TODO: why using (n, symm) rather than a tuple of markings here?
def psi_multiple(vec, which_psi, g, r, n, symm, moduli_type=MODULI_ST):
    r"""
    Return the multiplication of the sparse vector ``vec`` by a psi-class.
    """
    vec2 = []
    for num, coeff in vec:
        for num2, coeff2 in single_psi_multiple(num, which_psi, g, r, n, symm, moduli_type):
            vec2.append([num2, coeff * coeff2])
    return simplify_sparse(vec2)


# TODO: why using (n, symm) rather than a tuple of markings here?
def insertion_pullback(vec, new_mark, g, r, n, symm, moduli_type=MODULI_ST, from_small=False):
    r"""
    For a relation ``vec`` we return its pullback along the forgetfulmap that forgets a point.
    """
    vec2 = []
    for x in vec:
        for y in single_insertion_pullback(x[0], new_mark, g, r, n, symm, moduli_type, from_small):
            vec2.append([y[0], x[1] * y[1]])
    return simplify_sparse(vec2)


# TODO: why using (n, symm) rather than a tuple of markings here?
@cached_function
def single_psi_multiple(num, which_psi, g, r, n, symm, moduli_type=MODULI_ST):
    r"""
    Takes the index of a stratum ``num`` and returns the stratum in degree ``r+1``
    (as a sparse vector of length 1) corresponding to its multiplication by a psi-class.

    EXAMPLES::

        sage: from admcycles.DR.moduli import MODULI_RT, MODULI_CT, MODULI_ST
        sage: from admcycles.DR.algebra import single_psi_multiple
        sage: single_psi_multiple(5, 1, 2, 2, 2, 0, MODULI_ST)
        [(11, 1)]
    """
    markings = get_marks(n, symm)
    G = single_stratum(num, g, r, markings, moduli_type)
    answer = []
    for j in range(1, G.M.ncols()):
        if G.M[0, j] == which_psi:
            good_j = j
            break
    for i in range(1, G.M.nrows()):
        if G.M[i, good_j] != 0:
            deg = 0
            dim_used = 0
            for j in range(1, r + 1):
                dim_used += j * G.M[i, 0][j]
            for j in range(1, G.M.ncols()):
                dim_used += G.M[i, j][1] + G.M[i, j][2]
                deg += G.M[i, j][0]
            if dim_used < dim_form(G.M[i, 0][0], deg, moduli_type):
                GG = Graph(G.M)
                GG.M[i, good_j] += X
                answer.append(
                    (num_of_stratum(GG, g, r + 1, markings, moduli_type), 1))
            break
    return answer


# TODO: why using (n, symm) rather than a tuple of markings here?
@cached_function
def single_kappa_multiple(num, which_kappa, g, r, n, symm, moduli_type=MODULI_ST):
    r"""
    Takes the index of a stratum ``num`` and returns the index of its multiplication by a kappa-class.
    This uses the multi-indexed pushforward kappa-classes, rather than monomials in kappa-classes.
    """
    markings = get_marks(n, symm)
    G = single_stratum(num, g, r, markings, moduli_type)
    answer = []
    for i in range(1, G.M.nrows()):
        deg = 0
        dim_used = 0
        for j in range(1, r + 1):
            dim_used += j * G.M[i, 0][j]
        for j in range(1, G.M.ncols()):
            dim_used += G.M[i, j][1] + G.M[i, j][2]
            deg += G.M[i, j][0]
        if dim_used + which_kappa <= dim_form(G.M[i, 0][0], deg, moduli_type):
            GG = Graph(G.M)
            GG.M[i, 0] += X**which_kappa
            answer.append((num_of_stratum(GG, g, r + which_kappa,
                                          markings, moduli_type), 1))
            for j in range(1, r + 1):
                if G.M[i, 0][j] > 0:
                    GG = Graph(G.M)
                    GG.M[i, 0] += X**(j + which_kappa)
                    GG.M[i, 0] -= X**j
                    answer.append((num_of_stratum(
                        GG, g, r + which_kappa, markings, moduli_type), -G.M[i, 0][j]))
    return answer


# NOTE: this function is not used anywhere
def single_kappa_psi_multiple(num, kappa_partition, psi_exps, g, r, n=0, moduli_type=MODULI_ST):
    markings = tuple(range(1, n + 1))
    G = single_stratum(num, g, r, markings, moduli_type)
    GG = Graph(G.M)
    for j in range(1, G.M.ncols()):
        if GG.M[0, j] != 0:
            for i in range(1, G.M.nrows()):
                if GG.M[i, j] != 0:
                    GG.M[i, j] += psi_exps[GG.M[0, j][0] - 1] * X
                    break
    rnew = r + sum(kappa_partition) + sum(psi_exps)
    answer = []
    kappa_options = [list(range(1, G.M.nrows()))
                     for i in range(len(kappa_partition))]
    for kappa_distrib in itertools.product(*kappa_options):
        GGG = Graph(GG.M)
        for i in range(len(kappa_partition)):
            GGG.M[kappa_distrib[i], 0] += X**(kappa_partition[i])
        is_bad = False
        for i in range(1, GGG.M.nrows()):
            deg = 0
            dim_used = 0
            for j in range(1, rnew + 1):
                dim_used += j * GGG.M[i, 0][j]
            for j in range(1, GGG.M.ncols()):
                dim_used += GGG.M[i, j][1] + GGG.M[i, j][2]
                deg += GGG.M[i, j][0]
            if dim_used > dim_form(GGG.M[i, 0][0], deg, moduli_type):
                is_bad = True
                break
        if is_bad:
            continue
        answer.append(
            (num_of_stratum(GGG, g, rnew, markings, moduli_type), 1))
    return answer


# TODO: why using (n, symm) rather than markings here?
@cached_function
def single_insertion_pullback(num, new_mark, g, r, n, symm, moduli_type=MODULI_ST, from_small=False):
    r"""
    Takes the index of a stratum ``num`` and returns the sparse vector
    representation of its pullback along the forgetfulmap that foregets a
    point.

    EXAMPLES::

        sage: from admcycles.DR.algebra import single_insertion_pullback

        sage: single_insertion_pullback(0, 1, 5, 2, 0, 0, 1, False)
        [(0, 1), (3, -1)]
        sage: single_insertion_pullback(1, 1, 5, 2, 0, 0, 1, False)
        [(1, 1), (2, -1), (2, -1)]
        sage: single_insertion_pullback(10, 1, 2, 2, 1, 0, 3, False)
        [(25, 1), (27, -1)]
    """
    markings = get_marks(n, symm)
    if new_mark == 1:
        new_markings = get_marks(n + 1, symm + 1)
    else:
        new_markings = get_marks(n + 1, symm)
    if from_small:
        G = single_stratum(num, g, r, markings, MODULI_SMALL)
    else:
        G = single_stratum(num, g, r, markings, moduli_type)
    answer = []
    for i in range(1, G.M.nrows()):
        GG = Graph(G.M)
        if not (new_mark == 1 and symm > 0):
            for j in range(1, G.M.ncols()):
                if GG.M[0, j][0] >= new_mark:
                    GG.M[0, j] += 1
        GG.add_edge(i, 0, new_mark)
        answer.append(
            (num_of_stratum(GG, g, r, new_markings, moduli_type), 1))
        for j in range(1, r + 1):
            for k in range(GG.M[i, 0][j]):
                GGG = Graph(GG.M)
                GGG.M[i, 0] -= X**j
                GGG.M[i, -1] += j * X
                answer.append(
                    (num_of_stratum(GGG, g, r, new_markings, moduli_type), -1))
        if moduli_type <= MODULI_SM:
            continue
        for j in range(1, G.M.ncols()):
            if G.M[i, j][0] == 1:
                if G.M[i, j][1] >= 1:
                    x = G.M[i, j][1]
                    GGG = Graph(GG.M)
                    row1 = [GG.M[i, k] for k in range(GG.M.ncols())]
                    row2 = [0 for k in range(GG.M.ncols())]
                    row1[j] = 0
                    row1[-1] = 0
                    row2[j] = 1
                    row2[-1] = 1
                    GGG.split_vertex(i, row1, row2)
                    GGG.M[-2, -
                          1] += (x - 1) * X
                    answer.append(
                        (num_of_stratum(GGG, g, r, new_markings, moduli_type), -1))
            if not from_small:
                if G.M[i, j][0] == 2:
                    if G.M[i, j][1] >= 1 or G.M[i, j][2] >= 1:
                        x = G.M[i, j][1]
                        y = G.M[i, j][2]
                        row1 = [GG.M[i, k] for k in range(GG.M.ncols())]
                        row2 = [0 for k in range(GG.M.ncols())]
                        row1[j] = 0
                        row1[-1] = 0
                        row2[j] = 1
                        row2[-1] = 1
                        if y >= 1:
                            row1[j] = 1 + x * X
                            GGG = Graph(GG.M)
                            GGG.split_vertex(i, row1, row2)
                            GGG.M[-2, -
                                  1] += (y - 1) * X
                            answer.append(
                                (num_of_stratum(GGG, g, r, new_markings, moduli_type), -1))
                        if x >= 1:
                            row1[j] = 1 + y * X
                            GGG = Graph(GG.M)
                            GGG.split_vertex(i, row1, row2)
                            GGG.M[-2, -
                                  1] += (x - 1) * X
                            answer.append(
                                (num_of_stratum(GGG, g, r, new_markings, moduli_type), -1))
    return answer
