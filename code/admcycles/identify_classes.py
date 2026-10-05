from sage.rings.rational_field import QQ
from sage.matrix.constructor import matrix, vector
from sage.matrix.special import block_matrix

import admcycles.admcycles
from .admcycles import list_strata, generating_indices, pullback_matrix


def identify_class(tautring, d, pairfunction=None, pullfunction=None,
                   kappapsifunction=None, check=False):
    r"""
    Identify a tautological class in degree d by specifying its
    intersection pairing with classes in complementary degree
    and/or its pullback under boundary gluing morphisms.

    INPUT:

    - tautring (TautologicalRing) : ring containing the class that
      is to be identified

    - d (integer): degree of the class

    - pairfunction (function, optional): function taking classes in
      complementary degree and returning the intersection product with
      the desired class

    - pullfunction (function, optional): function taking stable graphs
      with at most two vertices and returning the prodtautclass obtained
      by pulling back the desired class under the associated boundary
      gluing map

    - kappapsifunction (function, optional): function taking as arguments
      a list, dictionary and TautologicalClass (giving a polynomial in
      kappa and psi-classes) and returning the intersection product of
      the desired class with this polynomial (or None)

    - check (bool, default = False) : whether to use FZ relations to
      verify that intersection numbers/pullbacks are consistent with
      known tautological relations

    EXAMPLES::

        sage: from admcycles.identify_classes import identify_class
        sage: from admcycles import TautologicalRing
        sage: R = TautologicalRing(2, 1)
        sage: cl = 3 * R.psi(1) -2 * R.kappa(1)
        sage: def pairf(a):
        ....:     return (a * cl).evaluate()
        sage: cl2 = R.identify_class(1, pairfunction = pairf)
        sage: cl == cl2
        True
        sage: def pullf(gamma):
        ....:     return gamma.boundary_pullback(cl)
        ....:
        sage: cl3 = R.identify_class(1, pullfunction=pullf)
        sage: cl == cl3
        True

    Here is some code to reconstruct the class 42*psi_1 on Mbar_0,6 from its intersection
    numbers with psi-monomials (which have an explicit formula). Note that the associated
    function kpfun is allowed to return None if kappa-classes show up::

        sage: R = TautologicalRing(0,6)
        sage: def kpfun(kap, psi, cl):
        ....:     if kap:
        ....:         return None
        ....:     b = vector(ZZ,[psi.get(i,0) for i in range(1,7)])+vector([1,0,0,0,0,0])
        ....:     return 42*factorial(3)/prod(factorial(bi) for bi in b)
        ....:
        sage: cl4 = R.identify_class(1, kappapsifunction=kpfun)
        sage: cl4 == 42*R.psi(1)
        True

    TESTS::

        sage: R = TautologicalRing(2, 1)
        sage: def bad_pairf(a):
        ....:     return (a * cl).evaluate() if not (a - R.kappa(3)).is_empty() else 0
        sage: R.identify_class(1, pairfunction = bad_pairf, check=True)
        Traceback (most recent call last):
        ...
        ValueError: intersection numbers or pullbacks are not consistent with FZ relations
    """
    gens = tautring.basis(d)
    ngens = len(gens)
    d_dual = tautring.socle_degree() - d
    M = matrix(QQ, 0, ngens)
    v = []
    rank_sufficient = (ngens == 0)
    if pairfunction is not None and not rank_sufficient:
        if check:
            gens_dual = tautring.generators(d_dual)
        else:
            gens_dual = tautring.basis(d_dual)
        ind_dcomp = tuple(generating_indices(tautring._g, tautring._n, d))
        inters = tautring.pairing_matrix(d_dual, basis=not check, ind_dcomp=ind_dcomp)
        M = block_matrix([[M], [inters]], subdivide=False)
        v += [pairfunction(a) for a in gens_dual]
        rank_sufficient = (M.rank() == ngens)

    if pullfunction is not None and not rank_sufficient:
        moduli = tautring._moduli
        graphs = [gam for gam in list_strata(tautring._g, tautring._n, 1)
                  if not gam.vanishes(moduli)]
        if len(graphs) > 0 and graphs[0].num_verts() == 1:
            irrgraph = graphs.pop(0)
            graphs.append(irrgraph)
        for gam in graphs:
            pulls = pullback_matrix(tautring._g, tautring._n, d, bdry=gam)
            # pulls = [gam.boundary_pullback(a).totensorTautbasis(d, vecout=True)
            #          for a in gens]
            M = block_matrix([[M], [pulls]],
                             subdivide=False)
            v += list(pullfunction(gam).totensorTautbasis(d, vecout=True))
            rank_sufficient = (M.rank() == ngens)
            if rank_sufficient and not check:
                break

    if kappapsifunction is not None and not rank_sufficient:
        for kappa, psi, cl in tautring.kappa_psi_polynomials(d_dual, True):
            intnum = kappapsifunction(kappa, psi, cl)
            if intnum is not None:
                M = block_matrix(QQ, [[M], [matrix([[(c * cl).evaluate() for c in gens]])]], subdivide=False)
                v.append(intnum)
            rank_sufficient = (M.rank() == ngens)
            if rank_sufficient and not check:
                break

    if not rank_sufficient:
        raise ValueError('Intersection numbers and/or pullbacks are ' +
                         'not enough to determine this class')
    try:
        w = M.solve_right(vector(QQ, v))
    except ValueError:
        raise ValueError('intersection numbers or pullbacks are not consistent with FZ relations')
    return tautring.from_basis_vector(w, d)


def Pullback_Matrices(g, n, d, ind_list=None):
    r"""
    Compute the pullback matrices of given degree d and list of
    boundary stratum.

    INPUT:

    - ind_list (list): the list of indices of the boundary stratum,
      0 indicates the first nontrivial graph
      appearing in the generator
      list of degree d tautological classes

    EXAMPLES::

        sage: from admcycles.identify_classes import Pullback_Matrices
        sage: from admcycles import TautologicalRing
        sage: Pullback_Matrices(1, 2, 1)
        [
        [1]  [1]
        [0], [1]
        ]
    """
    L1 = admcycles.admcycles.tautgens(g, n, d)
    Listgen1 = admcycles.admcycles.generating_indices(g, n, d)
    L2 = admcycles.admcycles.tautgens(g, n, 1)

    M_list = []
    if not ind_list:
        ind_list = range(len(L2) - n - 1)

    for a in ind_list:
        b = a + n + 1
        M0 = []
        Q = None
        if b == len(L2) - 1:
            Q = list(L2[b].standard_markings()._terms)[0]
        else:
            Q = list(L2[b]._terms)[0]

        for i in Listgen1:
            T = Q.boundary_pullback(L1[i])
            M0 += [T.totensorTautbasis(d, vecout=True)]
        M = matrix(M0)
        M_list += [M]
    return M_list


def solve_perfect_pairing(g, n, d, list_evaluate):
    r"""
    Identify a tautological class in degree d by specifying
    its intersection pairing
    with classes in complementary degree.

    INPUT:

    - list_evaluate (list) : the list of intersection numbers

    - list_dual_classes (list): a list of classes of dual codimension
      one wants to compute the intersection
      (the program will complete the list
      such that one obtain a full rank matrix)

    EXAMPLES::

        sage: from admcycles.identify_classes import solve_perfect_pairing
        sage: from admcycles import TautologicalRing
        sage: R = TautologicalRing(1,3)
        sage: cl = R.psi(1) -2 * R.kappa(1)
        sage: def pairf(a):
        ....:     return (a * cl).evaluate()
        sage: cl2 = solve_perfect_pairing(1, 3, 1,
        ....: [pairf(x) for x in R.generators(2)])
        sage: cl == cl2
        True
    """
    d_dual = 3 * g - 3 + n - d
    ind = admcycles.admcycles.generating_indices(g, n, d)
    gen = admcycles.admcycles.tautgens(g, n, d)
    gen_dual = admcycles.admcycles.tautgens(g, n, d_dual)
    M_intpair = []

    for i in ind:
        intersection_vector = [(gen[i] * X).evaluate() for X in gen_dual]
        M_intpair.append(intersection_vector)
    Sol = list(matrix(M_intpair).solve_left(matrix(list_evaluate)))[0]
    output = sum(Sol[i] * gen[ind[i]] for i in range(0, len(ind)))
    return output


def solve_clutch_pullback(g, n, d, bdiv_indices, pullback_classes):
    r"""
    Identify a tautological class in degree d by specifying its pullback
    under boundary gluing morphisms.

    INPUT:

    - bdiv_indices(list) : the list of indices of boundary
      stratum(the first nontrivial graph in
      tautgen list will be indexed
      by 0) to which we will pullback
    - pullback_classes(list) : the list of pullbacks of the tautological
      class with respect to the bdiv listed

    EXAMPLES::

        sage: from admcycles.identify_classes import solve_clutch_pullback
        sage: from admcycles import TautologicalRing
        sage: R = TautologicalRing(1,3)
        sage: stgraphs = [list(x._terms)[0] for x in R.generators(1)[4:]]
        sage: cl = R.psi(1) -2 * R.kappa(1)
        sage: def pullf(gr):
        ....:     return gr.boundary_pullback(cl)
        sage: cl2 = solve_clutch_pullback(1, 3, 1, range(len(stgraphs)),
        ....: [pullf(gr) for gr in stgraphs])
        sage: cl == cl2
        True

    """

    if 2 * d > 2 * g - 2 + n:
        print(" It may not work because the codim is too large")
    ListV = [T.totensorTautbasis(d, vecout=True) for T in pullback_classes]
    ListM = Pullback_Matrices(g, n, d)
    ListM_1 = [ListM[i] for i in bdiv_indices]
    Sol = SolveMultLin(ListM_1, ListV)
    ind = admcycles.admcycles.generating_indices(g, n, d)
    gen = admcycles.admcycles.tautgens(g, n, d)
    output = sum(Sol[i] * gen[ind[i]] for i in range(len(ind)))
    return output


def SolveMultLin(ListM, ListV):

    dim = ListM[0].nrows()
    assert all(Q.nrows() == dim for Q in ListM)
    NewM = []
    NewV = []
    for Q in ListM:
        NewM += list(Q.transpose())
    NewM = matrix(NewM).transpose()
    for W in ListV:
        NewV += list(W)
    NewV = matrix([NewV])
    result = NewM.solve_left(NewV)
    L = list(result)
    Sol = vector(L[0])
    return Sol
