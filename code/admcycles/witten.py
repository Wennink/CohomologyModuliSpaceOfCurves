r"""
Code for computations involving Witten's r-spin class.
Authors: Felix Janda (main author), Aaron Pixton (code improvements), Johannes Schmitt (integration into admcycles)
"""


from collections.abc import Iterable
import itertools
import numbers

from admcycles.admcycles import tautclass
from admcycles.DR import X, MODULI_ST, MODULI_RT, MODULI_CT, MODULI_SM, single_stratum, autom_count, interpolate, num_strata, convert_vector_to_monomial_basis

from admcycles import TautologicalRing

# from sage.combinat.subset import Subsets
from sage.arith.all import factorial, lcm
from sage.functions.other import ceil
from sage.rings.all import PolynomialRing, QQ, ZZ
from sage.modules.free_module_element import vector
# from sage.rings.polynomial.polynomial_ring import polygen
from sage.rings.polynomial.multi_polynomial_element import MPolynomial
from sage.rings.integer import Integer
from sage.calculus.var import var
from sage.misc.functional import symbolic_sum
from sage.symbolic.ring import SR
from copy import copy
from sage.misc.cachefunc import cached_function

# Computation of Witten's rspin class for large r


def rspin_leg_factor(d, a):
    if a < 0:
        a = X + a
    return Pmpolynomial(d).subs(a=a)


def rspin_edge_factor(w1, m, d1, d2):
    R = PolynomialRing(QQ, 1, 'X')
    X = R.gens()[0]
    d = d1 + d2 + 1
    S = 0
    for i in range(d + 1):
        S += R(rspin_leg_factor(i, (w1 + i) % (m - 1))(X=m) *
               rspin_leg_factor(d - i, (m - 2 - i - w1) % (m - 1))(X=m) * X**i)
    S /= X + 1
    assert S.denominator() == 1
    S = S.numerator()
    # print(-S[d1])
    return -S[d1]


def rspin_coeff_setup(num, g, r, n=0, dvector=(), moduli_type=MODULI_ST):
    markings = tuple(range(1, n + 1))
    G = single_stratum(num, g, r, markings, moduli_type)
    nr = G.M.nrows()
    nc = G.M.ncols()
    edge_list = []
    exp_list = []
    scalar_factor = 1 / autom_count(num, g, r, markings, moduli_type)
    given_weights = [1 - G.M[i + 1, 0][0] for i in range(nr - 1)]
    for i in range(1, nr):
        for j in range(1, G.M[i, 0].degree() + 1):
            scalar_factor /= factorial(G.M[i, 0][j])
            scalar_factor *= (-1)**G.M[i, 0][j]
            scalar_factor *= (rspin_leg_factor(j, 0))**(G.M[i, 0][j])
            given_weights[i - 1] -= j * G.M[i, 0][j]
    for j in range(1, nc):
        ilist = [i for i in range(1, nr) if G.M[i, j] != 0]
        if G.M[0, j] == 0:
            if len(ilist) == 1:
                i1 = ilist[0]
                i2 = ilist[0]
                exp1 = G.M[i1, j][1]
                exp2 = G.M[i1, j][2]
            else:
                i1 = ilist[0]
                i2 = ilist[1]
                exp1 = G.M[i1, j][1]
                exp2 = G.M[i2, j][1]
            edge_list.append([i1 - 1, i2 - 1])
            exp_list.append(exp1)
            exp_list.append(exp2)
        else:
            exp1 = G.M[ilist[0], j][1]
            scalar_factor *= rspin_leg_factor(exp1, dvector[G.M[0, j][0] - 1])
            given_weights[ilist[0] - 1] += dvector[G.M[0, j][0] - 1] - exp1
    return edge_list, exp_list, given_weights, scalar_factor


def rspin_coeff(num, g, r, n=0, dvector=(), r_coeff=None, step=1,
                m0given=-1, deggiven=-1, moduli_type=MODULI_ST):
    markings = tuple(range(1, n + 1))
    G = single_stratum(num, g, r, markings, moduli_type)
    nr = G.M.nrows()
    nc = G.M.ncols()
    edge_list, exp_list, given_weights, scalar_factor = rspin_coeff_setup(
        num, g, r, n, dvector, moduli_type)
    if m0given == -1:
        m0 = (ceil(sum([abs(i.subs(X=0))
              for i in dvector]) / 2) + g * 1 + 1) * step
    else:
        m0 = m0given
    h0 = nc - nr - n + 1
    if deggiven == -1:
        deg = 2 * sum(exp_list) + 2 * len(edge_list)
    else:
        deg = deggiven
    if r_coeff is None:
        mrange = list(range(m0 + step, m0 + step * deg + step + 1, step))
    else:
        mrange = [r_coeff]  # just evaluate at a single value m = r_coeff
    mvalues = []
    for m in mrange:
        given_weights_m = [ZZ(i.subs(X=m)) for i in given_weights]
        total = 0
        for weight_data in itertools.product(
                *[list(range(m - 1)) for i in range(len(edge_list))]):
            vertex_weights = copy(given_weights_m)
            for i, edge_i in enumerate(edge_list):
                vertex_weights[edge_i[0]] += weight_data[i]
                vertex_weights[edge_i[1]] -= weight_data[i] + \
                    2 + exp_list[2 * i] + exp_list[2 * i + 1]
            if any(i % (m - 1) for i in vertex_weights):
                continue
            term = 1
            for i in range(len(edge_list)):
                term *= rspin_edge_factor(weight_data[i],
                                          m, exp_list[2 * i], exp_list[2 * i + 1])
            total += term
        if r_coeff is None:
            mvalues.append(total * ZZ(m - 1)**(-h0))
        else:
            # print(m-1)
            # undo the rescaling by r**degree
            mvalues.append(ZZ(-1)**(r - g) * total * ZZ(m - 1)
                           ** (-r + g - h0) * ZZ(m)**(-r))
    # print(mrange,mvalues, scalar_factor, r, h0)
    mpoly = ZZ(-1)**(r - g) * (interpolate(mrange, mvalues).subs(x=X)
                               * scalar_factor).simplify_rational()
    if r_coeff is not None:
        mpoly = QQ(mpoly.subs(X=r_coeff))
    return mpoly


def rspin_compute(g, r, n=0, dvector=(), r_coeff=None,
                  step=1, m0=-1, deg=-1, moduli_type=MODULI_ST):
    answer = []
    markings = tuple(range(1, n + 1))
    for i in range(num_strata(g, r, markings, moduli_type)):
        answer.append(rspin_coeff(i, g, r, n, dvector,
                      r_coeff, step, m0, deg, moduli_type))
    return vector(answer)


def rspin_degree_test(g, r, n=0, dvector=(), step=1,
                      m0=-1, deg=-1, moduli_type=MODULI_ST):
    answer = []
    markings = tuple(range(1, n + 1))
    for i in range(num_strata(g, r, markings, moduli_type)):
        answer.append(rspin_coeff(i, g, r, n, dvector,
                      step, m0, deg, moduli_type).degree(X))
    return answer


def rspin_constant(g, r, n=0, dvector=(), step=1, m0=-
                   1, deg=-1, moduli_type=MODULI_ST):
    answer = []
    markings = tuple(range(1, n + 1))
    for i in range(num_strata(g, r, markings, moduli_type)):
        answer.append(rspin_coeff(i, g, r, n, dvector,
                      step, m0, deg, moduli_type).subs(X=0))
    return vector(answer)


def Wittenrspin(g, Avector, r_coeff=None, d=None, rpoly=False, moduli='st'):
    r"""
    Returns the polynomial limit of Witten's r-spin class in genus g with input Avector,
    as discussed in the appendix of [Pandharipande-Pixton-Zvonkine '16].

    More precisely, Avector is expected to be a vector of linear polynomials in QQ[r],
    with leading coefficients being rational numbers in the interval [0,1] and constant
    coefficients being integers. Elements of Avector should sum to C * r + 2g-2 for some
    nonnegative integer C. Then Wittenrspin returns the tautological class obtained as
    the limit of

    r^(g-1+C) W_{g,n}^r(Avector)

    for r >> 0 sufficiently large and divisible, evaluated at r=0.

    INPUT:

    - ``g`` -- integer; underlying genus

    - ``Avector``   -- tuple ; a tuple of either integers, elements of a polynomial
      ring QQ[r] in some variable r or tuples (C_i, D_i) which are interpreted as
      polynomials C_i * r + D_i. For the entries with C_i = 1 we assume D_i <=-2.

    - ``r_coeff``  -- integer or None (default: `None`); if a particular integer
      r_coeff = r is specified, the function will return the (unscaled) class W_{g,n}^r(Avector),
      not taking a limit for large r.

    - ``d`` -- integer; desired degree in tautological ring; will be set to g-1+C by
      default

    - ``rpoly``  -- bool (default: `False`); if True, return the limit of
      r^(g-1+C) W_{g,n}^r(Avector) without evaluating at r=0, as a tautclass with
      coefficients being polynomials in r

    EXAMPLES:

    We start by verifying the conjecture from the appendix of [Pandharipande-Pixton-Zvonkine '16]
    for g = 2 and mu = (2)::

      sage: from admcycles import Wittenrspin, Strataclass
      sage: H1 = Wittenrspin(2, (2,))
      sage: H2 = Strataclass(2, 1, (2,))
      sage: (H1-H2).is_zero()
      True

    We can also verify a new conjecture for classes of strata of meromorphic differentials for
    g = 1 and mu = (3,-1,-2). The argument (1/2,-1) stands for an insertion 1/2 * r -1::

      sage: H1 = Wittenrspin(1, (3, (1/2,-1), (1/2,-2)))
      sage: H2 = Strataclass(1, 1, (3,-1,-2))
      sage: (H1+H2).is_zero()
      True

    As a variant of this, we also verify that insertions r-b stand for poles of order b with
    vanishing residues::

      sage: R.<r> = PolynomialRing(QQ,1)
      sage: H1 = Wittenrspin(1, (5,r-2, r-3))
      sage: H2 = Strataclass(1, 1, (5,-2,-3), res_cond=(2,))
      sage: (H1+H2).is_zero()
      True

    We can also compute the (scaled) Witten's class without substituting r=0::

      sage: Wittenrspin(1,(2,r-2),rpoly=True)
      Graph :      [1] [[1, 2]] []
      Polynomial : (1/12*r^2 - 5/24*r + 1/12)*(kappa_1)_0 + (-1/12*r^2 + 29/24*r - 37/12)*psi_1 + (-1/12*r^2 + 17/24*r - 13/12)*psi_2
      <BLANKLINE>
      Graph :      [0] [[4, 5, 1, 2]] [(4, 5)]
      Polynomial : -1/48*r + 1/24
      <BLANKLINE>
      Graph :      [0, 1] [[1, 2, 4], [5]] [(4, 5)]
      Polynomial : 1/12*r^2 - 17/24*r + 13/12

    Instead of calculating the asymptotic, polynomial behaviour of Witten's class,
    we can also input a concrete value for r, using the option r_coeff. Below we
    verify the CohFT property of Witten's class, first for a separating boundary
    divisor::

      sage: from admcycles import StableGraph
      sage: A = Wittenrspin(2,(1,1),r_coeff=4)
      sage: gr = StableGraph([1,1],[[1,2,3],[4]],[(3,4)])
      sage: pb = gr.boundary_pullback(A)
      sage: vector(pb.totensorTautbasis(1)[1])
      (0, 3/4, 0, 3/4, 3/4)
      sage: B = Wittenrspin(1,(1,1,2),r_coeff=4)
      sage: B.basis_vector()
      (0, 1/4, 0, 1/4, 1/4)
      sage: C = Wittenrspin(1,(0,),r_coeff=4)
      sage: C.basis_vector()
      (3)

    Then for a nonseparating boundary divisor::

      sage: B = Wittenrspin(2,(2,),r_coeff=4)
      sage: gr = StableGraph([1],[[1,2,3]],[(2,3)])
      sage: pb = gr.boundary_pullback(B)
      sage: pb.totensorTautbasis(1)
      (0, 1/2, 1/4, 1/4, -1/4)
      sage: A1 = Wittenrspin(1,(2,1,1),r_coeff=4)
      sage: A2 = Wittenrspin(1,(2,0,2),r_coeff=4)
      sage: A3 = Wittenrspin(1,(2,2,0),r_coeff=4)
      sage: L=[t.basis_vector() for t in [A1,A2,A3]]; L
      [(0, 1/2, 0, 0, 1/4), (0, 0, 0, 1/4, -1/4), (0, 0, 1/4, 0, -1/4)]
      sage: sum(L)
      (0, 1/2, 1/4, 1/4, -1/4)


    We can also check manually, that interpolating the above results for
    large r precisely gives the output of the option rpoly=True::

      sage: from admcycles.double_ramification_cycle import interpolate
      sage: H1 = Wittenrspin(1, (3, (1/2,-1), (1/2,-2)), rpoly=True)
      sage: H1.basis_vector()
      (0, -1/4*r^2 + 5/2*r - 3, 1/4*r^2 - r, 1/4*r^2 - r - 3, -1/4*r^2 + 1/2*r + 5)
      sage: res=[]
      sage: pts = list(range(6,11,2))
      sage: for r in pts:
      ....:  res.append(r**(1-1+1)*Wittenrspin(1, (3, 1/2*r-1, 1/2*r-2),r_coeff=r).basis_vector(1))
      sage: v = vector([interpolate(pts, [a[i] for a in res],'r') for i in range(5)])
      sage: v-H1.basis_vector()
      (0, 0, 0, 0, 0)
    """
    n = len(Avector)

    if r_coeff is None:
        polyentries = [a for a in Avector if isinstance(a, MPolynomial)]
        if len(polyentries) > 0:
            R = polyentries[0].parent()
            r = R.gens()[0]
        else:
            R = PolynomialRing(QQ, 1, 'r')
            r = R.gens()[0]

        X = SR.var('X')
        AvectorX = []
        Cvector = []
        Dvector = []

        # Extract entries of Avector into a unified format (AvectorX)
        # Collect linear and constant coefficients of entries of AvectorX in
        # Cvector, Dvector
        for a in Avector:
            if isinstance(a, numbers.Integral):
                AvectorX.append(Integer(a))
                Cvector.append(QQ(0))
                Dvector.append(Integer(a))
            elif isinstance(a, MPolynomial):
                AvectorX.append(QQ(a[1]) * X + QQ(a[0]))
                Cvector.append(QQ(a[1]))
                Dvector.append(QQ(a[0]))
            elif isinstance(a, Iterable):
                AvectorX.append(QQ(a[0]) * X + QQ(a[1]))
                Cvector.append(QQ(a[0]))
                Dvector.append(QQ(a[1]))
            else:
                raise ValueError(
                    'Entries of Avector must be Integers, Polynomials or tuples (C_i, D_i)')

        # For C_i = 1, D_i = -1 we require a simple pole with vanishing residue
        # => return zero class
        if any((Cvector[i] == 1) and (Dvector[i] == -1) for i in range(n)):
            return tautclass([])

        step = lcm(c.denom() for c in Cvector)
        C = sum(Cvector)
        assert C in ZZ
        assert sum(Dvector) == 2 * g - 2
    else:
        AvectorX = [ZZ(a) for a in Avector]
        step = 0

    if d is None:
        if r_coeff is None:
            d = ZZ(g - 1 + C)
        else:
            denom = ZZ((r_coeff - 2) * (g - 1) + sum(Avector))
            if denom % r_coeff != 0:
                # Witten's class vanishes unless this congruence is satisfied
                return tautclass([])
            else:
                d = ZZ(denom / ZZ(r_coeff))
    moddict = {'sm': MODULI_SM, 'rt': MODULI_RT,
               'ct': MODULI_CT, 'st': MODULI_ST}
    modu = moddict[moduli]

    rvect = rspin_compute(g, d, n, tuple(AvectorX), r_coeff,
                          step, m0=-1, deg=-1, moduli_type=modu)
    if not rpoly:
        rvect = rvect.subs(X=0)
    rvect = convert_vector_to_monomial_basis(
        rvect, g, d, tuple(range(1, n + 1)), modu)

    if rpoly:
        rvect = vector(b.subs(X=r) for b in rvect)

    R = TautologicalRing(g, n, moduli=moduli)
    return R.from_vector(rvect, d)
    # return Tautv_to_tautclass(rvect, g, n, d, moduli=moduli)


@cached_function
def Pmpolynomial(m):
    r"""
    Returns the expression P_m(X,a) as defined in [Pandharipande-Pixton-Zvonkine '16, Section 4.5].

    TESTS::

      sage: from admcycles.witten import Pmpolynomial
      sage: Pmpolynomial(0)
      1
      sage: Pmpolynomial(1)
      -1/12*X^2 + 1/2*(X - 1)*a - 1/2*a^2 + 5/24*X - 1/12
      sage: Pmpolynomial(2)
      1/288*X^4 - 1/12*(5*X - 1)*a^3 + 1/8*a^4 + 7/288*X^3 + 1/48*(20*X^2 - 5*X - 4)*a^2 - 29/384*X^2 - 1/48*(6*X^3 + X^2 - 9*X + 2)*a + 7/288*X + 1/288
    """
    (b, X, a) = var('b,X,a')
    if m == 0:
        return 1 + 0 * X
    return (QQ(1) / 2 * symbolic_sum((2 * m * X - X - 2 * b) * Pmpolynomial(m - 1).subs(a=b - 1), b, 1, a) - QQ(1) / (4 * m * X * (X - 1)) *
            symbolic_sum((X - 1 - b) * (2 * m * X - b) * (2 * m * X - X - 2 * b) * Pmpolynomial(m - 1).subs(a=b - 1), b, 1, X - 2)).simplify_rational()
