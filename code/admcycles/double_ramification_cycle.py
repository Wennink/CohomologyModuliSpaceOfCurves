# encoding: utf-8
r"""
Double ramification cycle
"""

import itertools

from admcycles.admcycles import Tautvecttobasis, tautgens
from admcycles.stable_graph import StableGraph
from .tautological_ring import TautologicalRing
from .DR import interpolate
import admcycles.DR as DR

from sage.combinat.subset import Subsets
from sage.arith.all import factorial
from sage.functions.other import floor
from sage.misc.misc_c import prod
from sage.rings.all import PolynomialRing, QQ, ZZ
from sage.modules.free_module_element import vector
from sage.rings.polynomial.multi_polynomial_element import MPolynomial
from sage.misc.cachefunc import cached_function
from sage.rings.power_series_ring import PowerSeriesRing
from sage.combinat.combinat import bernoulli_polynomial
from sage.functions.log import exp
from sage.combinat.partition import Partitions

############
#
# Old DR-cycle implementation
#
############


def DR_cycle_old(g, Avector, d=None, k=None, tautout=True, basis=False):
    r"""Returns the k-twisted Double ramification cycle in genus g and codimension d
    for the partition Avector of k*(2g-2+n).

    In the notation of [JPPZ17]_, the output is 2^(-d) * P_g^{d,k}(Avector).

    Note: This is based on the old implementation DR_compute by Pixton. A new one,
    which can be faster in many examples is DR_cycle.

    INPUT:

    - ``tautout`` -- bool (default: `True`); if False, returns a vector
      (in all generators for basis=false, in the basis of the ring for basis=true)

    - ``basis``   -- bool (default: `False`); if True, use FZ relations to give out the
      DR cycle in a basis of the tautological ring
    """
    if d is None:
        d = g
    n = len(Avector)
    R = TautologicalRing(g, n)
    if k is None:
        k = floor(sum(Avector) / (2 * g - 2 + n))
    if sum(Avector) != k * (2 * g - 2 + n):
        raise ValueError('2g-2+n must divide the sum of entries of Avector.')

    v = DR.DR_compute(g, d, n, Avector, k)
    v1 = vector([QQ(a) for a in DR.convert_vector_to_monomial_basis(v, g, d, tuple(range(1, n + 1)), DR.MODULI_ST)])

    if basis:
        v2 = Tautvecttobasis(v1, g, n, d)
        if tautout:
            return R.from_basis_vector(v2, d)
        return v2
    else:
        if tautout:
            return R.from_vector(v1, d)
        return v1


############
#
# New DR-cycle implementation
#
############

def DR_cycle(g, Avector, d=None, k=None, rpoly=False, tautout=True, basis=False, chiodo_coeff=False, r_coeff=None, moduli='st', base_ring=QQ, spin=False, r_power=None):
    r"""Returns the k-twisted Double ramification cycle in genus g and codimension d
    for the partition Avector of k*(2g-2+n). If some elements of Avector are elements of a
    polynomial ring, compute DR-polynomial and substitute the entries of Avector - the result
    then has coefficients in a polynomial ring.

    In the notation of [JPPZ17]_, the output is 2^(-d) * P_g^{d,k}(Avector).

    Note: This is a reimplementation of Pixton's DR_compute which can be faster in many examples.
    To access the old version, use DR_cycle_old - it might be faster on older SageMath-versions.

    INPUT:

    - ``rpoly``  -- bool (default: `False`); if True, return tautclass 2^(-d) * P_g^{d,r,k}(Avector)
      whose coefficients are polynomials in the variable r (for r>>0).

    - ``tautout`` -- bool (default: `True`); if False, returns a vector
      (in all generators for basis=false, in the basis of the ring for basis=true)

    - ``basis``   -- bool (default: `False`); if True, use FZ relations to give out the
      DR cycle in a basis of the tautological ring

    - ``chiodo_coeff`` -- bool (default: `False`); if True, return the formula
      r^(2d-2g+1) epsilon_* c_d(-R* pi_* \L) from [JPPZ17]_, Corollary 4, Proposition 5 instead.
      It has DR_cycle(g, Avector) as its r=0 specialization.

    - ``r_coeff`` -- integer or None (default: `None`); if an integer ``r0`` is given, return
      the class/vector 2^(-d) * P_g^{d,r0,k}(Avector) for this fixed ``r0``. This option is
      incompatible with ``rpoly = True`` or polynomial entries of ``Àvector``.
      For r0>>0 this will agree with the value of the polynomial-coefficient class from
      ``rpoly = True`` at ``r=r0`` above.

    - ``moduli`` -- string (default: `'st'`); moduli on which DR is computed

    - ``base_ring`` -- string (default: `QQ`); ring of coefficients of the DR-cycle

    - ``spin`` -- bool (default: `False`); if True, compute the spin DR-cycle, and
      the input ramification data has to be odd numbers

    - ``r_power`` -- Integer (default: `None`); if not None, return the coefficient of a
      particular power of the formal variable r

    EXAMPLES::

      sage: from admcycles import DR_cycle, DR_cycle_old
      sage: DR_cycle(1, (2, 3, -5))
      Graph :      [1] [[1, 2, 3]] []
      Polynomial : 2*psi_1 + 9/2*psi_2 + 25/2*psi_3
      <BLANKLINE>
      Graph :      [0] [[5, 6, 1, 2, 3]] [(5, 6)]
      Polynomial : -1/24
      <BLANKLINE>
      Graph :      [0, 1] [[1, 2, 5], [3, 6]] [(5, 6)]
      Polynomial : -25/2
      <BLANKLINE>
      Graph :      [0, 1] [[1, 3, 5], [2, 6]] [(5, 6)]
      Polynomial : -9/2
      <BLANKLINE>
      Graph :      [0, 1] [[2, 3, 5], [1, 6]] [(5, 6)]
      Polynomial : -2
      sage: DR_cycle(1, (2, 3, -5), moduli='ct')
      Graph :      [1] [[1, 2, 3]] []
      Polynomial : 2*psi_1 + 9/2*psi_2 + 25/2*psi_3
      <BLANKLINE>
      Graph :      [0, 1] [[1, 2, 5], [3, 6]] [(5, 6)]
      Polynomial : -25/2
      <BLANKLINE>
      Graph :      [0, 1] [[1, 3, 5], [2, 6]] [(5, 6)]
      Polynomial : -9/2
      <BLANKLINE>
      Graph :      [0, 1] [[2, 3, 5], [1, 6]] [(5, 6)]
      Polynomial : -2
      sage: DR_cycle(1, (2, 3, -5), moduli='sm')
      0

    Here we check that `P_g^{d,k}(Avector)=0` for `d>g` ([CJ18]_)::

      sage: D = DR_cycle(1, (1, 3, -4), d=2)
      sage: D2 = DR_cycle_old(1, (1, 3, -4), d=2)  # long time
      sage: D.vector() == D2.vector()              # long time
      True
      sage: D.is_zero()
      True
      sage: v = DR_cycle(2, (3,), d=4, rpoly=true).evaluate()
      sage: v  # Conjecture by Longting Wu predicts that r^1-term vanishes
      -1/1728*r^6 + 1/576*r^5 + 37/34560*r^4 - 13/6912*r^3 - 1/1152*r^2

    Using ``chiodo_coeff = True`` we can compute the more complicated formula for
    the DR_cycle appearing in the original proof in [JPPZ17]_. It should give the same
    result when ``rpoly = False``, but as a polynomial in r it will differ from the
    simplified formula::

      sage: g=2; A=(2,4,-1); d=2; k=1
      sage: v1 = DR_cycle(g,A,d,k,chiodo_coeff=True).vector()
      sage: v2 = DR_cycle(g,A,d,k,chiodo_coeff=False).vector()
      sage: v1 == v2
      True
      sage: g=1; A=(1,5); d=1; k=3
      sage: DR_cycle(g,A,d,k,rpoly=True, chiodo_coeff=True)
      Graph :      [1] [[1, 2]] []
      Polynomial : (-1/12*r^2 + 3/2*r - 9/2)*(kappa_1)_0 + (1/12*r^2 - 1/2*r + 1/2)*psi_1 + (1/12*r^2 - 5/2*r + 25/2)*psi_2
      <BLANKLINE>
      Graph :      [0] [[4, 5, 1, 2]] [(4, 5)]
      Polynomial : -1/24
      <BLANKLINE>
      Graph :      [0, 1] [[1, 2, 4], [5]] [(4, 5)]
      Polynomial : -1/12*r^2 + 3/2*r - 9/2

    Setting ``r_coeff`` to a specific value, we can compute the class
    2^(-d) * P_g^{d,r0,k}(Avector) even in the non-polynomial regime, both with
    ``chiodo_coeff`` being ``True`` or ``False``::

      sage: g=2; A=(5,-1); d=2; k=1
      sage: D2 = DR_cycle(g,A,tautout=False,r_coeff=7)
      sage: D7 = DR_cycle(g,A,tautout=False,r_coeff=7)
      sage: Dr = DR_cycle(g,A,tautout=False,rpoly=True)
      sage: r = Dr.parent().base().gens()[0]  # extract coefficient variable r
      sage: Dr.subs({r:2}) == D2  # r=2 not in polynomial regime
      False
      sage: Dr.subs({r:7}) == D7  # r=7 is in polynomial regime
      True

    We can create a polynomial ring and use an Avector with entries in this ring.
    The result is a tautological class with polynomial coefficients::

      sage: R.<a1,a2>=PolynomialRing(QQ,2)
      sage: Q=DR_cycle(1,(a1,a2,-a1-a2))
      sage: Q
      Graph :      [1] [[1, 2, 3]] []
      Polynomial : 1/2*a1^2*psi_1 + 1/2*a2^2*psi_2 + (1/2*a1^2 + a1*a2 + 1/2*a2^2)*psi_3
      <BLANKLINE>
      Graph :      [0] [[5, 6, 1, 2, 3]] [(5, 6)]
      Polynomial : -1/24
      <BLANKLINE>
      Graph :      [0, 1] [[1, 2, 5], [3, 6]] [(5, 6)]
      Polynomial : -1/2*a1^2 - a1*a2 - 1/2*a2^2
      <BLANKLINE>
      Graph :      [0, 1] [[1, 3, 5], [2, 6]] [(5, 6)]
      Polynomial : -1/2*a2^2
      <BLANKLINE>
      Graph :      [0, 1] [[2, 3, 5], [1, 6]] [(5, 6)]
      Polynomial : -1/2*a1^2

    We can compute the spin DR cycle as constructed in [Costantini-Sauvaget-Schmitt-21]::

      sage: spinDR=DR_cycle(2,(9,-3,-1),spin=True)
      sage: spinDR.basis_vector()
      (-367, 122, -117, -372, -319, 28, 405, 268, 841, 397, 709, 427, -600, -923, 216, -422, -388, 285, -370, -612, 850, 364, -850, 243/2, 16, -227/2, -243/2, -122, -49, 89/2, 168, 26, -125/2, -48, 10, -45/2, 76, 24, -35/2, 79, -207/2, -31, -90, 195/2)

    We can compute the spin DR as a polynomial::

      sage: R.<a>=PolynomialRing(QQ,1)
      sage: DR_cycle(1,(2*a+1,-2*a+1),spin=True)
      Graph :      [1] [[1, 2]] []
      Polynomial : -1/4*(kappa_1)_0 + (a^2 + a + 1/4)*psi_1 + (a^2 - a + 1/4)*psi_2
      <BLANKLINE>
      Graph :      [0] [[4, 5, 1, 2]] [(4, 5)]
      Polynomial : 1/24
      <BLANKLINE>
      Graph :      [0, 1] [[1, 2, 4], [5]] [(4, 5)]
      Polynomial : -1/4

    This can be used to check Theorem 1.4 in [CSS21]_ for g=2, n=2::

        sage: g=2; n=2
        sage: from admcycles import psiclass
        sage: T = PolynomialRing(QQ,n,'a')
        sage: avec = T.gens()
        sage: k = sum(avec)/(2*g-2+n)
        sage: R.<z> = PowerSeriesRing(T, default_prec = 2*g+10)
        sage: cosh = 1/2*(exp(z)+exp(-z))
        sage: sinh = 1/2*(exp(z)-exp(-z))
        sage: S = sinh(z/2)/(z/2)
        sage: Sprime = S.derivative()
        sage: helpfun = exp(avec[0]*z*Sprime(k*z)/S(k*z))*cosh(z/2)/S(z)*prod(S(avec[i]*z) for i in range(1,n))/S(k*z)**(2*g+n-1)
        sage: 2**(-g)*helpfun[2*g]
        23/5898240*a0^4 - 29/1474560*a0^3*a1 + 157/2949120*a0^2*a1^2 - 53/1474560*a0*a1^3 + 103/5898240*a1^4 + 1/6144*a0^2 - 1/9216*a0*a1 + 11/18432*a1^2 - 1/2880
        sage: a0, a1 = T.gens()
        sage: (DR_cycle(g,(a0, a1), chiodo_coeff=True, spin=True)*psiclass(1,2,2)^(2*g-3+n)).evaluate()
        23/5898240*a0^4 - 29/1474560*a0^3*a1 + 157/2949120*a0^2*a1^2 - 53/1474560*a0*a1^3 + 103/5898240*a1^4 + 1/6144*a0^2 - 1/9216*a0*a1 + 11/18432*a1^2 - 1/2880

    TESTS::

      sage: from admcycles import DR_cycle, DR_cycle_old
      sage: D = DR_cycle(2, (3, 4, -2), k=1)       # long time
      sage: D2 = DR_cycle_old(2, (3, 4, -2), k=1)  # long time
      sage: D.vector() == D2.vector()              # long time
      True
      sage: D = DR_cycle(2, (1, 4, 5), k=2)        # long time
      sage: D2 = DR_cycle_old(2, (1, 4, 5), k=2)   # long time
      sage: D.vector() == D2.vector()              # long time
      True
      sage: D = DR_cycle(3, (2,4), k=1)            # long time
      sage: D2 = DR_cycle_old(3, (2,4), k=1)       # long time
      sage: D.vector() == D2.vector()              # long time
      True

      sage: D = DR_cycle(2, (3,),tautout=False); D
      (0, 1/8, -9/4, 81/8, 1/4, -9/4, -1/8, 1/8, 1/4, -1/8, 1/48, 1/240, -3/16, -41/240, 1/48, 1/48, 1/1152)
      sage: D2=DR_cycle_old(2, (3,), tautout=False); D2
      (0, 1/8, -9/4, 81/8, 1/4, -9/4, -1/8, 1/8, 1/4, -1/8, 1/48, 1/240, -3/16, -41/240, 1/48, 1/48, 1/1152)
      sage: D3 = DR_cycle(2, (3,), tautout=False, basis=True); D3
      (-5, 2, -8, 18, 3/2)
      sage: D4 = DR_cycle_old(2, (3,), tautout=False, basis=True); D4
      (-5, 2, -8, 18, 3/2)

      sage: g=3; A=(5,8,1); d=1; k=2
      sage: D1 = DR_cycle(g,A,d,k,chiodo_coeff=True)
      sage: D2 = DR_cycle(g,A,d,k,chiodo_coeff=False)
      sage: D1.vector() == D2.vector()
      True

      sage: g=2; A=(6,); d=2; k=2
      sage: D8 = DR_cycle(g,A,tautout=False,chiodo_coeff=True,r_coeff=8)
      sage: Dr = DR_cycle(g,A,tautout=False,chiodo_coeff=True,rpoly=True)
      sage: r = Dr.parent().base().gens()[0]  # extract coefficient variable r
      sage: Dr.subs({r:8}) == D8
      True

    """
    if d is None:
        d = g
    n = len(Avector)

    if any(isinstance(ai, MPolynomial) for ai in Avector):
        # compute DRpoly and substitute the ai in there
        Avector = vector(Avector)
        BR = Avector.parent().base_ring()
        pol, gens = DRpoly(g, d, n, tautout=False, basis=basis, gensout=True,
                           chiodo_coeff=chiodo_coeff, moduli=moduli, spin=spin)
        subsdict = {gens[i]: Avector[i] for i in range(n)}
        pol = pol.apply_map(lambda x: x.subs(subsdict))

        if tautout:
            R = TautologicalRing(g, n, moduli=moduli, base_ring=BR)
            return R.from_vector(pol, d)
        return pol

    if spin:
        if any(x % 2 != 1 for x in Avector):
            raise ValueError('The ramification data is not of spin type.')

    Asum = sum(Avector)

    if r_coeff is None:
        if Asum % (2 * g - 2 + n) != 0:
            raise ValueError('2g-2+n must divide the sum of entries of Avector.')
        if k is None:
            k = floor(Asum / (2 * g - 2 + n))
        if sum(Avector) != k * (2 * g - 2 + n):
            raise ValueError('The entries of Avector must sum to k*(2g-2+n).')
    else:
        if k is None:
            if Asum % (2 * g - 2 + n) == 0:
                k = floor(Asum / (2 * g - 2 + n))  # we are guessing that this is the right k, but only unique mod r
            else:
                raise ValueError('If a value of r_coeff is specified, the parameter k must be specified.')
        if sum(Avector) % r_coeff != k * (2 * g - 2 + n) % r_coeff:
            raise ValueError('The entries of Avector must sum to k*(2g-2+n) mod r_coeff.')
    if spin and k % 2 != 1:
        raise ValueError('The integer k has to be odd for spin DR.')

    R = TautologicalRing(g, n, moduli, base_ring=base_ring)
    gens = tautgens(g, n, d, decst=True, moduli=moduli)

    v = vector([DR_coeff_new(decs, g, n, d, Avector, k, rpoly, chiodo_coeff, r_coeff, spin=spin, r_power=r_power) for decs in gens])

    if not chiodo_coeff:
        v *= 1 / ZZ(2)**d
    # v1=vector([QQ(a) for a in DR.convert_vector_to_monomial_basis(v,g,d,tuple(range(1, n+1)),DR.MODULI_ST)])

    if basis:
        v1 = Tautvecttobasis(v, g, n, d)
        if tautout:
            return R.from_basis_vector(v1, d)
        return v1
    else:
        if tautout:
            return R.from_vector(v, d)
        return v


def DR_coeff_setup(G, g, n, d, Avector, k, chiodo_coeff):
    gamma = G.gamma
    kappa, psi = G.poly.monom[0]
    exp_list = []
    exp_list_fine = []
    if chiodo_coeff:
        R = PolynomialRing(QQ, 'x,r', 2)
        x, r = R.gens()
        scalar_factor = R.one() / G.automorphism_number()
    else:
        scalar_factor = QQ((1, G.automorphism_number()))
    given_weights = [-k * (2 * gv - 2 + len(gamma._legs[i]))
                     for i, gv in enumerate(gamma._genera)]

    # contributions to scalar_factor from kappa-classes
    for v in range(gamma.num_verts()):
        if chiodo_coeff:
            scalar_factor *= prod(((-1)**(m + 1) * bernoulli_polynomial(x, m + 2)(k / r, r) /
                                  (m + 1) / (m + 2))**ex / factorial(ex) for m, ex in enumerate(kappa[v]))
        else:
            if len(kappa[v]) == 1:  # some kappa_1^e at this vertex
                scalar_factor *= (-k**2)**(kappa[v][0]) / factorial(kappa[v][0])

    # contributions to scalar_factor and given_weights from markings
    for i in range(1, n + 1):
        v = gamma.vertex(i)
        psipow = psi.get(i, 0)  # if i in dictionary, have psi_i^(psi[i]), otherwise have psi_i^0
        given_weights[v] += Avector[i - 1]
        if chiodo_coeff:
            sfcontrib = QQ(0)
            for par in Partitions(psipow):
                parexp = par.to_exp()  # list [1,0,4] corresponds to psi^1 * (psi^3)^4
                sfcontrib += prod(((-1)**m * bernoulli_polynomial(x, m + 2)
                                  (Avector[i - 1] / r, r) / (m + 1) / (m + 2))**ex / factorial(ex) for m, ex in enumerate(parexp))
            scalar_factor *= sfcontrib
        else:
            scalar_factor *= (Avector[i - 1])**(2 * psipow) / factorial(psipow)

    # contributions to scalar_factor and explist from edges
    for (lu, lv) in gamma._edges:
        psipowu = psi.get(lu, 0)
        psipowv = psi.get(lv, 0)
        exp_list.append(psipowu + psipowv + 1)
        exp_list_fine.append([psipowu, psipowv])
        if chiodo_coeff:
            pass  # formula is more complicated, take care of entire edge term below
        else:
            scalar_factor *= ((-1)**(psipowu + psipowv)) / factorial(psipowv) / \
                factorial(psipowu) / (psipowu + psipowv + 1)

    return exp_list, given_weights, scalar_factor, exp_list_fine


def DR_coeff_new(G, g, n, d, Avector, k=0, rpoly=False, chiodo_coeff=False, r_coeff=None, directweights=False, spin=False, r_power=None):
    r"""
    Computes the coefficient of the decorated stratum G in the DR-cycle.

    For directweights= True, assume that G is a (pre)stable graph, and
    Avector = exp_list, given_weights, where

      * exp_list = [c for each edge decorated with (-psi -psi')^(c-1)]
      * given_weights = [weight(v) for v in gamma.vertices()]

    and computes the (r=0)-coefficient of x^exp_list in the expression

    r^(-h^1(G))/Aut(G) \sum_w \prod_{e in E(Gamma)} exp(w(h) w(h')/2 * x_e).

    EXAMPLES::

        sage: from admcycles.double_ramification_cycle import DR_coeff_new
        sage: from admcycles import StableGraph
        sage: gamma = StableGraph([0],[[1,2,3]],[(2,3)])
        sage: DR_coeff_new(gamma,1,1,1,([1],[0]), directweights=True)
        -1/24
        sage: DR_coeff_new(gamma,1,1,1,([2],[0]), directweights=True)
        -1/480
        sage: gamma = StableGraph([0,0],[[1],[2]],[(1,2)])
        sage: DR_coeff_new(gamma,0,0,1,([1],[7,-7]), directweights=True)
        -49/4
        sage: DR_coeff_new(gamma,0,0,0,([0],[7,-7]), directweights=True)
        1/2

    TESTS:

    Check that https://gitlab.com/modulispaces/admcycles/-/issues/124 is
    solved::

        sage: from admcycles.admcycles import decstratum
        sage: gamma = StableGraph([0, 1, 1], [[1, 2, 8], [4, 5, 9, 10], [3, 11]], [(8, 9), (10, 11)])
        sage: G = decstratum(gamma)
        sage: k, A = (-5, [-50, -50, 0, 0, 65])
        sage: DR_coeff_new(G, 2, 5, 2, A,k,False,False,None)
        902500
        sage: (k-A[0]-A[1])^2 * (2*k-A[2])^2
        902500
    """
    if directweights:
        gamma = G
        exp_list, given_weights = Avector
        m0 = sum(abs(c) for c in given_weights)  # TODO: can probably be improved
        scalar_factor = ZZ(1) / gamma.automorphism_number() / prod(factorial(c) for c in exp_list) * ZZ(2)**(-sum(exp_list))
        exp_list_fine = None

    else:
        gamma = G.gamma  # underlying stable graph of decstratum G
        kappa, _ = G.poly.monom[0]
        # kappa is a list of length = # vertices, of entries like [3,0,2] meaning that at this vertex there is a kappa_1^3 * kappa_3^2
        # _ = psi is a dictionary and psi[3]=4 means there is a decoration psi^4 at marking/half-edge 3

        if not chiodo_coeff and any(len(kalist) > 1 for kalist in kappa):
            return 0  # vertices can only carry powers of kappa_1, no higher kappas allowed

        # value from which on the Pixton-sum below will be polynomial in m
        m0 = (sum([abs(i) for i in Avector]) + (2 * g - 2 + n) * abs(k)) / ZZ(2) - abs(k)
        # TODO: verify this is still ok with chiodo_coeff

        exp_list, given_weights, scalar_factor, exp_list_fine = DR_coeff_setup(G, g, n, d, Avector, k, chiodo_coeff)

    h0 = gamma.num_edges() - gamma.num_verts() + 1  # first Betti number of the graph Gamma

    if chiodo_coeff:
        deg = 2 * d
    else:
        deg = 2 * sum(exp_list)  # degree of polynomial in m
    # TODO: verify this is still ok with chiodo_coeff

    # R = PolynomialRing(QQ, len(gamma.edges) + 1, 'd')
    # P=prod([(di*(d0-di))**exp_list[i] for i,di in enumerate(R.gens()[1:])])/(d0**h0)
    if r_coeff is not None:
        # it might be that given_weights doesn't sum to zero (only to zero mod r)
        # artificially subtract the sum from the first entry; this does not change the result mod r
        given_weights[0] -= sum(given_weights)

    u = gamma.flow_solve(given_weights)
    Vbasis = gamma.cycle_basis()

    # if r_coeff is not None, we want one particular value of r, so let function mpoly_special
    # interpolate a degree 0 polynomial at this value
    if r_coeff is not None:
        deg = 0
        m0 = r_coeff - 1

    if spin:
        spin_factor = QQ(1) / QQ(2 ** (g - h0))
    else:
        spin_factor = QQ(1)

    # mpoly = mpoly_affine_sum(P, u, Vbasis,m0+1,deg)
    mpoly = spin_factor * mpoly_special(exp_list, h0, u, Vbasis, m0 + 1, deg, chiodo_coeff, r_coeff, scalar_factor, exp_list_fine, d, spin)

    # mpoly = interpolate(mrange, mvalues)
    if rpoly:
        if chiodo_coeff:
            if r_power is not None:
                if r_power > mpoly.degree():
                    return 0
                return mpoly.list()[r_power]
            return mpoly
        else:
            if r_power is not None:
                if r_power > mpoly.degree():
                    return 0
                return mpoly.list()[r_power] * scalar_factor
            return mpoly * scalar_factor
    if chiodo_coeff:
        return mpoly.subs(r=0)
    return mpoly.subs(r=0) * scalar_factor


def mpoly_special(exp_list, h0, u, Vbasis, start, degr, chiodo_coeff, r_coeff, scalar_factor, exp_list_fine, d, spin=False):
    r"""
    Return the sum of the rational function in DR_coeff_new over the
    affine space u + V modulo r in ZZ^n as a univariate polynomial in r.
    V is the lattice with basis Vbasis.
    Use that this sum is polynomial in r starting from r=start and the polynomial has
    degree degr (for now).
    """
    mrange = list(range(start, start + degr + 1))
    if chiodo_coeff and r_coeff is None:
        # temporary security measure: interpolate with one more value, check degree still at most degr
        mrange.append(start + degr + 1)
    if spin:
        mrange = [2 * q for q in mrange]  # if spin is true, only consider r even
    mvalues = []
    rank = len(Vbasis)
    ulen = len(u)

    for m in mrange:
        total = 0
        for coeff in itertools.product(*[list(range(m)) for i in range(rank)]):
            v = u + sum([coeff[i] * Vbasis[i] for i in range(rank)])
            v = [vi % m for vi in v]
            if chiodo_coeff:
                if not spin or all(x % 2 == 1 for x in v):  # if spin is true, only count the odd weightings
                    total += prod(econtrib(exp_list_fine[i][0], exp_list_fine[i][1], -v[i] % m, m) for i in range(ulen))
            else:
                if not spin or all(x % 2 == 1 for x in v):  # if spin is true, only count the odd weightings
                    total += prod([(v[i] * (m - v[i]))**exp_list[i] for i in range(ulen)])
        if chiodo_coeff:
            mvalues.append(scalar_factor(0, m) * total * (m ** (2 * d - h0)))
        else:
            mvalues.append(total / QQ(m ** h0))
    result = interpolate(mrange, mvalues, 'r')
    if result.degree() > degr:
        raise ValueError('Polynomial has higher degree in r than expected!')
    return result


def econtrib(e1, e2, w1, r):
    polycoeff = edge_power_series(e1 + e2)[(e1, e2)]
    return polycoeff(*((-1)**m * bernoulli_polynomial(w1 / ZZ(r), m + 2) / (m + 1) / (m + 2) for m in range(e1 + e2 + 1)))


@cached_function
def edge_power_series(deg):
    R = PolynomialRing(QQ, 'a', deg + 1)
    A = R.gens()  # A = [a0, ..., a(deg)]
    S = PowerSeriesRing(R, 'X,Y', default_prec=deg + 2)
    X, Y = S.gens()
    ex = sum(A[i] * (X**(i + 1) - (-Y)**(i + 1)) for i in range(deg + 1))
    h = (1 - exp(ex)) / (X + Y)
    return {tuple(k): it for k, it in h.dict().items()}  # dictionary (1, 0) : -a1 - (1/2)*a0^2, ... with R-values


def mpoly_affine_sum(P, u, Vbasis, start, degr):
    r"""
    Return the sum of the polynomial P in variables r, d1, ..., dn over the
    affine space u + V modulo r in ZZ^n as a univariate polynomial in r.
    V is the lattice with basis Vbasis.
    Use that this sum is polynomial in r starting from r=start and the polynomial has
    degree degr (for now).
    """
    mrange = list(range(start, start + degr + 2))
    mvalues = []
    rank = len(Vbasis)

    for m in mrange:
        total = 0
        for coeff in itertools.product(*[list(range(m)) for i in range(rank)]):
            v = u + sum([coeff[i] * Vbasis[i] for i in range(rank)])
            v = [vi % m for vi in v]
            total += P(m, *v)
        mvalues.append(total)

    return interpolate(mrange, mvalues, 'r')

############
#
# DR polynomial
#
############


def multivariate_interpolate(f, d, n, gridwidth=1, R=None, generator=None, gridshift=None, transf_poly=None):
    r"""Takes a vector/number-valued function f on n variables and interpolates it on a grid around 0.
    Returns a vector with entries in a polynomial ring.

    INPUT:

    - ``d``        -- integer; maximal degree of output-polynomial in any of the variables

    - ``gridwidth``-- integer (default: `1`); width of the grid used for interpolation

    - ``R``        -- polynomial ring (default: `None`); expected to be polynomial ring in
      at least n variables; if None, use ring over QQ in variables z0,...,z(n-1)

    - ``generator``-- list (default: `None`); list of n variables in the above polynomial
      ring to be used in output; if None, use first n generators of ring

    - ``enlarge``-- integer (default: `1`); the factor of enlarging the gridwidth during
      interpolating the values

    - ``gridshift``-- tuple (default: `None`); of length n to shift the
      grid before interpolation takes place

    - ``transf_poly``-- polynomial (default: `None`); a polynomial of single variable of how to
      modify the input values to the function

    EXAMPLES::

        sage: from admcycles.double_ramification_cycle import multivariate_interpolate
        sage: from sage.modules.free_module_element import vector
        sage: def foo(x,y):
        ....:     return vector((x**2+y,2*x*y))
        ....:
        sage: multivariate_interpolate(foo,2,2)
        (z0^2 + z1, 2*z0*z1)
    """
    if R is None:
        R = PolynomialRing(QQ, 'z', n)
    if generator is None:
        generator = R.gens()

    if n == 0:  # return constant
        return R.one() * f()

    cube = [list(range(d + 1))] * n
    points = itertools.product(*cube)
    # shift cube containing evaluation points in negative direction to reduce abs value of evaluation points
    # the customized shift will also be taken into account
    if gridshift is None:
        shift = [-floor((d + 1) / QQ(2)) * gridwidth for i in range(n)]
    else:
        shift = [gridshift[i] - floor((d + 1) / QQ(2)) * gridwidth for i in range(n)]
    result = 0

    for p in points:
        # compute Lagrange polynomial not vanishing exactly at gridwidth*p
        lagr = prod([prod([generator[i] - (j * gridwidth + shift[i])
                    for j in range(d + 1) if j != p[i]]) for i in range(n)])

        pval = [gridwidth * p[i] + shift[i] for i in range(n)]
        value = lagr.subs({generator[i]: pval[i] for i in range(n)})
        if transf_poly is not None:
            pval = [transf_poly(val) for val in pval]

        # global fex,lagrex, pvalex
        # fex=f
        # lagrex=lagr
        # pvalex=pval
        if n == 1:  # avoid problems with multiplication of polynomial with vector
            mult = lagr / value
            result += vector(e * mult for e in f(*pval))
        else:
            result += f(*pval) / value * lagr
    return result


def DRpoly(g, d, n, dplus=0, tautout=True, basis=False, ring=None, gens=None, gensout=False, chiodo_coeff=False, moduli='st', spin=False):
    r"""
    Return the Double ramification cycle in genus g with n markings in degree d as a
    tautclass with polynomial coefficients. Evaluated at a point (a_1, ..., a_n) with
    sum a_i = k(2g-2+n) it equals DR_cycle(g,(a_1, ..., a_n),d).

    The computation uses interpolation and the fact that DR is a polynomial in the a_i
    of degree 2*d.

    INPUT:

    - ``dplus``  -- integer (default: `0`); if dplus>0, the interpolation is performed
      on a larger grid as a consistency check

    - ``tautout``-- bool (default: `True`); if False, returns a polynomial-valued vector
      (in all generators for basis=false, in the basis of the ring for basis=true)

    - ``basis``  -- bool (default: `False`); if True, use FZ relations to give out the
      DR cycle in a basis of the tautological ring

    - ``ring``   -- polynomial ring (default: `None`); expected to be polynomial ring in
      at least n variables; if None, use ring over QQ in variables a1,...,an

    - ``gens``   -- list (default: `None`); list of n variables in the above polynomial
      ring to be used in output; if None, use first n generators of ring

    - ``gensout``-- bool (default: `False`); if True, return (DR polynomial, list of generators
      of coefficient ring)

    - ``spin``-- bool (default: False`); if True, return the spin DR polynomial

    EXAMPLES::

      sage: from admcycles import DRpoly, DR_cycle, TautologicalRing
      sage: R = TautologicalRing(1, 2)
      sage: D, (a1, a2) = DRpoly(1, 1, 2, gensout=True)
      sage: D = D.subs({a2:-a1})
      sage: D = D.simplify()
      sage: D
      Graph :      [1] [[1, 2]] []
      Polynomial : 1/2*a1^2*psi_1 + 1/2*a1^2*psi_2
      <BLANKLINE>
      Graph :      [0] [[4, 5, 1, 2]] [(4, 5)]
      Polynomial : -1/24
      sage: (D*R.psi(1)).evaluate() # intersection number with psi_1
      1/24*a1^2 - 1/24
      sage: (D.subs({a1:4})-DR_cycle(1,(4,-4))).is_zero() # polynomial agrees with DR_cycle at (4,-4)
      True

     DR vanishes in degree d>g ([CJ18]_)::

      sage: DRpoly(1,2,2).is_zero()
      True
      sage: DRpoly(1,1,2,moduli='ct')
      Graph :      [1] [[1, 2]] []
      Polynomial : (-1/8*a1^2 - 1/4*a1*a2 - 1/8*a2^2)*(kappa_1)_0 + 1/2*a1^2*psi_1 + 1/2*a2^2*psi_2
      <BLANKLINE>
      Graph :      [0, 1] [[1, 2, 4], [5]] [(4, 5)]
      Polynomial : -1/8*a1^2 - 1/4*a1*a2 - 1/8*a2^2
      sage: R.<a1,a2,a3,b1,b2,b3> = PolynomialRing(QQ, 6)
      sage: Da = DRpoly(1, 1, 3, ring=R, gens=[a1, a2, a3])
      sage: Db = Da.subs({a1:b1, a2:b2, a3:b3})
      sage: Dab = Da.subs({a1:a1+b1, a2:a2+b2, a3:a3+b3})
      sage: diff = Da*Db - Da*Dab    # this should vanish in compact type by [HoPiSc19]_
      sage: diff.is_zero()
      False
      sage: diff.is_zero(moduli='ct')
      True
    """
    def f(*Avector):
        return DR_cycle(g, Avector, d, tautout=False, basis=basis, moduli=moduli, spin=spin)
        # k=floor(QQ(sum(Avector))/(2 * g - 2 + n))
        # return vector([QQ(e) for e in DR_red(g,d,n,Avector, k, basis)])
        # return vector(DR_compute(g,d,n,Avector, k))

    if ring is None:
        ring = PolynomialRing(QQ, ['a%s' % i for i in range(1, n + 1)])
    if gens is None:
        gens = ring.gens()[0:n]

    R = TautologicalRing(g, n, moduli)
    gridwidth = 2 * g - 2 + n
    if spin:
        shiftvec = tuple([g - 2 + n] + [-1 for i in range(n - 1)])  # to set an initial of Avector whose k is odd
        R_transf = PolynomialRing(QQ, 'x', 1)
        transf_poly = 2 * R_transf.gens()[0] + 1
        interp = multivariate_interpolate(f, 2 * d + dplus, n, gridwidth, R=ring, generator=gens, gridshift=shiftvec, transf_poly=transf_poly)
        interp = interp.subs({gens[i]: (QQ(1) / 2) * (gens[i] - QQ(1)) for i in range(n)})
    else:
        interp = multivariate_interpolate(f, 2 * d + dplus, n, gridwidth, R=ring, generator=gens)

    if not tautout:
        ans = interp
    else:
        if not basis:
            ans = R.from_vector(interp, d)
        else:
            ans = R.from_basis_vector(interp, d)
    if gensout:
        return (ans, gens)
    return ans


def degree_filter(polyvec, d):
    r"""Takes a vector of polynomials in several variables and returns a vector containing the (total)
    degree d part of these polynomials.

    INPUT:

    - vector of polynomials

    - integer degree

    EXAMPLES::

        sage: from admcycles.double_ramification_cycle import degree_filter
        sage: R.<x,y> = PolynomialRing(QQ, 2)
        sage: v = vector((x+y**2+2*x*y,1+x**3+x*y))
        sage: degree_filter(v, 2)
        (2*x*y + y^2, x*y)
    """
    resultvec = []
    for pi in polyvec:
        s = 0
        for c, m in pi:
            if m.degree() == d:
                s += c * m
        resultvec.append(s)
    return vector(resultvec)


def Hain_divisor(g, A):
    r"""
    Returns a divisor class D extending the pullback of the theta-divisor under the Abel-Jacobi map (on compact type) given by partition A of zero.

    Note: D^g/g! agrees with the Double-Ramification cycle in compact type.

    EXAMPLES::

      sage: from admcycles import *

      sage: R = PolynomialRing(QQ, 'z', 3)
      sage: z0, z1, z2 = R.gens()
      sage: u = Hain_divisor(2, (z0, z1, z2))
      sage: g = DRpoly(2, 1, 3, ring=R, gens=[z0, z1, z2]) #u,g should agree inside compact type
      sage: (u.vector() - g.vector()).subs({z0: -z1-z2})
      (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1/24)
    """
    n = len(A)
    R = TautologicalRing(g, n)

    def delt(l, I):
        # takes genus l and subset I of markings 1,...,n and returns generalized boundary divisor Delta_{l,I}
        I = set(I)
        if l == 0 and len(I) == 1:
            return -R.psi(list(I)[0])
        if l == g and len(I) == n - 1:
            i_set = set(range(1, n + 1)) - I
            return -R.psi(list(i_set)[0])
        if (l == 0 and len(I) == 0) or (l == g and len(I) == n):
            return R.zero()

        Icomp = set(range(1, n + 1)) - I
        gra = StableGraph([l, g - l], [list(I) + [n + 1], list(Icomp) + [n + 2]],
                          [(n + 1, n + 2)])
        return QQ((1, gra.automorphism_number())) * R(gra)

    result = sum([sum([(sum([A[i - 1] for i in I])**2) * delt(l, I)
                       for I in Subsets(list(range(1, n + 1)))])
                  for l in range(g + 1)])
    # note index i-1 since I subset {1,...,n} but array indices subset {0,...,n-1}

    return QQ((-1, 4)) * result


# Norbury_ThetaClass
def ThetaClass(g, n, moduli='st'):
    r"""
    Return the class Theta_{g,n} from the paper [Nor]_ by Norbury.

    INPUT:

    - ``moduli`` -- string (default: `'st'`); moduli on which Theta_{g,n} is computed

    EXAMPLES::

        We can verify many of the general properties of Theta_{g,n} in examples, starting
        with the initial condition Theta_{1,1} = 3 * psi_{1,1}.

            sage: from admcycles import ThetaClass, TautologicalRing
            sage: R = TautologicalRing(1, 1)
            sage: (ThetaClass(1,1) - 3*R.psi(1)).is_zero()
            True

        Likewise, we can check that the Theta-class pulls back correctly under boundary
        gluing maps.

            sage: from admcycles.admcycles import StableGraph, prodtautclass
            sage: A = ThetaClass(3,0)
            sage: gamma1 = StableGraph([1,2],[[1],[2]],[(1,2)])
            sage: pb1 = gamma1.boundary_pullback(A)
            sage: pb1.totensorTautbasis(4)
            [[0], [   207 -189/2   27/2], [], [], []]
            sage: check1 = prodtautclass(gamma1, protaut = [ThetaClass(1,1), ThetaClass(2,1)])
            sage: check1.totensorTautbasis(4)
            [[0], [   207 -189/2   27/2], [], [], []]

        A similar pullback property holds for the gluing map associated to the
        divisor of irreducible nodal curves.

            sage: B = ThetaClass(2,1)
            sage: gamma2 = StableGraph([1],[[1,2,3]],[(2,3)])
            sage: pb2 = gamma2.boundary_pullback(B)
            sage: pb2.totensorTautbasis(3)
            (6)
            sage: ThetaClass(1,3).basis_vector()
            (6)

        Finally, we check the property Theta_{g,n+1} = pi*(Theta_{g,n}) * psiclass_{n+1}::

            sage: C = ThetaClass(2,0)
            sage: R = TautologicalRing(2, 1)
            sage: (C.forgetful_pullback([1]) * R.psi(1) - B).is_zero()
            True
    """
    r = ZZ(2)
    s = -ZZ(1)
    d = ZZ(2) * g - 2 + n
    x = -ZZ(1)
    A = n * (1,)
    return ZZ(2)**(g - 1 + n) * (r**(2 * g - 2 * d - 1)) * (x**d) * DR_cycle(g, A, d, s, chiodo_coeff=True, r_coeff=r, moduli=moduli)
