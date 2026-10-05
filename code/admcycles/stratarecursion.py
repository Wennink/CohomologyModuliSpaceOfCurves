# -*- coding: utf-8 -*-
r""" Recursive computation of strata of k-differentials

This is following the papers [FaPa18]_ by Farkas-Pandharipande and [Sch18]_ by Schmitt.
"""

from collections.abc import Iterable
from copy import deepcopy
import itertools

from sage.misc.misc import subsets
from sage.combinat.integer_vector import IntegerVectors
from sage.combinat.partition import Partitions
from sage.misc.misc_c import prod
from sage.rings.all import ZZ, QQ
from sage.misc.cachefunc import cached_function
from sage.combinat.words.word import Word
from sage.functions.other import ceil
from sage.arith.misc import gcd
from sage.combinat.posets.poset_examples import posets

from .stable_graph import StableGraph
from admcycles.double_ramification_cycle import DR_cycle
import admcycles.diffstrata.sig
import admcycles.diffstrata.generalisedstratum
import admcycles.diffstrata.spinstratum
from .tautological_ring import TautologicalRing

# Given a genus g, an order k and a partition mu of k(2g-2), twistenum
# returns a list of graphs with twists

# Elements of this list are of the following form
# [
#   [g_0, [markings of v_0] ],
#   [g_1, [markings of v_1], #edges of v_1, [twists of edges to v_1] ],
#   ...,
#   [g_r, [markings of v_r], #edges of v_r, [twists of edges to v_r] ]
# ]
# NOTE: Twists are counted in multiples of k, so a twist of 3 actually means 3k

# ordering of graphs (always descending)
# genus g0 of central vertex > outlying vertex data
# ordering of outlying vertices
# total genus > genus > total edge twist


def classes(l):
    """
    INPUT:

    - l -- a list

    EXAMPLES::

        sage: from admcycles.stratarecursion import classes
        sage: classes([])
        []
        sage: classes([4,4,3,3,3,1,1])
        [[0, 1], [2, 3, 4], [5, 6]]
    """
    if not l:
        return []
    indices = []
    current = [0]
    currentitem = l[0]
    for i in range(1, len(l)):
        if l[i] == currentitem:
            current += [i]
        else:
            indices += [current]
            current = [i]
            currentitem = l[i]
    indices += [current]
    return indices


def SetPart(S, s):
    """
    Return a list of partitions of the set S into the disjoint union of s sets.

    A partition is a list of sets.

    EXAMPLES::

        sage: from admcycles.stratarecursion import SetPart
        sage: S = set(['b','o','f'])
        sage: SetPart(S,2)
        [[set(), {'b', 'f', 'o'}],
        ...
        [{'b', 'f', 'o'}, set()]]
        sage: SetPart(S,1)
        [[{'b', 'f', 'o'}]]
        sage: SetPart(S,-1)
        []
        sage: SetPart(S,0)
        []
    """
    if s < 0:
        return []
    if s == 0:
        if S:
            return []
        else:
            return [[]]
    if s == 1:
        return [[S]]

    resu = []
    for T in subsets(S):
        for r in SetPart(S - set(T), s - 1):
            resu.append([set(T)] + r)
    return resu


def twistenum(g, k, mu):
    k = ZZ(k)
    lis = []  # list of all graphs, returned in the end

    # collect all negative or non-divisible-by-k markings in A, all others in B
    A = []
    B = []
    for i in range(len(mu)):
        if mu[i] < 0 or (mu[i] % k != 0):
            A.append(i)
        else:
            B.append(i)
    Atot = sum([mu[i] for i in A])

    for g0 in range(g + 1):  # g0 = genus of center vertex
        # iterate over possible partitions of the rest of the genera to vertices
        for totgenlist in Partitions(g - g0):
            # list containing lists of indices with equal total genus
            cl = classes(totgenlist)

            # we can have 1 up to total_genus many edges, distribute the len(c) many possibilities to those
            # each of the len(c) vertices can have 1, ..., total_genus many edges; vector (1,0,2) means
            # 1 vertex has 1 edge, no vertex has 2 edges, 2 vertices have 3 edges
            par = [IntegerVectors(len(c), totgenlist[c[0]]) for c in cl]

            for p in itertools.product(*par):
                # gra contains the information that will eventually be added to lis
                gra = [[g0, A]]
                numed = 0  # total number of edges
                for j in range(len(cl)):
                    # p[j] is now an integer vector, encoding edge numbers of vertices c in cl[j] with totgenlist[c[0]] total genus
                    for z in range(len(p[j])):
                        gra += [[totgenlist[cl[j][0]] - z, [], z + 1, []]
                                for _ in range(p[j][z])]
                        numed += p[j][z] * (z + 1)

                # iterate over additional markings sent to v_0
                for markings0 in subsets(B):
                    # vertex v0 unstable
                    if g0 == 0 and numed + len(A) + len(markings0) <= 2:
                        continue
                    Btot = sum([mu[i] for i in markings0])
                    if not k.divides(Atot + Btot):
                        continue

                    Brest = [b for b in B if b not in markings0]

                    Itotal = (Atot + Btot) // k - 2 * numed - (2 * g0 - 2)

                    # Itotal is the total number of ADDITIONAL twists k that can be distributed to the various edges
                    # (all have k as default anyway, so each edge has at least a pole of order 2*k on the central vertex)

                    # TODO: break if Itotal<0

                    vertcl = classes(gra)

                    for coarsesttwistdist in IntegerVectors(Itotal, len(vertcl) - 1):
                        # distribute the additional twists on the classes of outlying vertices
                        twist = []
                        # twist will be a list for every class of outlying vertex recording a list of all possible twist->edge distr.
                        # element of the list for the class {3,4,5} have the form
                        # [[a,b],[c],[d,e,f]] if v_3 has two edges, v_4 one and v_5 three

                        for i in range(len(vertcl) - 1):
                            # for each of the classes collect the possibilities to distribute inside this class
                            vertcltwistlist = []
                            # will be added as an element to twist
                            for coarsetwistdist in Partitions(coarsesttwistdist[i] + len(vertcl[i + 1]), length=len(vertcl[i + 1])):
                                # coarsetwistdist describes how twists are distributed to the vertices in vertcl[i+1]
                                # artificially added ones to be able to use Partitions

                                inditwist = [Partitions(
                                    coarsetwistdist[v] + gra[vertcl[i + 1][v]][2] - 1, length=gra[vertcl[i + 1][v]][2]) for v in range(len(vertcl[i + 1]))]
                                # list for every vertex in the class giving all possible twists of the edges of this vertex

                                vertcltwistlist += itertools.product(
                                    *inditwist)

                            twist.append(vertcltwistlist)
                        for inde in itertools.product(*twist):
                            # inde is now of the form [ [[a,b], [c], [d,e,f]] , [[g], [h,i]], ...  ]
                            grap = deepcopy(gra)
                            # this will be updated now with the edge twists determined above and the markings sent to v_0
                            grap[0][1] += markings0
                            count = 1
                            for i in inde:
                                for j in i:
                                    grap[count][3] = j
                                    count += 1

                            twicla = classes(grap)
                            # print((twicla,len(twicla)-1,Brest))

                            for pa in SetPart(set(Brest), len(twicla) - 1):
                                mpar = [SetPart(pa[c], len(twicla[c + 1]))
                                        for c in range(len(twicla) - 1)]
                                if not mpar and Brest:
                                    continue
                                for part in itertools.product(*mpar):
                                    # part is now of the form [ [ set([0,2]), set([1]) ]  , [ set([3]) ] , ...  ]
                                    graph = deepcopy(grap)
                                    count = 1
                                    adm = True  # check if graph satisfies twist conditions at all vertices
                                    for i in part:
                                        for j in i:
                                            # we are now at the vertex v_count and need to check if the twist-condition is satisfied
                                            graph[count][1] = list(j)
                                            if (2 * graph[count][0] - 2) * k + k * sum(-l + 1 for l in graph[count][3]) != sum(mu[l] for l in graph[count][1]):
                                                adm = False
                                            count += 1
                                    if adm:
                                        sgraph = (
                                            (graph[0][0], tuple(sorted(m + 1 for m in graph[0][1]))),)
                                        sgraph += tuple(sorted(((gv, tuple(sorted(m + 1 for m in marki)), tuple(
                                            sorted(k * t for t in etwist))) for gv, marki, enu, etwist in graph[1:])))
                                        lis.append(sgraph)

    return list(set(lis))


def Strataclass(g, k, mu, virt=False, res_cond=(), xi_power=0, method='pull', spin=False, spin_conj=False, primitive=False):
    r"""
    Returns the fundamental class of the closure of the stratum of k-differentials in genus g in Mbar_{g,n}
    with vanishing and pole orders mu.

    The class is computed using a formula from papers by Farkas-Pandharipande and Schmitt,
    proven by [HoSc]_ and [BHPSS]_.
    The formula for differentials with residue conditions is based on unpublished work
    relying on [BaChGeGrMo]_.

    If the mu is of spin type, we can compute the spin stratum class H^+ - H^-. In [CSS21]_, Costantini,
    Sauvaget and Schmitt made a similar conjecture for the Pixton formula.

    INPUT:

    - ``g``  -- integer ; genus of the curves

    - ``k`` -- integer ; power of the canonical line bundle in definition of stratum

    - ``mu`` -- tuple ; tuple of integers of length n giving zero and pole multiplicities
      of k-differential, required to sum up to k*(2g-2)

    - ``virt``   -- bool (default: `False`); if True, k=1 and all entries of mu nonnegative, this
      computes the virtual codimension g class supported on the codimension g-1 stratum of
      holomorphic 1-differentials.

    - ``res_cond``   -- tuple (default: `()`); tuple of residue conditions. Each entry of
      res_cond can be of one of the following two types:

        - an integer i from 1, ..., n indicating a marking i with mu[i]<=-k, such that the
          differential eta is required to have a pole with vanishing (k-)residue at the marking.

        - a tuple (c1, ..., cn) of rational numbers indicating that a condition
          c1 * Res_{p1}(eta) + ... + cn * Res_{pn}(eta) = 0
          is imposed. Currently only implemented for ci in {0,1} and k=1.

      The function then computes the class of the closure of the locus of smooth curves
      having such a differential eta.

    - ``xi_power``   -- integer (default: `0`); if positive, returns the pushforward of
      the corresponding power of the first Chern class xi = c_1(O(-1)) of the tautological
      bundle on the moduli space of multi-scale differentials from [BCGGM3].
      Currently only implemented for k=1 and with method = 'diffstrata'.

    - ``method``   -- string (default: `'pull'`); when computing a stratum of 1-differentials
      with residue conditions, there are two choices here: 'pull' will compute it via boundary
      pullbacks of higher genus strata, 'diffstrata' will use the package `diffstrata`, which
      iteratively replaces residue conditions with equivalent divisorial conditions. The two
      results should be equal.

    - ``spin``   -- bool (default: `False`); if true, we will compute the spin stratum class

    - ``spin_conj``   -- bool (default: `False`); if we assume the conjecture in [CSS21]_ to be true,
      we will compute the spin stratum class by first compute the holomorphic strata of the same genus,
      then use the conjecture to recursively compute the input stratum class

    - ``primitive``  -- bool (default: `False`); if true, only compute the fundamental class of the connected component of the stratum that parametrizes primitive k-differentials (i.e. those k-differentials that are not powers of k'-differentials for some k'<k).

    WARNING::

        Imposing residue conditions at poles of high order leads to very long computations,
        since the method works by computing strata of differentials on high-genus moduli
        spaces.

    TESTS::

        sage: from admcycles import Hyperell, Biell
        sage: from admcycles.stratarecursion import Strataclass
        sage: L=Strataclass(2,1,(3,-1)); L.is_zero()
        True
        sage: L=Strataclass(3,1,(5,-1)); L.is_zero() # doctest: +SKIP
        True
        sage: L=Strataclass(2,1,(2,)); (L-Hyperell(2,1)).is_zero()
        True

    In g=2, the locus Hbar_2(2,2) decomposes into the codimension 1 set of Hbar_2(1,1) and the
    codimension 2 set of curves (C,p,q) with p,q Weierstrass points. The latter is equal to the cycle
    Hyperell(2,2). We can obtain it by subtracting the virtual cycle for the partition (1,1) from the
    virtual cycle for the partition (2,2)::

        sage: H1 = Strataclass(2, 2, (2, 2), virt = True)
        sage: H2 = Strataclass(2, 1, (1, 1), virt = True)
        sage: T = H1 - H2 - Hyperell(2, 2)
        sage: T.is_zero()
        True

    In g=1, the locus Hbar_1(2,-2) is the locus of curves (E,p,q) with p-q being 2-torsion in E.
    Equivalently, this is the locus of bielliptic curves with a pair of bielliptic conjugate points::

        sage: (Strataclass(1,1,(2,-2)) - Biell(1,0,1)).is_zero()
        True

    Some tests of computations involving residue conditions::

        sage: from admcycles import Strataclass
        sage: OmegaR = Strataclass(1,1,(6,-4,-2),res_cond=(3,))
        sage: OmegaRalt = Strataclass(1,1,(6,-4,-2),res_cond=(2,)) # long time
        sage: (OmegaR - OmegaRalt).is_zero() # long time
        True
        sage: (OmegaR.forgetful_pushforward([2,3])).fund_evaluate()
        42
        sage: a=4; (a+2)**2 + a**2 - 10 # formula from [Castorena-Gendron, Cor. 5.5]
        42
        sage: OmegaR2 = Strataclass(1,1,(4,-2,-2),res_cond=(3,))
        sage: (OmegaR2.forgetful_pushforward([2,3])).fund_evaluate()
        10
        sage: OmegaR3 = Strataclass(1,1,(5,-3,-2),res_cond=(2,)) #  not tested
        sage: (OmegaR3.forgetful_pushforward([2,3])).fund_evaluate() #  not tested
        24
        sage: a=3; (a+2)**2 + a**2 - 10 # formula from [Castorena-Gendron, Cor. 5.5] #  not tested
        24
        sage: OmegaR5 = Strataclass(2,1,(5,-1,-2),res_cond=(3,)) #  not tested
        sage: OmegaR5.is_zero() # vanishes by residue theorem # not tested
        True

    We can also check that the two ways of computing residue conditions (via pullbacks and
    via the package diffstrata) coincide::

        sage: a = Strataclass(1,1,(4,-2,-2), res_cond=(2,))
        sage: b = Strataclass(1,1,(4,-2,-2), res_cond=(2,), method='diffstrata')
        sage: (a-b).is_zero()
        True

    The following computes the locus of genus 1 curves admitting a differential with multiplicity
    vector (8,-2,-2,-2,-2) at the markings such that the sum of residues at p2 and p3 equals zero::

        sage: c = Strataclass(1,1,(8,-2,-2,-2,-2), res_cond=((0,1,1,0,0),))

    Using the parameter xi_power, we can observe an interesting relationship between strata with
    xi-insertions and higher terms in Pixton's formula of the double ramification cycle::

        sage: from admcycles import DR_cycle
        sage: g=0; mu = [11,4,-8,-2,-5,-2]; A = [a+1 for a in mu]
        sage: n = len(mu); adddeg = 1
        sage: D = DR_cycle(g,A,rpoly=True,d=g+adddeg,chiodo_coeff=True)
        sage: v = vector(QQ,[a[adddeg] for a in D.basis_vector()])
        sage: S = Strataclass(g,1,mu,xi_power=adddeg)
        sage: print(v); print(-S.basis_vector())
        (0, 0, -4, 7, 2, 4, 2, 0, -1, 0, 0, 0, 0, 2, 0, 2)
        (0, 0, -4, 7, 2, 4, 2, 0, -1, 0, 0, 0, 0, 2, 0, 2)

    We can use the function to compute spin stratum class, with or without the assumption of the
    conjecture of spin Pixton formula::

        sage: cl1=Strataclass(2,1,(8,-4,-2),spin=True)
        sage: cl1.basis_vector()
        (-1107/2, 369/2, -246, -552, -899/2, 288, 590, 807/2, 1254, 1167/2, 1947/2, 613, -793, -1354, 351, -615, -666, 939/2, -563, -2077/2, 1302, 1107/2, -2583/2, 369/2, 21, -165, -181, -369/2, -201/2, 201/2, 551/2, -31/2, -155/2, -203/2, 18, -18, 114, 119/2, -58, 102, -102, -109/2, -76, 142)
        sage: cl2=Strataclass(2,1,(8,-4,-2),spin=True,spin_conj=True)
        sage: cl1==cl2
        True

    If we assume the conjecture above, we can also compute spin strata of meromorphic k-differentials
    for k > 1. Below we check that they restrict under a boundary gluing map as expected::

        sage: from admcycles import StableGraph
        sage: from admcycles.admcycles import prodtautclass
        sage: H = Strataclass(2,3,[10,-4],spin=True,spin_conj=True)
        sage: gamma = StableGraph([1,1],[[1,3],[2,4]],[(3, 4)])
        sage: pb = gamma.boundary_pullback(H)
        sage: H1 = Strataclass(1,3,[10,-10],spin=True,spin_conj=True)
        sage: H2 = Strataclass(1,3,[-4,4],spin=True,spin_conj=True)
        sage: prot = prodtautclass(gamma, protaut=[H1, H2])
        sage: pb.totensorTautbasis(2) == prot.totensorTautbasis(2)
        True

    We test that summing up the components of a stratum gives in fact
    the stratum::

        sage: (Strataclass(2, 6, (12,), virt=True) - sum(Strataclass(2, 6 // d, (12 // d,), virt=True, primitive=True) for d in [1,2,3,6])).is_zero()
        True

    We check Conjecture 1.4 from [CGHMS]_ in some genus zero cases::

        sage: def test_conjecture(mu):
        ....:     for u in range(1, len(mu) - 2):
        ....:         k = -sum(mu) // 2
        ....:         A = [m + k for m in mu]
        ....:         scl = Strataclass(0, k, mu, xi_power=u, virt=True, primitive=True)
        ....:         v_scl = scl.basis_vector()
        ....:         drcl = DR_cycle(0, A, d=u, chiodo_coeff=True, rpoly=True)
        ....:         v_drcl = vector([ui[u] for ui in drcl.basis_vector()])
        ....:         assert (-1)**u * v_scl == v_drcl
        sage: test_conjecture((-1,-1,-1,-1))
        sage: test_conjecture((-1,-1,-1,-3,2))
        sage: test_conjecture((-1,-1,-1,-4,1))
    """
    n = len(mu)
    R = TautologicalRing(g, n)
    k = ZZ(k)
    if sum(mu) != k * (2 * g - 2):
        raise ValueError('mu must be a partition of k*(2g-2).')

    # Hbar has codimension g
    meromorphic = any(not k.divides(m) or m < 0 for m in mu)

    if spin:
        method = 'diffstrata'
        if any(m % 2 != 0 for m in mu):
            raise ValueError('The signature is not of spin type')
        if k > 1:
            if primitive:
                raise NotImplementedError("For k>1 spin is only implemented for primitive=False")
            if k % 2 != 1:
                raise ValueError('The integer k has to be odd if we want to have spin structure.')
            if not spin_conj or not meromorphic or res_cond != () or xi_power != 0:
                raise NotImplementedError
            method = 'pull'  # for k>1, we do not use diffstrata
        elif res_cond == () and meromorphic and spin_conj:
            method = 'pull'  # in this cases, we do not use diffstrata

    if (g == 0) and not (res_cond or xi_power):
        if primitive and not gcd(list(mu) + [k]) == 1:
            return R.zero()
        else:
            return R.fundamental_class()

    if all(m == 0 for m in mu) and not (res_cond or xi_power):
        if primitive and k > 1:
            return R.zero()
        else:
            return -R.fundamental_class() if spin else R.fundamental_class()

    if method == 'diffstrata' or xi_power > 0 or any(isinstance(rc, Iterable) for rc in res_cond) or (k > 1 and res_cond):
        if k == 1:
            if virt:
                raise NotImplementedError('virt=True not implemented for method="diffstrata" and k=1')
            # preprocessing residue conditions
            fancy_res_cond = []
            for rc in res_cond:
                if isinstance(rc, Iterable):
                    if not all(a == 0 or a == 1 for a in rc):
                        raise NotImplementedError('Only residue conditions with coefficients 0,1 implemented.')
                    fancy_res_cond.append([(0, i) for i, a in enumerate(rc) if a == 1])
                else:
                    fancy_res_cond.append([(0, rc - 1)])

            X = admcycles.diffstrata.generalisedstratum.GeneralisedStratum(
                sig_list=[admcycles.diffstrata.sig.Signature(tuple(mu))], res_cond=fancy_res_cond)

            elgtclass = X.xi_pow(xi_power)  # ELGTautClass of the xi class with power

            if spin:  # if spin, we turn the ELGTautClass into spin version
                elgtspin = admcycles.diffstrata.spinstratum.ELGT_addspin(elgtclass)
                return elgtspin.to_prodtautclass_spin().pushforward()

            return elgtclass.to_prodtautclass().pushforward()
        else:
            if any(isinstance(rc, Iterable) for rc in res_cond):
                raise NotImplementedError('Residue conditions of the form (c1, ..., cn) only implemented for k=1')
            if spin:
                raise NotImplementedError
            if not primitive:
                raise NotImplementedError("xi_pow>0 and k>1 only implemented for primitive=True")
            if not virt:
                raise ValueError('The combination of virt=False and primitive=True is not sensible for k>1')
            X = admcycles.diffstrata.generalisedstratum.Stratum(
                mu, k, vanishing_residues=res_cond)

            elgtclass = X.zeta_pow(xi_power)  # ELGTautClass of the xi class with power
            return elgtclass.to_prodtautclass().pushforward()

    if len(res_cond) > 0:
        # res_cond = tuple(res_cond) # make sure it is of type tuple
        if not k == 1:
            raise RuntimeError('Residue conditions for k>1 should have been handled before')
        if virt:
            raise ValueError('Residue conditions not compatible with virt=True')

        res_cond = sorted(res_cond)
        poles = [i for (i, mui) in enumerate(mu) if mui < 0]  # indices of poles

        if len(poles) == 1:  # residue conditions are automatic
            return Strataclass(g, k, mu, virt=virt)

        if any(mu[i - 1] >= 0 for i in res_cond):  # try imposing residue cond. at non-pole
            raise ValueError('Residue conditions can only be imposed at poles')
        if any(mu[i - 1] == -1 for i in res_cond):  # try imposing residue cond. at simple pole
            return R.zero()

        num_add_marks = len([1 for i in res_cond if mu[i - 1] % 2])  # additional markings
        maxleg = n + num_add_marks + 2

        genera = [g] + [ceil(-mu[i - 1] / 2) for i in res_cond]
        munew = []
        outermus = []
        markcounter = 1
        legs = [[]]
        edges = [(maxleg + 2 * j, maxleg + 2 * j + 1) for j in range(len(res_cond))]

        for i in range(1, n + 1):
            if i not in res_cond:
                legs[0].append(markcounter)
                munew.append(mu[i - 1])
                markcounter += 1
            else:
                legs[0].append(maxleg)
                if mu[i - 1] % 2 == 0:
                    legs.append([maxleg + 1])
                    outermus.append([-mu[i - 1] - 2])
                else:
                    legs.append([maxleg + 1, markcounter])
                    outermus.append([-mu[i - 1] - 2, 1])
                    munew.append(1)
                    markcounter += 1
                maxleg += 2
        gamma = StableGraph(genera, legs, edges)

        outerg = sum(genera)
        outerclass = Strataclass(outerg, k, munew, virt=False)

        pullb = gamma.boundary_pullback(outerclass)
        return pullb.factor_reconstruct(0, [Strataclass(genera[j + 1], 1, outermus[j]) for j in range(len(res_cond))])

    if k > 1 and not meromorphic and not virt:
        # all entries divisible by k and nonnegative AND user wants a codim g-1 class
        # return the corresponding stratum of abelian differentials
        if primitive:
            raise ValueError('The combination of virt=False and primitive=True is not sensible for k>1')
        return Strataclass(g, 1, tuple(m // k for m in mu))

    if primitive and k > 1:
        P = posets.DivisorLattice(gcd(list(mu) + [k]))
        # compute primitive component by Moebius inversion formula
        return sum(P.moebius_function(1, y) * Strataclass(g, k // y, [m // y for m in mu], virt=True) for y in P)
        # Alternative implementation without fancy Moebius inversion
        # ans = Strataclass(g, k, mu, virt=True)
        # # We substract the non-primitive compunents
        # for d in gcd(list(mu) + [k]).divisors():
        #     if d == 1:
        #         continue
        #     ans -= Strataclass(g, k // d, [m // d for m in mu], virt=True, primitive=True)
        # return ans

    ordering_permutation = Word(mu).standard_permutation().inverse()
    ordering_dict = {i + 1: j for i, j in enumerate(ordering_permutation)}
    # this is the dictionary such that renaming the answer with standard-ordering according to ordering_dict gives correct answer
    sortmu = tuple(sorted(mu))

    try:
        v = StrataDB.cached(g, k, sortmu, virt, spin)
        if meromorphic or virt:  # return codim g class
            ans_preord = R.from_vector(v, g)
        else:
            ans_preord = R.from_vector(v, g - 1)
        ans_preord.rename_legs(ordering_dict)
        return ans_preord
    except KeyError:
        pass

    # at this point, we actually have to compute
    # we will compute the answer with standard ordering, store its vector in StrataDB and then return the renamed answer
    if meromorphic or virt:
        # return codimension g class
        bdry_list = twistenum(g, k, sortmu)
        indfind1 = tuple((i for i, l in enumerate(bdry_list) if l[0][0] == g))
        assert len(indfind1) == 1, (g, k, mu, tuple(indfind1))
        bdry_list.pop(indfind1[0])  # remove the trivial graph

        # right hand side of recursion
        result = DR_cycle(g, tuple(m + k for m in sortmu), spin=spin)
        result -= Strataboundarysum(g, k, sortmu, bdry_list=bdry_list, spin=spin, spin_conj=spin_conj)

        v = result.vector(g)
        StrataDB.set_cache(v, *(g, k, sortmu, virt, spin))
        result = R.from_vector(v, g)  # gives simplified version of result
        result.rename_legs(ordering_dict)
        return result
    else:
        # return codimension g-1 class
        # by previous check can assume that k=1
        assert k == 1, (g, k, mu)

        sortmuprime = list(sortmu) + [-1]
        sortmuprime[n - 1] += 1
        sortmuprime = tuple(sortmuprime)

        bdry_list = twistenum(g, k, sortmuprime)

        indfind1 = tuple((i for i, l in enumerate(bdry_list) if l[0][0] == g))
        assert len(indfind1) == 1, (g, k, mu, tuple(indfind1))
        bdry_list.pop(indfind1[0])  # remove the trivial graph

        indfind2 = tuple((i for i, l in enumerate(bdry_list) if len(
            l) == 2 and l[0][0] == 0 and l[0][1] == (n, n + 1) and l[1][0] == g))
        assert len(indfind2) == 1, (g, k, mu)
        bdry_list.pop(indfind2[0])

        preresult = DR_cycle(g, tuple(m + k for m in sortmuprime))
        preresult -= Strataboundarysum(g, k, sortmuprime, bdry_list=bdry_list)
        result = preresult.forgetful_pushforward([n + 1])
        result *= QQ(1) / sortmuprime[n - 1]

        v = result.vector(g - 1)
        StrataDB.set_cache(v, *(g, k, sortmu, virt, spin))
        result = R.from_vector(v, g - 1)  # gives simplified version of result
        result.rename_legs(ordering_dict)
        return result


def Strataboundarysum(g, k, mu, bdry_list=None, termsout=False, spin=False, spin_conj=False):
    r"""
    Returns sum of boundary terms in Conjecture A for entries of bdry_list.
    These entries have the format from the output of twistenum, but might be a subset of these.

    INPUT:

        - g (integer): genus

        - k (integer): power of canonical bundle

        - bdry_list (list, default=None): a sublist of all the twisted stable graphs; if not
          specified, it will just use the whole list

        - termsout (bool, default=False): if true, then the output will not be simplified

        - spin (bool, default=False): if true, then compute the spin strata boundary sum

        - spin_conj (bool, default=False): if true, then we will assume the spin Conjecture A
          to be true and the summand will be computed by recursion on this formula

    EXAMPLES::

        sage: from admcycles.stratarecursion import Strataboundarysum
        sage: from admcycles.double_ramification_cycle import DR_cycle
        sage: Strataboundarysum(2,1,(6,-4),spin=True).basis_vector()
        (-139, 46, -109, -99, 219, 194, 174, 136, -318, 91/2, -45/2, -15, -46, -25/2)

    """
    if spin:
        if any(m % 2 != 0 for m in mu):
            raise ValueError('This signature is not of spin type')
        if all(m >= 0 for m in mu) and all(k.divides(m) for m in mu):
            raise ValueError('The boundary sum with spin should not be called by such signature')
        if k > 1:
            if k % 2 != 1:
                raise ValueError('The integer k has to be odd if we want to have spin structure.')
            if not spin_conj:
                raise NotImplementedError

    if bdry_list is None:
        bdry_list = twistenum(g, 1, mu)

    resultterms = []
    n = len(mu)
    for vdata in bdry_list:
        genera = [b[0] for b in vdata]
        legs = [list(b[1]) for b in vdata]  # just markings at the moment
        edges = []
        maxleg = n + 1
        # stores twist at legs and half-edges
        twist = {i: mu[i - 1] for i in range(1, n + 1)}
        for v, (_, _, twistvect) in list(enumerate(vdata))[1:]:
            for I in twistvect:
                legs[0].append(maxleg)
                legs[v].append(maxleg + 1)
                edges.append((maxleg, maxleg + 1))
                twist[maxleg] = -I - k
                twist[maxleg + 1] = I - k
                maxleg += 2
        bdry_graph = StableGraph(genera, legs, edges)
        coeff = prod([I for (_, _, twistvect) in vdata[1:] for I in twistvect])
        coeff /= k**(len(genera) - 1) * automorphism_number_fixing_twist(bdry_graph, twist)

        if spin and any(y % 2 != 0 for _, y in twist.items()):
            continue
        else:
            vertterms = [Strataclass(genera[0], k, [twist[l] for l in legs[0]], spin=spin, spin_conj=spin_conj)]
            vertterms += [Strataclass(genera[v], 1, [twist[l] // k for l in legs[v]], spin=spin, spin_conj=spin_conj)
                          for v in range(1, len(genera))]
            bdry_term = bdry_graph.boundary_pushforward(vertterms)
            resultterms += [coeff * bdry_term]

    if termsout:
        return resultterms
    else:
        result = sum(resultterms)
        result.simplify()
        return result


@cached_function
def StrataDB(g, k, mu):
    raise NotImplementedError('StrataDB is just an internal database '
                              'for strata classes, use Strataclass instead')


def automorphism_number_fixing_twist(gr, I):
    r"""
    Return number of automorphisms of gr leaving the twist I on gr invariant.

    EXAMPLES::

        sage: from admcycles import StableGraph
        sage: from admcycles.stratarecursion import automorphism_number_fixing_twist
        sage: gr = StableGraph([0,0],[[1,2,3],[4,5,6]],[(1,2),(3,4),(5,6)])
        sage: twist = {i:0 for i in range(7)}
        sage: automorphism_number_fixing_twist(gr,twist)
        8
        sage: twist[1] = 1
        sage: automorphism_number_fixing_twist(gr,twist)
        2
        sage: twist[2] = 1
        sage: automorphism_number_fixing_twist(gr,twist)
        4
    """
    halfedges = gr.halfedges()
    G = gr.leg_automorphism_group()
    return len([1 for g in G if all(I[g(h)] == I[h] for h in halfedges)])
