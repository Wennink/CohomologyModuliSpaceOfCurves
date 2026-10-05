# -*- coding: utf-8 -*-
r"""
Double ramification cycle
"""

import itertools
from copy import copy

from sage.combinat.integer_vector import IntegerVectors
from sage.combinat.combinat import bernoulli_polynomial
from sage.arith.all import factorial
from sage.functions.log import exp
from sage.rings.all import QQ
from sage.rings.power_series_ring import PowerSeriesRing

from admcycles.admcycles import list_strata
from admcycles.stable_graph import StableGraph
from admcycles.double_ramification_cycle import DR_cycle
from .tautological_ring import TautologicalRing

# S.<x0,x1>=PowerSeriesRing(QQ,'x0,x1',default_prec=14)


def graph_sum(g, n, decgraphs=None, globalfact=None, vertterm=None, legterm=None, edgeterm=None, maxdeg=None, deg=None, termsout=False):
    r"""Returns the (possibly mixed-degree) tautological class obtained by summing over graphs gamma,
    inserting vertex-, leg- and edgeterms.

    INPUT:

    - ``decgraphs`` -- list or generator; entries of decgraphs are pairs (gamma,dec) of a StableGraph
      gamma and some additional combinatorial structure dec associated to gamma

    - ``globalfact`` -- function; globalfact(gamma,dec) gets handed the parameters gamma,dec as arguments and gives out a number that is multiplied with the corresponding term in the graph sum; default is 1

    - ``vertterm`` -- function; ``vertterm(gv,nv,maxdeg, **kwargs)`` takes arguments local genus gv and number of legs nv
      and maxdeg gets handed the parameters gamma,dec,v as optional keyworded arguments and gives out a
      tautological class on Mbar_{gv,nv}; the class is assumed to be of degree at most maxdeg,
      if deg is given, the class is exactly of degree deg

    - ``legterm`` -- function; ``legterm(gv,nv,i,maxdeg, **kwargs)`` similar to vertterm, except input is
      gv,nv,i,maxdeg where i is number of marking on Mbar_{gv,nv} associated to leg
      gamma, dec and origleg (number of leg in outer graph) given as keyworded arguments

    - ``edgeterm`` -- function; edgeterm(maxdeg,**kwargs) takes keyworded arguments gamma,dec,e,maxdeg
      it gives a generating series s in x0,x1 such that the insertion at edge
      e=(h0,h1) is given by s(psi_h0, psi_h1)

    - ``termsout`` -- parameter; if termsout=False, return sum of all terms
      if termsout = 'coarse', return tuple of terms, one for each pair (gamma,dec)
      if termsout = 'fine', return tuple of terms, one for each pair (gamma,dec) and each distribution
      of cohomological degrees to vertices and half-edges
    """
    if maxdeg is None:
        maxdeg = 3 * g - 3 + n if deg is None else deg
    if decgraphs is None:
        decgraphs = [(gr, None) for ednum in range(3 * g - 3 + n + 1)
                     for gr in list_strata(g, n, ednum)]
    if globalfact is None:
        def globalfact(a, b):
            return 1
    if vertterm is None:
        def vertterm(gv, nv, maxdeg, **kwargs):
            return TautologicalRing(gv, nv).fundamental_class()
    if legterm is None:
        def legterm(gv, nv, i, maxdeg, **kwargs):
            return TautologicalRing(gv, nv).fundamental_class()
    if edgeterm is None:
        def edgeterm(maxdeg, **kwargs):
            S = PowerSeriesRing(QQ, 'x0,x1', default_prec=maxdeg + 1)
            return S.one()

    termlist = []

    for (gamma, dec) in decgraphs:
        restdeg = maxdeg - len(gamma.edges())
        if restdeg < 0:
            continue

        gammadectermlist = []

        numvert = gamma.numvert()
        gnvect = [(gamma.genera(i), len(gamma.legs(i))) for i in range(numvert)]
        dimvect = [3 * g - 3 + n for (g, n) in gnvect]
        markings = gamma.list_markings()
        vertdic = {l: v for v in range(numvert) for l in gamma.legs(v)}
        indexdic = {l: j + 1 for v in range(numvert) for j, l in enumerate(gamma.legs(v))}
        # ex_dimvect=[dimvect[vertdic[l]] for l in halfedges]  # list of dimensions of spaces adjacent to half-edges

        # Pre-compute all vertex-, leg- and edgeterms
        vterms = {v: vertterm(gnvect[v][0], gnvect[v][1], restdeg, gamma=gamma, dec=dec, v=v) for v in range(numvert)}
        lterms = {i: legterm(gnvect[vertdic[i]][0], gnvect[vertdic[i]][1], indexdic[i],
                             restdeg, gamma=gamma, dec=dec, origleg=i) for i in markings}
        eterms = {e: edgeterm(restdeg, gamma=gamma, dec=dec, e=e) for e in gamma.edges()}
        varlist = {(h0, h1): eterms[h0, h1].parent().gens() for h0, h1 in gamma.edges()}
        eterms = {e: eterms[e].coefficients() for e in eterms}
        varx = {h0: varlist[h0, h1][0] for h0, h1 in gamma.edges()}
        varx.update({h1: varlist[h0, h1][1] for h0, h1 in gamma.edges()})

        if deg is None:
            rdlis = range(restdeg + 1)  # terms of all degrees up to restdeg must be computed
        else:
            rdlis = [deg - len(gamma.edges())]
        for rdeg in rdlis:
            # distribute the remaining degree rdeg to vertices
            for degdist in IntegerVectors(rdeg, numvert, outer=dimvect):
                # now for each vertex, split degree to vertex- and leg/half-edge terms
                vertchoices = [IntegerVectors(degdist[v], len(gamma.legs(v)) + 1) for v in range(numvert)]
                for choice in itertools.product(*vertchoices):
                    vdims = []
                    ldims = {}
                    for v in range(numvert):
                        vdims.append(choice[v][0])
                        ldims.update({l: choice[v][i + 1] for i, l in enumerate(gamma.legs(v))})

                    effvterms = [vterms[v].degree_part(vdims[v]) for v in vterms]
                    efflterms = {i: lterms[i].degree_part(ldims[i]) for i in lterms}
                    for i in efflterms:
                        effvterms[vertdic[i]] *= efflterms[i]  # multiply contributions from legs to vertexterms
                    for h0, h1 in gamma.edges():
                        # TODO: optimization potential here by multiplying kppolys directly
                        gv0, nv0 = gnvect[vertdic[h0]]
                        R0 = TautologicalRing(gv0, nv0)
                        effvterms[vertdic[h0]] *= eterms[(h0, h1)].get(varx[h0]**ldims[h0]
                                                                       * varx[h1]**ldims[h1], 0) * R0.psi(indexdic[h0])**ldims[h0]
                        gv1, nv1 = gnvect[vertdic[h1]]
                        R1 = TautologicalRing(gv1, nv1)
                        effvterms[vertdic[h1]] *= R1.psi(indexdic[h1])**ldims[h1]
                    for t in effvterms:
                        t.simplify()
                    # print(gamma)
                    # print(rdeg)
                    # print(degdist)
                    # print(choice)
                    # print(effvterms)
                    # print(eterms)
                    # print(indexdic)
                    # print('\n')
                    tempres = gamma.boundary_pushforward(effvterms)
                    tempres.simplify()
                    if not tempres.is_empty():
                        tempres *= globalfact(gamma, dec)
                        gammadectermlist.append(tempres)
                    # print(termlist)
        if termsout == 'coarse':
            termlist.append(sum(gammadectermlist))
        else:
            termlist += gammadectermlist
    if termsout:
        return termlist
    else:
        return sum(termlist)

############
#
# Useful functions and examples
#
############

###
# Example 1 : Conjectural graph sum for DR_g(1,-1)
###

# Generating functions for graphs


def DR11_tree_test(gr):
    return gr.vertex(1) == gr.vertex(2)


def DR11_trees(g, maxdeg):
    return [gr for n in range(1, g + 1) for e in range(min(n, maxdeg - n + 1))
            for gr in list_strata(0, 2 + n, e) if DR11_tree_test(gr)]


def DR11_graphs(g, maxdeg=None):
    if maxdeg is None:
        maxdeg = 3 * g - 3 + 2
    result = []
    for gr in DR11_trees(g, maxdeg):
        n = len(gr.list_markings()) - 2
        maxleg = max([max(j + [0]) for j in gr.legs])
        grlist = []
        for gdist in IntegerVectors(g, n, min_part=1):
            genera = copy(gr.genera) + list(gdist)
            legs = copy(gr.legs) + [[j] for j in range(maxleg + 1, maxleg + n + 1)]
            edges = copy(gr.edges) + [(j - maxleg + 2, j) for j in range(maxleg + 1, maxleg + n + 1)]
            grlist.append(StableGraph(genera, legs, edges))
        result += [(gam, None) for gam in grlist]
    removedups(result, lambda a, b: a[0].is_isomorphic(b[0]))
    return result


def removedups(li, comp=None):
    """
    Remove duplicates in a list ``li`` according to a comparison function.

    This works inplace and modifies ``li``.

    EXAMPLES::

        sage: from admcycles.graph_sum import removedups
        sage: L = [4,6,3,2,4,99,1,3,2]
        sage: removedups(L)
        sage: L
        [6, 4, 99, 1, 3, 2]
    """
    if comp is None:
        def comp(a, b):
            return a == b
    n = len(li)
    currn = len(li)
    for i in range(n, -1, -1):
        if any(comp(li[i], li[j]) for j in range(i + 1, currn)):
            li.pop(i)
            currn -= 1

# Global factor = 1/|Aut(Gamma)|


def divbyaut(gamma, dec):
    return QQ(1) / gamma.automorphism_number()

# Vertex- and edgeterms for DR11


def DR11_vterm(gv, nv, maxdeg, **kwargs):
    R = TautologicalRing(gv, nv)
    if gv == 0:
        gamma = kwargs['gamma']
        v = kwargs['v']
        f = R.fundamental_class()
        if 1 not in gamma.legs[v]:
            # we are in genus zero vertex not equal to base
            return -nv * f
        else:
            # we are at the base vertex
            return f
    else:
        return sum([(-1)**j * R.lambdaclass(j) for j in range(maxdeg + 1)])


def DR11_eterm(maxdeg, **kwargs):  # smarter: edterm(maxdeg=None,gamma=None,dec=None,e=None, *args, *kwds)
    S = PowerSeriesRing(QQ, 'x0,x1', default_prec=maxdeg + 1)
    x0, x1 = S.gens()
    return 1 / (1 - x0 - x1 + x0 * x1)

# Final conjectural graph sum expressing DR_g(1,-1)


def DR11_sum(g, deg=None, **kwds):
    if deg is None:
        deg = g
    return graph_sum(g, 2, decgraphs=DR11_graphs(g, maxdeg=deg), globalfact=divbyaut, vertterm=DR11_vterm, edgeterm=DR11_eterm, deg=deg, **kwds)


def DR11_decgraphs(g, maxdeg=None):
    """
    Decorate the graphs of DR11_graphs(g) with a choice of half-edge
    at each non-root vertex.
    """
    for gr0, _ in DR11_graphs(g, maxdeg):
        L = [v for v in gr0.legs if 1 not in v]
        for choice in itertools.product(*L):
            yield (gr0, choice)


def divbyaut_new(gamma, dec):
    zeroverts = gamma.genera.count(0)
    return factorial(zeroverts - 1) / gamma.automorphism_number()

# Vertex- and edgeterms for DR11


def DR11_vterm_new(gv, nv, maxdeg, **kwargs):
    R = TautologicalRing(gv, nv)
    if gv == 0:
        gamma = kwargs['gamma']
        v = kwargs['v']
        f = R.fundamental_class()
        if 1 not in gamma.legs[v]:
            # we are in genus zero vertex not equal to base
            return -1 * f
        else:
            # we are at the base vertex
            return f
    else:
        return sum([(-1)**j * R.lambdaclass(j) for j in range(maxdeg + 1)])


def DR11_eterm_new(maxdeg, **kwargs):  # smarter: edterm(maxdeg=None,gamma=None,dec=None,e=None, *args, *kwds)
    S = PowerSeriesRing(QQ, 'x0,x1', default_prec=maxdeg + 1)
    x0, x1 = S.gens()
    e = kwargs['e']
    dec = kwargs['dec']
    ex = 0
    for i in e:
        if i in dec:
            ex += 1
    return 1 / ((1 - x0 - x1)**ex)

# Final conjectural graph sum expressing DR_g(1,-1)


def DR11_sum_new(g, deg=None, **kwds):
    if deg is None:
        deg = g
    return graph_sum(g, 2, decgraphs=DR11_decgraphs(g, maxdeg=deg), globalfact=divbyaut_new, vertterm=DR11_vterm_new, edgeterm=DR11_eterm_new, deg=deg, **kwds)


###
# Example 2 : Chiodo's formula from [JPPZ, Corollary 4]
###
def dicunion(d1, d2):
    r"""
    Computes the union of dictionaries d1, d2.

    EXAMPLES::

        sage: from admcycles.graph_sum import dicunion
        sage: d1 = {1:2, 3:4}; d2 = {1:2, 4:5};
        sage: dicunion(d1, d2)
        {1: 2, 3: 4, 4: 5}
    """
    d3 = copy(d1)
    d3.update(d2)
    return d3


def GammaWlist(g, Avector, k, r):
    r"""
    Returns a generator of pairs (Gamma, w) of pairs of stable graphs Gamma in genus g
    and admissible k-weightings w mod r on Gamma for the weight vector Avector.

    EXAMPLES::

        sage: from admcycles.graph_sum import GammaWlist
        sage: list(GammaWlist(0, (4,-1,-2,-3), 1, 2))
        [([0] [[1, 2, 3, 4]] [], {1: 4, 2: -1, 3: -2, 4: -3}),
         ([0, 0] [[1, 2, 5], [3, 4, 6]] [(5, 6)],
          {1: 4, 2: -1, 3: -2, 4: -3, 5: 0, 6: 0}),
         ([0, 0] [[1, 3, 5], [2, 4, 6]] [(5, 6)],
          {1: 4, 2: -1, 3: -2, 4: -3, 5: 1, 6: 1}),
         ([0, 0] [[1, 4, 5], [2, 3, 6]] [(5, 6)],
          {1: 4, 2: -1, 3: -2, 4: -3, 5: 0, 6: 0})]
    """
    n = len(Avector)
    stdic = {i + 1: Avector[i] for i in range(n)}
    for e in range(3 * g - 3 + n + 1):  # number of edges"""
        for gamma in list_strata(g, n, e):
            edges = gamma.edges()
            for w in itertools.product(*[list(range(r)) for h in edges]):
                dic = dicunion(stdic, {edges[i][0]: w[i] for i in range(len(edges))})
                dic.update({edges[i][1]: (r - w[i]) % r for i in range(len(edges))})
                if all((k * (2 * gv - 2 + len(hev)) - sum(dic[h] for h in hev)) % r == 0 for gv, hev in zip(gamma.genera(), gamma.legs())):
                    yield (gamma, dic)


def Chiodo_GF(g, r):
    def GF(gamma, dic):
        h1 = gamma.num_edges() - gamma.num_verts() + 1
        return r**(2 * g - 1 - h1) / gamma.automorphism_number()
    return GF


def expclass(x, g=None, n=None):
    r"""
    Given a tautological class x on Mbar_{g,n} of degree at least 1, returns
    the exponential exp(x) = 1 + x + 1/2*x^2 + ... of x.

    EXAMPLES::

        sage: from admcycles.graph_sum import expclass
        sage: from admcycles import TautologicalRing
        sage: R = TautologicalRing(1, 2)
        sage: expclass(R.psi(1))
        doctest:...: DeprecationWarning: expclass is deprecated. Please use the exp method of TautologicalClass instead
        See https://gitlab.com/modulispaces/admcycles/-/merge_requests/109 for details.
        Graph :      [1] [[1, 2]] []
        Polynomial : 1 + psi_1 + 1/2*psi_1^2

    TESTS::

        sage: from admcycles import TautologicalRing
        sage: R = TautologicalRing(0, 3)
        sage: expclass(R.zero(), 0, 3)
        Graph :      [0] [[1, 2, 3]] []
        Polynomial : 1
    """
    from .superseded import deprecation
    deprecation(109, 'expclass is deprecated. Please use the exp method of TautologicalClass instead')
    if g is not None:
        if n is not None:
            R = TautologicalRing(g, n)
        else:
            R = TautologicalRing(g)
        return R(x).exp()
    return x.exp()


def Chiodo_vterm(k, r):
    def vterm(gv, nv, maxdeg, **kwargs):
        R = TautologicalRing(gv, nv)
        expo = -sum((-1)**(m - 1) * bernoulli_polynomial(k / r, m + 1) / m / (m + 1) * R.kappa(m)
                    for m in range(1, 3 * gv - 3 + nv + 1))
        return R(expo).exp()
    return vterm


def Chiodo_legterm(r):
    def legterm(gv, nv, i, maxdeg, **kwargs):
        R = TautologicalRing(gv, nv)
        dec = kwargs['dec']
        origleg = kwargs['origleg']
        ai = dec[origleg]
        expo = sum((-1)**(m - 1) * bernoulli_polynomial(ai / r, m + 1) / m /
                   (m + 1) * R.psi(i)**m for m in range(1, 3 * gv - 3 + nv + 1))
        return R(expo).exp()
    return legterm


def Chiodo_edgeterm(r):
    def eterm(maxdeg, **kwargs):
        dec = kwargs['dec']
        e = kwargs['e']
        wh = dec[e[0]]

        S = PowerSeriesRing(QQ, 'x0,x1', default_prec=maxdeg + 4)
        x0, x1 = S.gens()
        expo = sum((-1)**(m - 1) * bernoulli_polynomial(wh / r, m + 1) / m /
                   (m + 1) * (x0**m - (-x1)**m) for m in range(1, maxdeg + 3))
        return (1 - exp(expo)) / (x0 + x1)
    return eterm


def Chiodo_alt(g, Avector, k, r):
    r"""
    Computes the mixed-degree class epsilon_* c(-R^* pi_* L) from [JPPZ17]_, Corollary 4.

    This agrees with the corresponding sum of DR_cycles with chiodo_coeff=True, weighted by appropriate powers of r.

    EXAMPLES::

        sage: from admcycles.graph_sum import Chiodo, Chiodo_alt
        sage: g=1; A=(0,0); k=2; r=2;
        sage: (Chiodo_alt(g, A, k, r)-Chiodo(g, r, k, A, 1)).simplify()
        0
        sage: g=1; A=(1,1); k=4; r=3;
        sage: (Chiodo_alt(g, A, k, r)-Chiodo(g, r, k, A, 1)).simplify()
        0
    """
    n = len(Avector)
    GWlist = GammaWlist(g, Avector, k, r)
    GF = Chiodo_GF(g, r)
    vterm = Chiodo_vterm(k, r)
    lterm = Chiodo_legterm(r)
    eterm = Chiodo_edgeterm(r)

    return graph_sum(g, n, decgraphs=GWlist, globalfact=GF, vertterm=vterm, legterm=lterm, edgeterm=eterm)


def Chiodo(g, r, k, A, x):
    n = len(A)
    return sum((r**(2 * g - 2 * d - 1)) * (x**d) * DR_cycle(g, A, d, k, chiodo_coeff=True, r_coeff=r) for d in range(3 * g - 3 + n + 1))
