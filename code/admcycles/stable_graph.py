# -*- coding: utf-8 -*-
r"""
Stable graphs
"""
import itertools
from collections import defaultdict

from sage.misc.misc_c import prod

from sage.structure.sage_object import SageObject

from sage.combinat.permutation import Permutations
from sage.combinat.subset import Subsets
from sage.rings.integer_ring import ZZ
from sage.modules.free_module import FreeModule
from sage.functions.other import floor
from sage.graphs.graph import Graph
from sage.rings.all import Integer
from sage.arith.all import factorial
from sage.groups.perm_gps.permgroup_named import SymmetricGroup

from sage.plot.polygon import polygon2d
from sage.plot.text import text
from sage.plot.bezier_path import bezier_path
from sage.plot.line import line
from sage.plot.circle import circle

from .superseded import deprecated_function_alias
from .moduli import MODULI_ST, MODULI_TL, MODULI_CT, MODULI_RT, MODULI_SM


class StableGraph(SageObject):
    r"""
    Stable graph.

    A stable graph is a graph (with allowed loops and multiple edges) that
    has "genus" and "marking" decorations at its vertices. It is represented
    as a list of genera of its vertices, a list of legs at each vertex and a
    list of pairs of legs forming edges.

    The markings (the legs that are not part of edges) are allowed to have
    repetitions.

    EXAMPLES:

    We create a stable graph with two vertices of genera 3,5 joined by an edge
    with a self-loop at the genus 3 vertex::

        sage: from admcycles import StableGraph
        sage: StableGraph([3,5], [[1,3,5],[2]], [(1,2),(3,5)])
        [3, 5] [[1, 3, 5], [2]] [(1, 2), (3, 5)]

    The markings can have repetitions::

         sage: StableGraph([1,0], [[1,2], [3,2]], [(1,3)])
         [1, 0] [[1, 2], [3, 2]] [(1, 3)]

    It is also possible to create graphs which are not necessarily stable::

        sage: StableGraph([1,0], [[1], [2,3]], [(1,2)])
        [1, 0] [[1], [2, 3]] [(1, 2)]

        sage: StableGraph([0], [[1]], [])
        [0] [[1]] []

    If the input is invalid a :class:`ValueError` is raised::

        sage: StableGraph([0, 0], [[1], [2], [3]], [])
        Traceback (most recent call last):
        ...
        ValueError: genera and legs must have the same length

        sage: StableGraph([0, 'hello'], [[1], [2]], [(1,2)])
        Traceback (most recent call last):
        ...
        ValueError: genera must be a list of non-negative integers

        sage: StableGraph([0, 0], [[1,2], [3]], [(3,4)])
        Traceback (most recent call last):
        ...
        ValueError: the edge (3, 4) uses invalid legs

        sage: StableGraph([0, 0], [[2,3], [2]], [(2,3)])
        Traceback (most recent call last):
        ...
        ValueError: the edge (2, 3) uses invalid legs
    """
    __slots__ = ['_genera', '_legs', '_edges', '_maxleg', '_mutable',
                 '_graph_cache', '_canonical_label_cache', '_hash']

    def __init__(self, genera, legs, edges, mutable=False, check=True):
        """
        INPUT:

        - ``genera`` -- (list) List of genera of the vertices of length m.

        - ``legs`` -- (list) List of length m, where ith entry is list of legs
          attached to vertex i.

        - ``edges`` -- (list) List of edges of the graph. Each edge is a 2-tuple of legs.

        - ``mutable`` - (boolean, default to ``False``) whether this stable graph
          should be mutable

        - ``check`` - (boolean, default to ``True``) whether some additional sanity
          checks are performed on input
        """
        if check:
            if not isinstance(genera, list) or \
               not isinstance(legs, list) or \
               not isinstance(edges, list):
                raise TypeError('genera, legs, edges must be lists')

            if len(genera) != len(legs):
                raise ValueError('genera and legs must have the same length')

            if not all(isinstance(g, (int, Integer)) and g >= 0 for g in genera):
                raise ValueError("genera must be a list of non-negative integers")

            mlegs = defaultdict(int)
            for v, l in enumerate(legs):
                if not isinstance(l, list):
                    raise ValueError("legs must be a list of lists")
                for i in l:
                    if not isinstance(i, (int, Integer)) or i <= 0:
                        raise ValueError("legs must be positive integers")
                    mlegs[i] += 1

            for e in edges:
                if not isinstance(e, tuple) or len(e) != 2:
                    raise ValueError("invalid edge {}".format(e))
                if mlegs.get(e[0], 0) != 1 or mlegs.get(e[1], 0) != 1:
                    raise ValueError("the edge {} uses invalid legs".format(e))

        self._genera = genera
        self._legs = legs
        self._edges = edges
        self._maxleg = max([max(j + [0]) for j in self._legs])  # highest leg-label that occurs
        self._mutable = bool(mutable)
        self._graph_cache = None
        self._canonical_label_cache = None
        self._hash = None

    def set_immutable(self):
        r"""
        Set this graph immutable.
        """
        self._mutable = False

    def is_mutable(self):
        r"""
        Return whether this graph is mutable.
        """
        return self._mutable

    def __hash__(self):
        r"""
        EXAMPLES::

            sage: from admcycles import StableGraph
            sage: G1 = StableGraph([3,5], [[1,3,5],[2]], [(1,2),(3,5)])
            sage: G2 = StableGraph([3,5], [[1,3,5],[2]], [(1,2),(3,5)])
            sage: G3 = StableGraph([3,5], [[3,5,1],[2]], [(2,1),(3,5)])
            sage: G4 = StableGraph([2,2], [[1,3,5],[2]], [(1,2),(3,5)])
            sage: G5 = StableGraph([3,5], [[1,4,5],[2]], [(1,2),(4,5)])
            sage: hash(G1) == hash(G2)
            True
            sage: (hash(G1) == hash(G3) or hash(G1) == hash(G4) or
            ....:  hash(G1) == hash(G5) or hash(G3) == hash(G4) or
            ....:  hash(G3) == hash(G5) or hash(G4) == hash(G5))
            False
        """
        if self._mutable:
            raise TypeError("mutable stable graph are not hashable")
        if self._hash is None:
            self._hash = hash((tuple(self._genera),
                              tuple(tuple(x) for x in self._legs),
                              tuple(self._edges)))
        return self._hash

    def copy(self, mutable=True):
        r"""
        Return a copy of this graph.

        When it is asked for an immutable copy of an immutable graph the
        current graph is returned without copy.

        INPUT:

        - ``mutable`` - (boolean, default ``True``) whether the returned graph must
          be mutable

        EXAMPLES::

            sage: from admcycles import StableGraph
            sage: G = StableGraph([3,5], [[1,3,5],[2]], [(1,2),(3,5)])
            sage: H = G.copy()
            sage: H == G
            True
            sage: H.is_mutable()
            True
            sage: H is G
            False

            sage: G.copy(mutable=False) is G
            True
        """
        if not self.is_mutable() and not mutable:
            # avoid copy when immutability holds for both
            return self
        G = StableGraph.__new__(StableGraph)
        G._genera = self._genera[:]
        G._legs = [x[:] for x in self._legs]
        G._edges = [x[:] for x in self._edges]
        G._maxleg = self._maxleg
        G._mutable = mutable
        G._graph_cache = None
        G._canonical_label_cache = None
        G._hash = None
        return G

    def __repr__(self):
        return repr(self._genera) + ' ' + repr(self._legs) + ' ' + repr(self._edges)

    def __lt__(self, other):
        r"""
        TESTS::

            sage: from admcycles import StableGraph
            sage: g0 = StableGraph([1], [[1, 2, 3]], [])
            sage: g1 = StableGraph([0], [[5, 6, 1, 2, 3]], [(5, 6)])
            sage: g2 = StableGraph([0, 1], [[1, 2, 5], [3, 6]], [(5, 6)])
            sage: g3 = StableGraph([0, 1], [[1, 3, 5], [2, 6]], [(5, 6)])
            sage: g4 = StableGraph([0, 1], [[2, 3, 5], [1, 6]], [(5, 6)])
            sage: sorted([g3, g1, g2, g4, g0]) == sorted([g2, g0, g4, g1, g3]) == [g0, g1, g2, g3, g4]
            True

            sage: g0 < g0
            False
            sage: g0 <= g0
            True

            sage: g1 > g0 and g1 >= g0 and g2 > g1 and g2 >= g1
            True
            sage: g1 < g0 or g1 <= g0 or g2 < g1 or g2 <= g1
            False
        """
        if type(self) is not type(other):
            raise TypeError('incomparable elements')

        # first sort by number of edges
        sne = self.num_edges()
        one = other.num_edges()
        if sne < one:
            return True
        if one < sne:
            return False

        # then by number of vertices
        snv = self.num_verts()
        onv = other.num_verts()
        if snv < onv:
            return True
        elif snv > onv:
            return False

        # then use plain comparison of the data
        if self._genera < other._genera:
            return True
        elif self._genera > other._genera:
            return False
        elif self._legs < other._legs:
            return True
        elif self._legs > other._legs:
            return False
        elif self._edges < other._edges:
            return True
        elif self._edges > other._edges:
            return False
        else:
            # equality case
            return False

    def __eq__(self, other):
        r"""
        TESTS::

            sage: from admcycles import StableGraph
            sage: G1 = StableGraph([3,5], [[1,3,5],[2]], [(1,2),(3,5)])
            sage: G2 = StableGraph([3,5], [[1,3,5],[2]], [(1,2),(3,5)])
            sage: G3 = StableGraph([3,5], [[3,5,1],[2]], [(2,1),(3,5)])
            sage: G4 = StableGraph([2,2], [[1,3,5],[2]], [(1,2),(3,5)])
            sage: G5 = StableGraph([3,5], [[1,4,5],[2]], [(1,2),(4,5)])
            sage: G1 == G2
            True
            sage: G1 == G3 or G1 == G4 or G1 == G5
            False
        """
        if type(self) is not type(other):
            return False
        return self._genera == other._genera and \
            self._legs == other._legs and \
            self._edges == other._edges

    def __ne__(self, other):
        return not (self == other)

    def __le__(self, other):
        return self == other or self < other

    def __gt__(self, other):
        return other < self

    def __ge__(self, other):
        return self == other or other < self

    def _graph(self):
        if not self._mutable and self._graph_cache is not None:
            return self._graph_cache

        # TODO: it should be much faster to build this graph...
        from collections import defaultdict

        legs = defaultdict(list)

        # the multiplicity of edges is stored as integral labels
        # on the graph
        G = Graph(len(self._genera), loops=True, multiedges=False, weighted=True)
        for li, lj in self._edges:
            i = self.vertex(li)
            j = self.vertex(lj)
            if G.has_edge(i, j):
                G.set_edge_label(i, j, G.edge_label(i, j) + 1)
            else:
                G.add_edge(i, j, 1)

            if i < j:
                legs[i, j].append((li, lj))
            else:
                legs[j, i].append((lj, li))

        sym = len(self.list_markings()) + sum(map(len, self._edges)) != sum(map(len, self._legs))

        vertex_partition = defaultdict(list)
        for i, (g, l) in enumerate(zip(self._genera, self._legs)):
            if sym:
                l = sorted(self.list_markings_symm(i))
            else:
                l = sorted(self.list_markings(i))
            inv = (g,) + tuple(l)
            vertex_partition[inv].append(i)

        vertex_data = sorted(vertex_partition)
        partition = [vertex_partition[k] for k in vertex_data]

        output = (G, vertex_data, dict(legs), partition)
        if not self._mutable:
            self._graph_cache = output
        return output

    def _canonical_label(self):
        if not self._mutable and self._canonical_label_cache is not None:
            return self._canonical_label_cache
        G, _, _, partition = self._graph()

        # NOTE: we explicitly set algorithm='sage' since bliss got confused
        # with edge labeled graphs. See
        # https://trac.sagemath.org/ticket/28531
        H, phi = G.canonical_label(partition=partition,
                                   edge_labels=True,
                                   certificate=True,
                                   algorithm='sage')

        output = (H, phi)
        if not self._mutable:
            self._canonical_label_cache = output
        return output

    def set_canonical_label_symm(self, certificate=False, sortlegs=False):
        if not self._mutable:
            raise ValueError("the graph must be mutable; use inplace=False")

        G, vdat, legs, part = self._graph()
        H, dicv = self._canonical_label()
        invdicv = {j: i for i, j in dicv.items()}
        if certificate:
            dicl = {}

        # vdat: list of the possible (g, l0, l1, ...)
        # where l0, l1, ... are the markings
        # legs: dico: (i,j) -> list of edges given by pair of legs

        new_genera = [self._genera[invdicv[i]] for i in range(self.num_verts())]
        assert new_genera == sorted(self._genera)
        new_legs = [sorted(self.list_markings_symm(invdicv[i])) for i in range(self.num_verts())]

        can_edges = []
        for e0, e1, mult in G.edges(sort=False):
            f0 = dicv[e0]
            f1 = dicv[e1]
            inv = False
            if f0 > f1:
                f0, f1 = f1, f0
                inv = True
            can_edges.append((f0, f1, e0, e1, mult, inv))
        can_edges.sort()

        nl = self.num_legs()
        marks = self.list_markings_symm()
        m0 = len(marks) + 1
        non_markings = range(m0, m0 + nl - len(marks))
        assert len(non_markings) == 2 * sum(mult for _, _, _, _, mult, _ in can_edges)

        k = 0
        new_edges = []
        for f0, f1, e0, e1, mult, inv in can_edges:
            assert f0 <= f1
            new_legs[f0].extend(non_markings[i] for i in range(k, k + 2 * mult, 2))
            new_legs[f1].extend(non_markings[i] for i in range(k + 1, k + 2 * mult, 2))
            new_edges.extend((non_markings[i], non_markings[i + 1]) for i in range(k, k + 2 * mult, 2))

            if certificate:
                assert len(legs[e0, e1]) == mult, (len(legs[e0, e1]), mult)
                if inv:
                    assert dicv[e0] == f1
                    assert dicv[e1] == f0
                    for i, (l1, l0) in enumerate(legs[e0, e1]):
                        dicl[l0] = non_markings[k + 2 * i]
                        dicl[l1] = non_markings[k + 2 * i + 1]
                else:
                    assert dicv[e0] == f0
                    assert dicv[e1] == f1
                    for i, (l0, l1) in enumerate(legs[e0, e1]):
                        dicl[l0] = non_markings[k + 2 * i]
                        dicl[l1] = non_markings[k + 2 * i + 1]

            k += 2 * mult

        self._genera = new_genera
        self._legs = new_legs
        self._edges = new_edges

        if sortlegs:
            for legs in self._legs:
                legs.sort()

        if certificate:
            return (dicv, dicl)

    def set_canonical_label(self, certificate=False, sortlegs=False):
        r"""
        Set canonical label to this stable graph.

        The canonical labeling is such that two isomorphic graphs get relabeled
        the same way. If certificate is true return a pair `dicv`, `dicl` of
        mappings from the vertices and legs to the canonical ones.

        EXAMPLES::

            sage: from admcycles import StableGraph

            sage: S = StableGraph([1,2,3], [[1,4,5],[2,6,7],[3,8,9]], [(4,6),(5,8),(7,9)])

            sage: T = S.copy()
            sage: T.set_canonical_label()
            sage: T  # random
            [1, 2, 3] [[1, 4, 6], [2, 5, 8], [3, 7, 9]] [(4, 5), (6, 7), (8, 9)]
            sage: assert S.is_isomorphic(T)

        Check that isomorphic graphs get relabelled the same way::

            sage: S0 = StableGraph([3,5], [[1,3,5,4],[2]],  [(1,2),(3,5)], mutable=False)
            sage: S1 = S0.copy()
            sage: S2 = StableGraph([3,5], [[2,3,1,4],[5]],  [(2,5),(3,1)], mutable=True)
            sage: S3 = StableGraph([5,3], [[5],[2,3,4,1]],  [(2,5),(3,1)], mutable=True)
            sage: S1.set_canonical_label()
            sage: S2.set_canonical_label()
            sage: S3.set_canonical_label()
            sage: assert S1 == S2 == S3
            sage: assert S0.is_isomorphic(S1)

            sage: S0 = StableGraph([1,2,3], [[1,4,5],[2,6,7],[3,8,9]], [(4,6),(5,8),(7,9)], mutable=False)
            sage: S1 = S0.copy()
            sage: S2 = StableGraph([3,2,1], [[3,8,5],[2,6,7],[1,4,9]], [(8,6),(5,4),(7,9)], mutable=True)
            sage: S3 = StableGraph([2,1,3], [[7,2,5],[6,4,1],[3,9,8]], [(7,6),(5,8),(4,9)], mutable=True)
            sage: S1.set_canonical_label()
            sage: S2.set_canonical_label()
            sage: S3.set_canonical_label()
            sage: assert S1 == S2 == S3
            sage: assert S0.is_isomorphic(S1)

            sage: S0 = StableGraph([1,2,3], [[1,4,5],[2,6,7],[3,8,9]], [(4,6),(5,8),(7,9)], mutable=True)
            sage: S1 = StableGraph([3,2,1], [[3,8,5],[2,6,7],[1,4,9]], [(8,6),(5,4),(7,9)], mutable=True)
            sage: S2 = StableGraph([2,1,3], [[7,2,5],[6,4,1],[3,9,8]], [(7,6),(5,8),(4,9)], mutable=True)
            sage: for S in [S0, S1, S2]:
            ....:     T = S.copy()
            ....:     assert S == T
            ....:     vm, lm = T.set_canonical_label(certificate=True)
            ....:     S.relabel(vm, lm, inplace=True)
            ....:     S.tidy_up()
            ....:     assert S == T, (S, T)


        TESTS::

            sage: from admcycles import StableGraph
            sage: S0 = StableGraph([2], [[]], [], mutable=True)
            sage: S0.set_canonical_label()

            sage: S0 = StableGraph([0,1,0], [[1,2,4], [3], [5,6,7]], [(2,3), (4,5), (6,7)])
            sage: S1 = S0.copy()
            sage: S1.set_canonical_label()
            sage: assert S0.is_isomorphic(S1)
            sage: S2 = S1.copy()
            sage: S1.set_canonical_label()
            sage: assert S1 == S2

            sage: S0 = StableGraph([1,0], [[2,3], [5,7,9]], [(2,5), (7,9)], mutable=True)
            sage: S1 = StableGraph([1,0], [[1,3], [2,7,9]], [(1,2), (7,9)], mutable=True)
            sage: S0.set_canonical_label()
            sage: S1.set_canonical_label()
            sage: assert S0 == S1
        """
        if not self._mutable:
            raise ValueError("the graph must be mutable; use inplace=False")

        G, vdat, legs, part = self._graph()
        H, dicv = self._canonical_label()
        invdicv = {j: i for i, j in dicv.items()}
        if certificate:
            dicl = {}

        # vdat: list of the possible (g, l0, l1, ...)
        # where l0, l1, ... are the markings
        # legs: dico: (i,j) -> list of edges given by pair of legs

        new_genera = [self._genera[invdicv[i]] for i in range(self.num_verts())]
        assert new_genera == sorted(self._genera)
        new_legs = [sorted(self.list_markings(invdicv[i])) for i in range(self.num_verts())]

        can_edges = []
        for e0, e1, mult in G.edges(sort=False):
            f0 = dicv[e0]
            f1 = dicv[e1]
            inv = False
            if f0 > f1:
                f0, f1 = f1, f0
                inv = True
            can_edges.append((f0, f1, e0, e1, mult, inv))
        can_edges.sort()

        nl = self.num_legs()
        marks = set(self.list_markings())
        m0 = (max(marks) if marks else 0) + 1
        non_markings = range(m0, m0 + nl - len(marks))
        assert len(non_markings) == 2 * sum(mult for _, _, _, _, mult, _ in can_edges)

        k = 0
        new_edges = []
        for f0, f1, e0, e1, mult, inv in can_edges:
            assert f0 <= f1
            new_legs[f0].extend(non_markings[i] for i in range(k, k + 2 * mult, 2))
            new_legs[f1].extend(non_markings[i] for i in range(k + 1, k + 2 * mult, 2))
            new_edges.extend((non_markings[i], non_markings[i + 1]) for i in range(k, k + 2 * mult, 2))

            if certificate:
                assert len(legs[e0, e1]) == mult, (len(legs[e0, e1]), mult)
                if inv:
                    assert dicv[e0] == f1
                    assert dicv[e1] == f0
                    for i, (l1, l0) in enumerate(legs[e0, e1]):
                        dicl[l0] = non_markings[k + 2 * i]
                        dicl[l1] = non_markings[k + 2 * i + 1]
                else:
                    assert dicv[e0] == f0
                    assert dicv[e1] == f1
                    for i, (l0, l1) in enumerate(legs[e0, e1]):
                        dicl[l0] = non_markings[k + 2 * i]
                        dicl[l1] = non_markings[k + 2 * i + 1]

            k += 2 * mult

        self._genera = new_genera
        self._legs = new_legs
        self._edges = new_edges

        if sortlegs:
            for legs in self._legs:
                legs.sort()

        if certificate:
            return (dicv, dicl)

    def relabel(self, vm, lm, inplace=False, mutable=False):
        r"""
        INPUT:

        - ``vm`` -- (dictionary) a vertex map (from the label of this graph to
          the new labels). If a vertex number is missing it will remain untouched.

        - ``lm`` -- (dictionary) a leg map (idem). If a leg label is missing it
          will remain untouched.

        - ``inplace`` -- (boolean, default ``False``) whether to relabel the
          graph inplace

        - ``mutable`` -- (boolean, default ``False``) whether to make the
          resulting graph immutable. Ignored when ``inplace=True``

        EXAMPLES::

            sage: from admcycles import StableGraph
            sage: G = StableGraph([3,5], [[1,3,5,4],[2]],  [(1,2),(3,5)])
            sage: vm = {0:1, 1:0}
            sage: lm = {1:3, 2:5, 3:7, 4:9, 5:15}
            sage: G.relabel(vm, lm)
            [5, 3] [[5], [3, 7, 15, 9]] [(3, 5), (7, 15)]

            sage: G.relabel(vm, lm, mutable=False).is_mutable()
            False
            sage: G.relabel(vm, lm, mutable=True).is_mutable()
            True

            sage: H = G.copy()
            sage: H.relabel(vm, lm, inplace=True)
            sage: H == G.relabel(vm, lm)
            True
        """
        # TODO: more inplace operations when possible
        m = len(self._genera)
        genera = [None] * m
        legs = [None] * m
        for i, (g, l) in enumerate(zip(self._genera, self._legs)):
            j = vm.get(i, i)  # new label
            genera[j] = g
            legs[j] = [lm.get(k, k) for k in l]

        edges = [(lm.get(i, i), lm.get(j, j)) for i, j in self._edges]

        if inplace:
            if not self._mutable:
                raise ValueError('the graph is not mutable; use a copy instead')
            self._genera = genera
            self._legs = legs
            self._edges = edges
        else:
            return StableGraph(genera, legs, edges, mutable)

    def is_isomorphic(self, other, certificate=False):
        r"""
        Test whether this stable graph is isomorphic to ``other``.

        INPUT:

        - ``certificate`` - if set to ``True`` return also a vertex mapping and
                            a legs mapping

        EXAMPLES::

            sage: from admcycles import StableGraph

            sage: G1 = StableGraph([3,5], [[1,3,5,4],[2]],  [(1,2),(3,5)])
            sage: G2 = StableGraph([3,5], [[2,3,1,4],[5]],  [(2,5),(3,1)])
            sage: G3 = StableGraph([5,3], [[5],[2,3,4,1]],  [(2,5),(3,1)])
            sage: G1.is_isomorphic(G2) and G1.is_isomorphic(G3)
            True

        Graphs with distinct markings are not isomorphic::

            sage: G4 = StableGraph([3,5], [[1,3,5,4],[2]],  [(1,2),(3,4)])
            sage: G1.is_isomorphic(G4) or G2.is_isomorphic(G4) or G3.is_isomorphic(G4)
            False

        Graph with marking multiplicities::

            sage: H1 = StableGraph([0], [[1,1]], [])
            sage: H2 = StableGraph([0], [[1,1]], [])
            sage: H1.is_isomorphic(H2)
            True

            sage: H3 = StableGraph([0,0], [[1,2,4],[1,3]], [(2,3)])
            sage: H4 = StableGraph([0,0], [[1,2],[1,3,4]], [(2,3)])
            sage: H3.is_isomorphic(H4)
            True

        TESTS::

            sage: from admcycles import StableGraph

            sage: G = StableGraph([0, 0], [[5, 8, 4, 3], [9, 2, 1]], [(8, 9)])
            sage: H = StableGraph([0, 0], [[1, 2, 6], [3, 4, 5, 7]], [(6, 7)])
            sage: G.is_isomorphic(H)
            True
            sage: ans, (vm, lm) = G.is_isomorphic(H, certificate=True)
            sage: assert ans
            sage: G.relabel(vm, lm)
            [0, 0] [[6, 2, 1], [5, 7, 4, 3]] [(7, 6)]

            sage: G = StableGraph([0, 0], [[4, 8, 2], [3, 9, 1]], [(8, 9)])
            sage: H = StableGraph([0, 0], [[1, 3, 5], [2, 4, 6]], [(5, 6)])
            sage: G.is_isomorphic(H)
            True
            sage: ans, (vm, lm) = G.is_isomorphic(H, certificate=True)
            sage: assert ans
            sage: G.relabel(vm, lm)
            [0, 0] [[3, 5, 1], [4, 6, 2]] [(6, 5)]

            sage: G = StableGraph([0, 1, 1], [[1, 3, 5], [2, 4], [6]], [(1, 2), (3, 4), (5, 6)])
            sage: H = StableGraph([1, 0, 1], [[1], [2, 3, 5], [4, 6]], [(1, 2), (3, 4), (5, 6)])
            sage: _ = G.is_isomorphic(H, certificate=True)

        Check for https://gitlab.com/modulispaces/admcycles/issues/22::

            sage: g1 = StableGraph([0, 0], [[1, 3], [2,4]], [(1, 2), (3, 4)])
            sage: g2 = StableGraph([0, 0], [[1], [2]], [(1, 2)])
            sage: g1.is_isomorphic(g2)
            False

        Check for https://gitlab.com/modulispaces/admcycles/issues/24::

            sage: gr1 = StableGraph([0, 0, 0, 2, 1, 2], [[1, 2, 6], [3, 7, 8], [4, 5, 9], [10], [11], [12]], [(6, 7), (8, 9), (3, 10), (4, 11), (5, 12)])
            sage: gr2 = StableGraph([0, 0, 1, 1, 1, 2], [[1, 2, 5, 6, 7], [3, 4, 8], [9], [10], [11], [12]], [(7, 8), (3, 9), (4, 10), (5, 11), (6, 12)])
            sage: gr1.is_isomorphic(gr2)
            False
        """
        if type(self) is not type(other):
            raise TypeError

        sG, svdat, slegs, spart = self._graph()
        oG, ovdat, olegs, opart = other._graph()

        # first compare vertex data partitions
        if svdat != ovdat or any(len(p) != len(q) for p, q in zip(spart, opart)):
            return (False, None) if certificate else False

        # next, graph isomorphism
        # NOTE: since canonical label maps the first atom of the partition to
        # {0, ..., m_1 - 1} the second to {m_1, ..., m_1 + m_2 - 1}, etc we are
        # guaranteed that the partitions match when the graphs are isomorphic.
        sH, sphi = self._canonical_label()
        oH, ophi = other._canonical_label()
        if sH != oH:
            return (False, None) if certificate else False

        if certificate:
            ophi_inv = {j: i for i, j in ophi.items()}
            vertex_map = {i: ophi_inv[sphi[i]] for i in range(len(self._genera))}

            legs_map = {}
            # legs that are not part of edges are untouched
            # (slot zero in the list is the genus)
            for l in svdat:
                for i in l[1:]:
                    legs_map[i] = i

            # pair of legs that form edges have moved
            for (i, j), sl in slegs.items():
                m = sG.edge_label(i, j)
                assert len(sl) == m, (m, sl, self, other)

                ii = ophi_inv[sphi[i]]
                jj = ophi_inv[sphi[j]]
                if ii <= jj:
                    ol = olegs[ii, jj]
                else:
                    ol = [(b, a) for (a, b) in olegs[jj, ii]]
                assert len(ol) == m, (m, sl, ol, self, other)

                for (a, b), (c, d) in zip(sl, ol):
                    legs_map[a] = c
                    legs_map[b] = d

            return True, (vertex_map, legs_map)

        else:
            return True

    def vertex_automorphism_group(self, *args, **kwds):
        r"""
        Return the action of the automorphism group on the vertices.

        All arguments provided are forwarded to the method `automorphism_group`
        of Sage graphs.

        EXAMPLES::

            sage: from admcycles import StableGraph

            sage: G = StableGraph([0], [[1, 2, 3, 4, 5, 6]], [(3, 4), (5, 6)])
            sage: G.vertex_automorphism_group()
            Permutation Group with generators [()]

            sage: G = StableGraph([0, 0], [[1, 1, 2], [1, 1, 3]], [(2, 3)])
            sage: G.vertex_automorphism_group()
            Permutation Group with generators [(0,1)]
            sage: G = StableGraph([0, 0], [[4, 1, 2], [1, 3, 4]], [(3, 2)])
            sage: G.vertex_automorphism_group()
            Permutation Group with generators [(0,1)]

            sage: G = StableGraph([0, 0, 0], [[1,2], [3,4], [5,6]],
            ....:                 [(2,3),(4,5),(6,1)])
            sage: A = G.vertex_automorphism_group()
            sage: A
            Permutation Group with generators [(1,2), (0,1)]
            sage: A.cardinality()
            6

        Using extra arguments::

            sage: G.vertex_automorphism_group(algorithm='sage')
            Permutation Group with generators [(1,2), (0,1)]
            sage: G.vertex_automorphism_group(algorithm='bliss')   # optional - bliss
            Permutation Group with generators [(1,2), (0,1)]
        """
        G, _, _, partition = self._graph()
        return G.automorphism_group(partition=partition,
                                    edge_labels=True,
                                    *args, **kwds)

    def leg_automorphism_induce(self, g, A=None, check=True):
        r"""
        Given a leg automorphism ``g`` return its action on the vertices.

        Note that there is no check that the element ``g`` is a valid automorphism.

        INPUT:

        - ``g`` - a permutation acting on the legs

        - ``A`` - ambient permutation group for the result

        - ``check`` - (default ``True``) parameter forwarded to the constructor
          of the permutation group acting on vertices.

        EXAMPLES::

            sage: from admcycles import StableGraph
            sage: G = StableGraph([0, 0, 0, 0], [[1,8,9,16], [2,3,10,11], [4,5,12,13], [6,7,14,15]],
            ....:                 [(1,2),(3,4),(5,6),(7,8),(9,10),(11,12),(13,14),(15,16)])
            sage: Averts = G.vertex_automorphism_group()
            sage: Alegs = G.leg_automorphism_group()
            sage: g = Alegs('(1,14)(2,13)(3,4)(5,10)(6,9)(7,8)(11,12)(15,16)')
            sage: assert G.leg_automorphism_induce(g) == Averts('(0,3)(1,2)')
            sage: g = Alegs('(3,11)(4,12)(5,13)(6,14)')
            sage: assert G.leg_automorphism_induce(g) == Averts('')
            sage: g = Alegs('(1,11,13,15,9,3,5,7)(2,12,14,16,10,4,6,8)')
            sage: assert G.leg_automorphism_induce(g) == Averts('(0,1,2,3)')

        TESTS::

            sage: G = StableGraph([3], [[]], [])
            sage: S = SymmetricGroup([0])
            sage: G.leg_automorphism_induce(S(''))
            ()
        """
        if A is None:
            A = SymmetricGroup(list(range(len(self._genera))))
        if len(self._genera) == 1:
            return A('')
        p = [self.vertex(g(self._legs[u][-1])) for u in range(len(self._genera))]
        return A(p, check=check)

    def leg_automorphism_induced_edge_aut(self, g, A=None, check=True):
        if A is None:
            A = SymmetricGroup(list(range(len(self._edges))))
        if not self._edges:
            return A('')
        p = []
        for h1, _ in self._edges:
            for i, e in enumerate(self._edges):
                if g(h1) in e:
                    p.append(i)
                    break
        return A(p, check=check)

    def vertex_automorphism_lift(self, g, A=None, check=True):
        r"""
        Provide a canonical lift of vertex automorphism to leg automorphism.

        Note that there is no check that ``g`` defines a valid automorphism of
        the vertices.

        INPUT:

        - ``g`` - permutation automorphism of the vertices

        - ``A`` - an optional permutation group in which the result belongs to

        - ``check`` -- (default ``True``) parameter forwarded to the constructor
          of the permutation group

        EXAMPLES::

            sage: from admcycles import StableGraph
            sage: G = StableGraph([0, 0, 0, 0], [[1,8,9,16], [2,3,10,11], [4,5,12,13], [6,7,14,15]],
            ....:                 [(1,2),(3,4),(5,6),(7,8),(9,10),(11,12),(13,14),(15,16)])
            sage: Averts = G.vertex_automorphism_group()
            sage: G.vertex_automorphism_lift(Averts(''))
            ()
            sage: G.vertex_automorphism_lift(Averts('(0,3)(1,2)'))
            (1,6)(2,5)(3,4)(7,8)(9,14)(10,13)(11,12)(15,16)
            sage: G.vertex_automorphism_lift(Averts('(0,1,2,3)'))
            (1,3,5,7)(2,4,6,8)(9,11,13,15)(10,12,14,16)
        """
        p = sorted(sum(self._legs, []))
        if A is None:
            A = SymmetricGroup(p)
        leg_pos = {j: i for i, j in enumerate(p)}

        G, _, edge_to_legs, partition = self._graph()

        # promote automorphisms of G as automorphisms of the stable graph
        for u, v, lab in G.edges(sort=True):
            gu = g(u)
            gv = g(v)

            if u < v:
                start = edge_to_legs[u, v]
            else:
                start = [(t, s) for s, t in edge_to_legs[v, u]]

            if gu < gv:
                end = edge_to_legs[gu, gv]
            else:
                end = [(t, s) for s, t in edge_to_legs[gv, gu]]

            for (lu, lv), (glu, glv) in zip(start, end):
                p[leg_pos[lu]] = glu
                p[leg_pos[lv]] = glv

        # ugly fix to deal with partial symmetry case
        if p.count(1) > 1:
            seen = set()
            p = [x for x in p if not (x in seen or seen.add(x))]
            A = SymmetricGroup(sorted(p))

        return A(p, check=check)

    def leg_automorphism_group_vertex_stabilizer(self, *args, **kwds):
        r"""
        Return the group of automorphisms of this stable graph stabilizing the vertices.

        All arguments are forwarded to the subgroup method of the Sage symmetric group.

        EXAMPLES::

            sage: from admcycles import StableGraph
            sage: G = StableGraph([0],[[1,2,3,4,5,6,7,8]], [(1,2),(3,4),(5,6),(7,8)])
            sage: G.leg_automorphism_group_vertex_stabilizer()
            Subgroup generated by [(1,2), (1,3)(2,4), (1,3,5,7)(2,4,6,8)] of (Symmetric group of order 8! as a permutation group)

            sage: G = StableGraph([1,1],[[1,2],[3,4]], [(1,3),(2,4)])
            sage: G.leg_automorphism_group_vertex_stabilizer()
            Subgroup generated by [(1,2)(3,4)] of (Symmetric group of order 4! as a permutation group)
        """
        legs = sorted(sum(self._legs, []))

        G, _, edge_to_legs, partition = self._graph()

        S = SymmetricGroup(legs)
        gens = []
        for u, v, lab in G.edges(sort=True):
            if lab == 1 and u != v:
                continue

            if u < v:
                multiedge = edge_to_legs[u, v]
            else:
                multiedge = edge_to_legs[v, u]

            if lab >= 2:
                (lu0, lv0) = multiedge[0]
                (lu1, lv1) = multiedge[1]
                gens.append(S.element_class([(lu0, lu1), (lv0, lv1)], S, check=False))
                if lab >= 3:
                    gens.append(S.element_class([tuple(x for x, y in multiedge),
                                                 tuple(y for x, y in multiedge)], S, check=False))
            if u == v:
                (lu, lv) = multiedge[0]
                gens.append(S.element_class([(lu, lv)], S, check=False))

        return S.subgroup(gens, *args, **kwds)

    def leg_automorphism_group(self, *args, **kwds):
        r"""
        Return the action of the automorphism group on the legs.

        The arguments provided to this function are forwarded to the
        constructor of the subgroup of the symmetric group.

        EXAMPLES::

            sage: from admcycles import StableGraph

        A triangle::

            sage: G = StableGraph([0, 0, 0], [[1,2], [3,4], [5,6]],
            ....:                 [(2,3),(4,5),(6,1)])
            sage: Alegs = G.leg_automorphism_group()
            sage: assert Alegs.cardinality() == G.automorphism_number()

        A vertex with four loops::

            sage: G = StableGraph([0], [[1,2,3,4,5,6,7,8]], [(1,2),(3,4),(5,6),(7,8)])
            sage: Alegs = G.leg_automorphism_group()
            sage: assert Alegs.cardinality() == G.automorphism_number()
            sage: a = Alegs.random_element()

        Using extra arguments::

            sage: G = StableGraph([0,0,0], [[6,1,7,8],[2,3,9,10],[4,5,11,12]],
            ....:       [(1,2), (3,4), (5,6), (7,8), (9,10), (11,12)])
            sage: G.leg_automorphism_group()
            Subgroup generated by [(11,12), (9,10), (7,8), (1,2)(3,6)(4,5)(7,9)(8,10), (1,6)(2,5)(3,4)(9,11)(10,12)] of (Symmetric group of order 12! as a permutation group)
            sage: G.leg_automorphism_group(canonicalize=False)
            Subgroup generated by [(1,6)(2,5)(3,4)(9,11)(10,12), (1,2)(3,6)(4,5)(7,9)(8,10), (11,12), (9,10), (7,8)] of (Symmetric group of order 12! as a permutation group)
        """
        legs = sorted(sum(self._legs, []))
        G, _, edge_to_legs, partition = self._graph()
        # NOTE: this is too much generators. It is enough to move around the multiple
        # edges in each orbit of the vertex automorphism group.
        S = SymmetricGroup(legs)
        gens = []
        for g in self.vertex_automorphism_group().gens():
            gens.append(self.vertex_automorphism_lift(g, S))
        for g in self.leg_automorphism_group_vertex_stabilizer().gens():
            gens.append(g)

        return S.subgroup(gens, *args, **kwds)

    def leg_automorphism_group_no_self_edge_auto(self):
        if self.num_verts() > 1:
            raise ValueError
        selfedges = []
        for i in range(len(self._genera)):
            selfedges += self.edges_between(i, i)
        G = self.leg_automorphism_group()
        L = []
        for i, (a, b) in enumerate(selfedges):
            for c, d in selfedges[:i]:
                L.append(G('(' + str(a) + ',' + str(c) + ')(' + str(b) + ',' + str(d) + ')'))
        return G.subgroup(L)

    def automorphism_number(self):
        r"""
        Return the size of the automorphism group (acting on legs).

        EXAMPLES::

            sage: from admcycles import StableGraph
            sage: G = StableGraph([0, 2], [[1, 2, 4], [3, 5]], [(4, 5)])
            sage: G.automorphism_number()
            1

            sage: G = StableGraph([0, 0, 0], [[1,2,7,8], [3,4,9,10], [5,6,11,12]],
            ....:                 [(2,3),(4,5),(6,1),(8,9),(10,11),(12,7)])
            sage: G.automorphism_number()
            48
            sage: G.leg_automorphism_group().cardinality()
            48

            sage: G = StableGraph([0, 0], [[1, 1, 2], [1, 1, 3]], [(2, 3)])
            sage: G.automorphism_number()
            Traceback (most recent call last):
            ...
            NotImplementedError: automorphism_number not valid for repeated marking

        TESTS::

            sage: from sage.combinat.permutation import Permutations
            sage: glist=[1,1,2,2]
            sage: for p in Permutations([0,1,2,3]):
            ....:     gr = StableGraph([0]+[glist[i] for i in p],[[1,2,3,4],[5],[6],[7],[8]],[(1,5),(2,6),(3,7),(4,8)])
            ....:     assert gr.automorphism_number() == 4, (gr, gr.automorphism_number())
        """
        G, _, _, _ = self._graph()
        aut = self.vertex_automorphism_group().cardinality()

        # edge automorphism
        for i, j, lab in G.edges(sort=False):
            aut *= factorial(lab)
            if i == j:
                aut *= 2**lab

        # explicitly forbid marking multiplicity
        markings = self.list_markings()
        if len(markings) != len(set(markings)):
            raise NotImplementedError("automorphism_number not valid for repeated marking")

        return aut

    def g(self):
        r"""
        Return the genus of this stable graph

        EXAMPLES::

            sage: from admcycles import StableGraph
            sage: G = StableGraph([1,2],[[1,2], [3,4]], [(1,3),(2,4)])
            sage: G.g()
            4
        """
        return sum(self._genera) + len(self._edges) - len(self._genera) + ZZ.one()

    def n(self):
        r"""
        Return the number of legs of the stable graph.

        EXAMPLES::

            sage: from admcycles import StableGraph
            sage: G = StableGraph([1,2],[[1,2],[3,4,5,6]],[(1,3),(2,4)]);G.n()
            2
        """
        return len(self.list_markings())

    def genera(self, i=None, copy=True):
        """
        Return the list of genera of the stable graph.

        If an integer argument is given, return the genus at this vertex.

        EXAMPLES::

            sage: from admcycles import StableGraph
            sage: G = StableGraph([1,2],[[1,2],[3,4,5,6]],[(1,3),(2,4)])
            sage: G.genera()
            [1, 2]
            sage: G.genera(0), G.genera(1)
            (1, 2)
        """
        if i is None:
            return self._genera[:] if copy else self._genera
        else:
            return self._genera[i]

    def edges(self, copy=True):
        r"""
        Return the list of edges.

        By default, this returns a copy of the corresponding list,
        set copy=False to obtain the internal variable of the graph.

        EXAMPLES::

            sage: from admcycles import StableGraph
            sage: Gamma = StableGraph([1,1], [[1,2,3,4,5,6],[7,8,9]], [(2,3), (4,5), (6,7)])
            sage: L = Gamma.edges(); L
            [(2, 3), (4, 5), (6, 7)]
            sage: L.append((8,9)); L
            [(2, 3), (4, 5), (6, 7), (8, 9)]
            sage: Gamma # not changed by above operation
            [1, 1] [[1, 2, 3, 4, 5, 6], [7, 8, 9]] [(2, 3), (4, 5), (6, 7)]
        """
        return self._edges[:] if copy else self._edges

    def num_verts(self):
        r"""
        Return the number of vertices.

        EXAMPLES::

            sage: from admcycles import StableGraph
            sage: Gamma = StableGraph([1,1], [[1,2,3,4,5,6],[7,8,9]], [(2,3), (4,5), (6,7), (8,9)])
            sage: Gamma.num_verts()
            2
        """
        return len(self._genera)

    def legs(self, v=None, copy=True):
        r"""
        Return the list of legs at vertex v, or the whole list of
        legs if v is not specified.

        By default, this returns a copy of the corresponding list(s),
        set copy=False to obtain the internal variable of the graph.

        EXAMPLES::

            sage: from admcycles import StableGraph
            sage: Gamma = StableGraph([1,1], [[1,2,3,4,5,6],[7,8,9]], [(2,3), (4,5), (6,7)])
            sage: L = Gamma.legs(0); L
            [1, 2, 3, 4, 5, 6]
            sage: L.append(10); L
            [1, 2, 3, 4, 5, 6, 10]
            sage: Gamma # not changed by above operation
            [1, 1] [[1, 2, 3, 4, 5, 6], [7, 8, 9]] [(2, 3), (4, 5), (6, 7)]
            sage: Gamma.legs()
            [[1, 2, 3, 4, 5, 6], [7, 8, 9]]
        """
        if v is None:
            return [l[:] for l in self._legs] if copy else self._legs
        else:
            return self._legs[v][:] if copy else self._legs[v]

    # TODO: deprecate
    numvert = num_verts

    def num_edges(self):
        r"""
        Return the number of edges.

        EXAMPLES::

            sage: from admcycles import StableGraph
            sage: Gamma = StableGraph([1,1], [[1,2,3,4,5,6],[7,8,9]], [(2,3), (4,5), (6,7), (8,9)])
            sage: Gamma.num_edges()
            4
        """
        return len(self._edges)

    def num_loops(self):
        r"""
        Return the number of loops (ie edges attached twice to a vertex).

        EXAMPLES::

            sage: from admcycles import StableGraph
            sage: Gamma = StableGraph([1,1], [[1,2,3,4,5,6],[7,8,9]], [(2,3), (4,5), (6,7), (8,9)])
            sage: Gamma.num_loops()
            3
        """
        n = 0
        for h0, h1 in self._edges:
            n += self.vertex(h0) == self.vertex(h1)
        return n

    def num_legs(self, i=None):
        r"""
        Return the number of legs at vertex i, or the total number of legs
        if i is not specified.

        EXAMPLES::

            sage: from admcycles import StableGraph
            sage: Gamma = StableGraph([0,2], [[1,2,3,4],[6,8]], [(4,6)])
            sage: Gamma.num_legs(0)
            4
            sage: Gamma.num_legs()
            6
        """
        if i is None:
            return sum(len(l) for l in self._legs)
        else:
            return len(self._legs[i])

    def _graph_(self):
        r"""
        Return the Sage graph object encoding the stable graph

        This inserts a vertex with label (i,j) in the middle of the edge (i,j).
        Also inserts a vertex with label ('L',i) at the end of each leg l.

        EXAMPLES::

            sage: from admcycles import StableGraph
            sage: Gr = StableGraph([3,5],[[1,3,5,7],[2]],[(1,2),(3,5)])
            sage: SageGr = Gr._graph_()
            sage: SageGr
            Multi-graph on 5 vertices
            sage: SageGr.vertices(sort=False)   # random
            [(1, 2), 0, 1, (3, 5), ('L', 7)]
        """
        G = Graph(multiedges=True)
        for i, j in self._edges:
            G.add_vertex((i, j))
            G.add_edge((i, j), self.vertex(i))
            G.add_edge((i, j), self.vertex(j))
        for i in self.list_markings():
            G.add_edge(('L', i), self.vertex(i))
        return G

    def dim(self, v=None):
        """
        Return dimension of moduli space at vertex v.

        If v=None, return dimension of entire stratum parametrized by graph.

        EXAMPLES::

            sage: from admcycles import StableGraph
            sage: Gr = StableGraph([3,5],[[1,3,5,7],[2]],[(1,2),(3,5)])
            sage: Gr.dim(0), Gr.dim(1), Gr.dim()
            (10, 13, 23)
        """
        if v is None:
            return sum([self.dim(v) for v in range(len(self._genera))])
        return 3 * self._genera[v] - 3 + len(self._legs[v])

    # TODO: deprecate and remove
    def invariant(self):
        r"""
        Return a graph-invariant in form of a tuple of integers or tuples

        At the moment this assumes that we only compare stable graph with same total
        g and set of markings
        currently returns sorted list of (genus,degree) for vertices

        IDEAS:

        * number of self-loops for each vertex

        EXAMPLES::

            sage: from admcycles import StableGraph
            sage: Gr = StableGraph([3,5],[[1,3,5,7],[2]],[(1,2),(3,5)])
            sage: Gr.invariant()
            ((3, 4, (7,)), (5, 1, ()))
        """
        return tuple(sorted([(self._genera[v], len(self._legs[v]), tuple(sorted(self.list_markings(v)))) for v in range(len(self._genera))]))

    def tidy_up(self):
        r"""
        Sort legs and edges.

        EXAMPLES::

            sage: from admcycles import StableGraph
            sage: S = StableGraph([1, 3, 2], [[1, 5, 4], [2, 3, 6], [9, 8, 7]], [(9,3), (1,2)], mutable=True)
            sage: S.tidy_up()
            sage: S
            [1, 3, 2] [[1, 4, 5], [2, 3, 6], [7, 8, 9]] [(1, 2), (3, 9)]
        """
        if not self._mutable:
            raise ValueError("the graph is immutable; use a copy instead")
        for e in range(len(self._edges)):
            if self._edges[e][0] > self._edges[e][1]:
                self._edges[e] = (self._edges[e][1], self._edges[e][0])
        for legs in self._legs:
            legs.sort()
        self._edges.sort()
        self._maxleg = max([max(j + [0]) for j in self._legs])

    def vertex(self, l):
        r"""
        Return vertex number of leg l.

        EXAMPLES::

            sage: from admcycles import StableGraph
            sage: Gamma = StableGraph([0,2], [[1,2,3,4],[6,8]], [(4,6)])
            sage: Gamma.vertex(1)
            0
            sage: Gamma.vertex(6)
            1
        """
        for v in range(len(self._legs)):
            if l in self._legs[v]:
                return v
        return -1  # self does not have leg l

    def list_markings_symm(self, v=None):
        r"""
        Return the list of markings (non-edge legs) of self at vertex v.

        EXAMPLES::

            sage: from admcycles import StableGraph

            sage: gam = StableGraph([3,5],[[1,3,7],[2,4]],[(1,2)])
            sage: gam.list_markings(0)
            (3, 7)
            sage: gam.list_markings()
            (3, 7, 4)
        """
        if v is None:
            return tuple([j for v in range(len(self._genera))
                          for j in self.list_markings_symm(v)])
        s = []
        for e1, e2 in self._edges:
            s += [e1, e2]
        return tuple([m for m in self._legs[v] if m not in s])

    def list_markings(self, v=None):
        r"""
        Return the list of markings (non-edge legs) of self at vertex v.

        EXAMPLES::

            sage: from admcycles import StableGraph

            sage: gam = StableGraph([3,5],[[1,3,7],[2,4]],[(1,2)])
            sage: gam.list_markings(0)
            (3, 7)
            sage: gam.list_markings()
            (3, 7, 4)
        """
        if v is None:
            return tuple([j for v in range(len(self._genera))
                          for j in self.list_markings(v)])
        s = set(self._legs[v])
        for e in self._edges:
            s -= set(e)
        return tuple(s)

    def leglist(self):
        r"""
        Return the list of legs

        EXAMPLES::

            sage: from admcycles import StableGraph

            sage: gam = StableGraph([3,5],[[1,3,7],[2,4]],[(1,2)])
            sage: gam.leglist()
            [1, 3, 7, 2, 4]
        """
        return [j for leg in self._legs for j in leg]

    def halfedges(self):
        r"""
        Return the tuple containing all half-edges, i.e. legs belonging to an edge

        EXAMPLES::

            sage: from admcycles import StableGraph

            sage: gam = StableGraph([3,5],[[1,3,7],[2,4]],[(1,2)])
            sage: gam.halfedges()
            (1, 2)
        """
        return tuple(j for ed in self._edges for j in ed)

    def edges_between(self, i, j):
        r"""
        Return the list [(l1,k1),(l2,k2), ...] of edges from i to j, where l1 in i, l2 in j; for i==j return each edge only once

        EXAMPLES::

            sage: from admcycles import StableGraph

            sage: gam = StableGraph([3,5],[[1,3,7],[2,4]],[(1,2)])
            sage: gam.edges_between(0, 1)
            [(1, 2)]
            sage: gam.edges_between(0, 0)
            []
        """
        if i == j:
            return [e for e in self._edges if (e[0] in self._legs[i] and e[1] in self._legs[j])]
        else:
            return [e for e in self._edges if (e[0] in self._legs[i] and e[1] in self._legs[j])] + [(e[1], e[0]) for e in self._edges if (e[0] in self._legs[j] and e[1] in self._legs[i])]

    def forget_markings(self, markings):
        r"""
        Erase all legs in the list markings, do not check if this gives well-defined graph

        EXAMPLES::

            sage: from admcycles import StableGraph
            sage: Gamma = StableGraph([0,2], [[1,2,3,4],[6,8]], [(4,6)], mutable=True)
            sage: Gamma.forget_markings([1,3,8])
            [0, 2] [[2, 4], [6]] [(4, 6)]
        """
        if not self._mutable:
            raise ValueError("the graph is not mutable; use a copy instead")
        for m in markings:
            self._legs[self.vertex(m)].remove(m)
        return self

    def leginversion(self, l):
        r"""
        Returns l' if l and l' form an edge, otherwise returns l

        EXAMPLES::

            sage: from admcycles import StableGraph

            sage: gam = StableGraph([3,5],[[1,3,7],[2,4]],[(1,2)])
            sage: gam.leginversion(1)
            2
        """
        for a, b in self._edges:
            if a == l:
                return b
            if b == l:
                return a
        return l

    def stabilize(self):
        r"""
        Stabilize this stable graph.

        (all vertices with genus 0 have at least three markings) and returns
        ``(dicv,dicl,dich)`` where

        - dicv a dictionary sending new vertex numbers to the corresponding old
          vertex numbers

        - dicl a dictionary sending new marking names to the label of the last
          half-edge that they replaced during the stabilization this happens
          for instance if a g=0 vertex with marking m and half-edge l
          (belonging to edge (l,l')) is stabilized: l' is replaced by m, so
          dicl[m]=l'

        - dich a dictionary sending half-edges that vanished in the
          stabilization process to the last half-edge that replaced them this
          happens if a g=0 vertex with two half-edges a,b (whose corresponding
          half-edges are c,d) is stabilized: we obtain an edge (c,d) and a ->
          d, b -> d we assume here that a stabilization exists (all connected
          components have 2g-2+n>0)

        EXAMPLES::

            sage: from admcycles import StableGraph

            sage: gam = StableGraph([3,5],[[1,3,7],[2,4]],[(1,2)], mutable=True)
            sage: gam.stabilize()
            ({0: 0, 1: 1}, {}, {})

            sage: gam = StableGraph([3,5],[[1,3,7],[2,4]],[(1,2)])
            sage: gam.stabilize()
            Traceback (most recent call last):
            ...
            ValueError: the graph is not mutable; use a copy instead

            sage: g = StableGraph([0,0,0], [[1,5,6],[2,3],[4,7,8]], [(1,2),(3,4),(5,6),(7,8)], mutable=True)
            sage: g.stabilize()
            ({0: 0, 1: 2}, {}, {2: 4, 3: 1})
            sage: h = StableGraph([0, 0, 0], [[1], [2,3], [4]], [(1,2), (3,4)], mutable=True)
            sage: h.stabilize()
            ({0: 2}, {}, {})
        """
        if not self._mutable:
            raise ValueError("the graph is not mutable; use a copy instead")
        markings = self.list_markings()
        stable = False
        verteximages = list(range(len(self._genera)))
        dicl = {}
        dich = {}
        while not stable:
            numvert = len(self._genera)
            count = 0
            stable = True
            while count < numvert:
                if self._genera[count] == 0 and len(self._legs[count]) == 1:
                    stable = False
                    e0 = self._legs[count][0]
                    e1 = self.leginversion(e0)
                    v1 = self.vertex(e1)
                    self._genera.pop(count)
                    verteximages.pop(count)
                    numvert -= 1
                    self._legs[v1].remove(e1)
                    self._legs.pop(count)
                    try:
                        self._edges.remove((e0, e1))
                    except ValueError:
                        self._edges.remove((e1, e0))
                elif self._genera[count] == 0 and len(self._legs[count]) == 2:
                    stable = False
                    e0 = self._legs[count][0]
                    e1 = self._legs[count][1]

                    if e1 in markings:
                        swap = e0
                        e0 = e1
                        e1 = swap

                    e1prime = self.leginversion(e1)
                    v1 = self.vertex(e1prime)
                    self._genera.pop(count)
                    verteximages.pop(count)
                    numvert -= 1

                    if e0 in markings:
                        dicl[e0] = e1prime
                        self._legs[v1].remove(e1prime)
                        self._legs[v1].append(e0)
                        self._legs.pop(count)
                        try:
                            self._edges.remove((e1, e1prime))
                        except ValueError:
                            self._edges.remove((e1prime, e1))
                    else:
                        e0prime = self.leginversion(e0)
                        self._legs.pop(count)
                        try:
                            self._edges.remove((e0, e0prime))
                        except ValueError:
                            self._edges.remove((e0prime, e0))
                        try:
                            self._edges.remove((e1, e1prime))
                        except ValueError:
                            self._edges.remove((e1prime, e1))
                        self._edges.append((e0prime, e1prime))

                        # update dich
                        dich[e0] = e1prime
                        dich[e1] = e0prime
                        dich.update({h: e1prime for h in dich if dich[h] == e0})
                        dich.update({h: e0prime for h in dich if dich[h] == e1})
                else:
                    count += 1
        return ({i: verteximages[i] for i in range(len(verteximages))}, dicl, dich)

    def degenerations(self, v=None, mutable=False):
        r"""
        Run through the list of all possible degenerations of this graph.

        A degeneration happens by adding an edge at v or splitting it
        into two vertices connected by an edge the new edge always
        comes last in the list of edges.

        If v is None, return all degenerations at all vertices.

        EXAMPLES::

            sage: from admcycles import StableGraph

            sage: gam = StableGraph([3,5],[[1,3,7],[2,4]],[(1,2)])
            sage: list(gam.degenerations(1))
            [[3, 4] [[1, 3, 7], [2, 4, 8, 9]] [(1, 2), (8, 9)],
             [3, 0, 5] [[1, 3, 7], [2, 4, 8], [9]] [(1, 2), (8, 9)],
             [3, 1, 4] [[1, 3, 7], [8], [2, 4, 9]] [(1, 2), (8, 9)],
             [3, 1, 4] [[1, 3, 7], [2, 8], [4, 9]] [(1, 2), (8, 9)],
             [3, 1, 4] [[1, 3, 7], [4, 8], [2, 9]] [(1, 2), (8, 9)],
             [3, 1, 4] [[1, 3, 7], [2, 4, 8], [9]] [(1, 2), (8, 9)],
             [3, 2, 3] [[1, 3, 7], [8], [2, 4, 9]] [(1, 2), (8, 9)],
             [3, 2, 3] [[1, 3, 7], [2, 8], [4, 9]] [(1, 2), (8, 9)],
             [3, 2, 3] [[1, 3, 7], [4, 8], [2, 9]] [(1, 2), (8, 9)],
             [3, 2, 3] [[1, 3, 7], [2, 4, 8], [9]] [(1, 2), (8, 9)]]

        All these graphs are immutable (or mutable when ``mutable=True``)::

            sage: any(g.is_mutable() for g in gam.degenerations())
            False
            sage: all(g.is_mutable() for g in gam.degenerations(mutable=True))
            True

        TESTS::

            sage: from admcycles import StableGraph
            sage: G = StableGraph([2,2,2], [[1],[2,3],[4]], [(1,2),(3,4)])
            sage: sum(1 for v in range(3) for _ in G.degenerations(v))
            8
            sage: sum(1 for _ in G.degenerations())
            8
        """
        if v is None:
            for v in range(self.num_verts()):
                yield from self.degenerations(v, mutable)
            return

        g = self._genera[v]
        l = len(self._legs[v])

        # for positive genus: add loop to v and decrease genus
        if g > 0:
            G = self.copy()
            G.degenerate_nonsep(v)
            if not mutable:
                G.set_immutable()
            yield G

        # now all graphs with separating edge : separate in (g1,M) and (g-g1,legs[v]-M), take note of symmetry and stability
        for g1 in range(floor(g / 2) + 1):
            for M in Subsets(set(self._legs[v])):
                if (g1 == 0 and len(M) < 2) or \
                   (g == g1 and l - len(M) < 2) or \
                   (2 * g1 == g and l > 0 and (not self._legs[v][0] in M)):
                    continue
                G = self.copy()
                G.degenerate_sep(v, g1, M)
                if not mutable:
                    G.set_immutable()
                yield G

    def newleg(self):
        r"""
        Create two new leg-indices that can be used to create an edge

        This modifies ``self._maxleg``.

        EXAMPLES::

            sage: from admcycles import StableGraph

            sage: gam = StableGraph([3,5],[[1,3,7],[2,4]],[(1,2)])
            sage: gam.newleg()
            (8, 9)
        """
        self._maxleg += 2
        return (self._maxleg - 1, self._maxleg)

    def rename_legs(self, dic, shift=None, inplace=True, return_dicts=False, mutable=False, tidyup=True):
        r"""
        Rename the markings according to the dictionary ``dic``.

        Return a new stable graph which is isomorphic to self up to the
        change of markings given in ``dic``.

        If ``return_dicts`` is set to ``True``, return a triple
        ``(new_stable_graph, markings_relabelling, all_legs_relabelling)``
        where

        - ``markings_relabelling`` is the dictionary whose keys are the marking of
          the current graph and the values are the new markings

        - ``all_legs_relabelling`` is a dictionary of all the marking relabelling
          (this argument could be forwarded to :meth:`StableGraph.relabel`)

        INPUT:

        dic : dictionary
          the relabeling old label -> new label

        shift : integer
          if provided, perform the corresponding shift on the non-marked legs

        inplace : boolean (default ``True``)
          whether to do an inplace modification or return a new stable graph

        return_dicts : boolean
          whether to return the extra relabelling information

        mutable : boolean (default ``False``)
          whether the return graph should be mutable (ignored when ``inplace=True``)

        EXAMPLES::

            sage: from admcycles import StableGraph

            sage: g = StableGraph([0], [[1,2]], [], mutable=True)
            sage: g.rename_legs({1: 3})
            [0] [[2, 3]] []

            sage: g = StableGraph([0, 0], [[1,3,4],[2,5]], [(4,5)], mutable=True)
            sage: gg, rel, extra = g.rename_legs({1:2, 2:1}, return_dicts=True)
            sage: gg
            [0, 0] [[2, 3, 4], [1, 5]] [(4, 5)]
            sage: rel == {1: 2, 2: 1, 3: 3}
            True

        A graph involving some changes in non-marking legs::

            sage: g = StableGraph([0, 0], [[1, 4], [2, 3, 5]], [(4, 5)])
            sage: g.rename_legs({1: 2, 2: 4, 3: 6}, inplace=False)
            [0, 0] [[1, 2], [4, 5, 6]] [(1, 5)]
            sage: gg, markings_dic, legs_dic = g.rename_legs({1: 2, 2: 4, 3: 6}, inplace=False, return_dicts=True)
            sage: gg
            [0, 0] [[1, 2], [4, 5, 6]] [(1, 5)]
            sage: markings_dic == {1: 2, 2: 4, 3: 6}
            True
            sage: legs_dic == {1: 2, 2: 4, 3: 6, 4: 1, 5: 5}
            True

        Using the ``shift`` argument::

            sage: g = StableGraph([0], [[1, 2, 3]], [(2, 3)], mutable=True)
            sage: g.rename_legs({1: 5}, shift=1, inplace=False)
            [0] [[3, 4, 5]] [(3, 4)]
            sage: gg, markings_dic, legs_dic = g.rename_legs({1: 5}, shift=1, inplace=False, return_dicts=True)
            sage: gg
            [0] [[3, 4, 5]] [(3, 4)]
            sage: markings_dic == {1: 5}
            True
            sage: legs_dic == {1: 5, 2: 3, 3: 4}
            True

        This method forbids renaming internal legs (for that purpose use :meth:`relabel`)::

            sage: g = StableGraph([0], [[1,2,3]], [(2,3)], mutable=True)
            sage: g.rename_legs({2:5})
            Traceback (most recent call last):
            ...
            ValueError: non-marking legs [2] in dic (use the relabel method instead)
        """
        # 1. compute an admissible relabelling of the legs
        markings = self.list_markings()
        markings_relabelling = {i: dic.get(i, i) for i in markings}
        bad_legs = [i for i in dic if i not in markings]
        if bad_legs:
            raise ValueError('non-marking legs {} in dic (use the relabel method instead)'.format(bad_legs))

        if shift is not None:
            # replace v[j] by markings_relabelling[v[j]] if v[j] in markings_relabelling and leave at v[j] otherwise
            all_legs_relabelling = {i: i + shift for e in self._edges for i in e}
            all_legs_relabelling.update(markings_relabelling)
        else:
            image_markings = tuple(sorted(markings_relabelling.values()))
            if markings == image_markings:
                # no need to modify any non-marking leg
                all_legs_relabelling = {i: i for e in self._edges for i in e}
                all_legs_relabelling.update(markings_relabelling)
            else:
                # find a minimal relabelling avoiding collisions by recycling the forgotten markings
                k = 0
                forget = [i for i in markings if i not in image_markings]
                all_legs = []
                for l in self._legs:
                    all_legs.extend(l)
                all_legs_relabelling = {i: i for e in self._edges for i in e}
                for i in image_markings:
                    if i in markings or i not in all_legs_relabelling:
                        continue
                    # exchange i with an unused marking
                    all_legs_relabelling[i] = forget[k]
                    k += 1
                all_legs_relabelling.update(markings_relabelling)

        # 2. actually perform the relabelling
        if inplace:
            result = self
            result.relabel({}, all_legs_relabelling, inplace=True)
            if tidyup:  # by default it will sort the list of legs and edges
                result.tidy_up()
        else:
            result = self.relabel({}, all_legs_relabelling, inplace=False, mutable=True)
            if tidyup:  # by default it will sort the list of legs and edges
                result.tidy_up()
            if not mutable:
                result.set_immutable()

        # 3. return the result
        return (result, markings_relabelling, all_legs_relabelling) if return_dicts else result

    def degenerate_sep(self, v, g1, M):
        r"""
        degenerate vertex v into two vertices with genera g1 and g(v)-g1 and legs M and complement

        add new edge (e[0],e[1]) such that e[0] is in new vertex v, e[1] in last vertex, which is added

        EXAMPLES::

            sage: from admcycles import StableGraph

            sage: G = StableGraph([3,5],[[1,3,7],[2,4]],[(1,2)], mutable=True)
            sage: G.degenerate_sep(1, 2, [4])
            sage: G
            [3, 2, 3] [[1, 3, 7], [4, 8], [2, 9]] [(1, 2), (8, 9)]

            sage: G = StableGraph([3,5],[[1,3,7],[2,4]],[(1,2)])
            sage: G.degenerate_sep(1, 2, [4])
            Traceback (most recent call last):
            ...
            ValueError: the graph is not mutable; use a copy instead
        """
        if not self._mutable:
            raise ValueError("the graph is not mutable; use a copy instead")
        g = self._genera[v]
        oldleg = self._legs[v]
        e = self.newleg()

        self._genera[v] = g1
        self._genera += [g - g1]
        self._legs[v] = list(M) + [e[0]]
        self._legs += [sorted(set(oldleg) - set(M)) + [e[1]]]
        self._edges += [e]

    def degenerate_nonsep(self, v):
        """
        EXAMPLES::

            sage: from admcycles import StableGraph

            sage: G = StableGraph([3,5],[[1,3,7],[2,4]],[(1,2)], mutable=True)
            sage: G.degenerate_nonsep(1)
            sage: G
            [3, 4] [[1, 3, 7], [2, 4, 8, 9]] [(1, 2), (8, 9)]

            sage: G = StableGraph([3,5],[[1,3,7],[2,4]],[(1,2)])
            sage: G.degenerate_nonsep(1)
            Traceback (most recent call last):
            ...
            ValueError: the graph is not mutable; use a copy instead
        """
        if not self._mutable:
            raise ValueError("the graph is not mutable; use a copy instead")
        e = self.newleg()
        self._genera[v] -= 1
        self._legs[v] += [e[0], e[1]]
        self._edges += [e]

    def contract_edge(self, e, adddata=False):
        r"""
        Contracts the edge e=(e0,e1) or the list of edges e.

        This method returns nothing by default. But if ``adddata`` is set to
        ``True``, then it returns a tuple ``(av, edgegraph, vnum)`` where

          - ``av`` is the the vertex in the modified graph on which previously
            the edge ``e`` had been attached

          - ``edgegraph`` is a stable graph induced in self by the edge e
            (1-edge graph, all legs at the ends of this edge are considered as
            markings)

          - ``vnum`` is a list of one or two vertices e was attached before the
            contraction (in the order in which they appear)

          - ``diccv`` is a dictionary mapping old vertex numbers to new vertex
            numbers

        When e is a list of edges, only ``diccv`` is returned.

        EXAMPLES::

            sage: from admcycles import StableGraph

            sage: G = StableGraph([3,5],[[1,3,7],[2,4]],[(1,2),(3,7)], mutable=True)
            sage: G.contract_edge((1,2))
            sage: G
            [8] [[3, 7, 4]] [(3, 7)]
            sage: G.contract_edge((3,7))
            sage: G
            [9] [[4]] []

            sage: G2 = StableGraph([3,5],[[1,3,7],[2,4]],[(1,2),(3,7)], mutable=True)
            sage: G2.contract_edge((3,7))
            sage: G2.contract_edge((1,2))
            sage: G == G2
            True

            sage: G2 = StableGraph([3,5],[[1,3,7],[2,4]],[(1,2),(3,7)], mutable=True)
            sage: G2.contract_edge((3,7), adddata=True)
            (0, [3] [[1, 3, 7]] [(3, 7)], [0], {0: 0, 1: 1})

            sage: G = StableGraph([1,1,1,1],[[1],[2,4],[3,5],[6]],[(1,2),(3,4),(5,6)],mutable=True)
            sage: G.contract_edge((3,4),True)
            (1, [1, 1] [[2, 4], [3, 5]] [(3, 4)], [1, 2], {0: 0, 1: 1, 2: 1, 3: 2})

            sage: G = StableGraph([3,5],[[1,3,7],[2,4]],[(1,2)])
            sage: G.contract_edge((1,2))
            Traceback (most recent call last):
            ...
            ValueError: the graph is not mutable; use a copy instead

        Contracting multiple edges at once::

            sage: from admcycles import StableGraph
            sage: G = StableGraph([0,1,2],[[1,2,3,4],[5,6],[7]],[(2,3),(4,5),(6,7)],mutable=True)
            sage: G.contract_edge([(2,3),(4,5)],adddata=True)
            {0: 0, 1: 0, 2: 1}
            sage: G
            [2, 2] [[1, 6], [7]] [(6, 7)]
            sage: G.contract_edge([(6,7)])
            sage: G
            [4] [[1]] []
            sage: G.contract_edge([],adddata=True)
            {0: 0}
        """
        if not self._mutable:
            raise ValueError("the graph is not mutable; use a copy instead")

        if len(e) == 0 or isinstance(e[0], tuple):
            # e is a list of edges
            if adddata:
                diccv = {i: i for i in range(self.num_verts())}
                for ed in e:
                    _, _, _, dicnew = self.contract_edge(ed, adddata=True)
                    diccv = {i: dicnew[diccv[i]] for i in diccv}
                return diccv
            for ed in e:
                self.contract_edge(ed)
            return None

        v0 = self.vertex(e[0])
        v1 = self.vertex(e[1])

        if v0 == v1:  # contracting a loop
            if adddata:
                H = StableGraph([self._genera[v0]], [self._legs[v0][:]], [e])
            self._genera[v0] += 1
            self._legs[v0].remove(e[0])
            self._legs[v0].remove(e[1])
            self._edges.remove(e)

            if adddata:
                return (v0, H, [v0], {v: v for v in range(len(self._genera))})

        else:  # contracting an edge between different vertices
            if v0 > v1:
                v0, v1 = v1, v0

            if adddata:
                diccv = {v: v for v in range(v1)}
                diccv[v1] = v0
                diccv.update({v: v - 1 for v in range(v1 + 1, len(self._genera))})
                H = StableGraph([self._genera[v0], self._genera[v1]], [self._legs[v0][:], self._legs[v1][:]], [e])

            g1 = self._genera.pop(v1)
            self._genera[v0] += g1
            l1 = self._legs.pop(v1)
            self._legs[v0] += l1
            self._legs[v0].remove(e[0])
            self._legs[v0].remove(e[1])
            self._edges.remove(e)

            if adddata:
                return (v0, H, [v0, v1], diccv)

    def glue_vertex(self, i, Gr, divGr={}, divs={}, dil={}):
        r"""
        Glues the stable graph ``Gr`` at the vertex ``i`` of this stable graph

        optional arguments: if divGr/dil are given they are supposed to be a
        dictionary, which will be cleared and updated with the
        renaming-convention to pass from leg/vertex-names in Gr to
        leg/vertex-names in the glued graph similarly, divs will be a
        dictionary assigning vertex numbers in the old self the corresponding
        number in the new self necessary condition:

        - every leg of i is also a leg in Gr
        - every leg of Gr that is not a leg of i in self gets a new name

        EXAMPLES::

            sage: from admcycles import StableGraph
            sage: Gamma = StableGraph([2,1], [[1,2,3,4],[5]], [(2,3),(4,5)], mutable=True)
            sage: Gr = StableGraph([0,1,1], [[1,2,5],[6,3,7],[8,4]], [(5,6),(7,8)])
            sage: divGr=dict()
            sage: divs=dict()
            sage: dil=dict()
            sage: Gamma.glue_vertex(0, Gr, divGr, divs, dil)
            sage: Gamma
            [1, 0, 1, 1] [[5], [1, 2, 10], [3, 11, 12], [4, 9]] [(4, 5), (9, 12), (10, 11)]
            sage: divGr
            {0: 1, 1: 2, 2: 3}
            sage: divs
            {1: 0}
            sage: dil
            {5: 10, 6: 11, 7: 12, 8: 9}
        """
        if not self._mutable:
            raise ValueError("the graph is not mutable; use a copy instead")

        divGr.clear()
        divs.clear()
        dil.clear()

        # remove vertex i, legs corresponding to it and all self-edges
        selfedges_old = self.edges_between(i, i)
        self._genera.pop(i)
        legs_old = self._legs.pop(i)
        for e in selfedges_old:
            self._edges.remove(e)

        # when gluing in Gr, make sure that new legs corresponding to edges inside Gr
        # or legs in Gr which are already attached to a vertex different from i in self get a new unique label in the glued graph
        m = max(self._maxleg, Gr._maxleg)  # largest index used in either graph, new labels m+1, m+2, ...

        Gr_new = Gr.copy()

        a = []
        for l in Gr._legs:
            a += l
        a = set(a)    # legs of Gr
        b = set(legs_old)  # legs of self at vertex i

        # set of legs of Gr that need to be relabeled: all legs of Gr that are not attached to vertex i in self
        e = a - b
        for l in e:
            m += 1
            dil[l] = m
        Gr_new.relabel({}, dil, inplace=True)

        # vertex dictionaries
        for j in range(i):
            divs[j] = j
        for j in range(i + 1, len(self._genera) + 1):
            divs[j] = j - 1
        for j in range(len(Gr._genera)):
            divGr[j] = len(self._genera) + j

        self._genera += Gr_new._genera
        self._legs += Gr_new._legs
        self._edges += Gr_new._edges

        self.tidy_up()

    def subset_valence(self, V):
        r"""
        Computes the number of edges between V and its complement,
        for V a subset of the vertices of the StableGraph.

        INPUT:

        - ``V`` -- (list) List of vertices of the StableGraph.

        EXAMPLES::

            sage: from admcycles.logtaut import *
            sage: PG = PicGraph([1,2,1],[[1,2],[3,4],[5]],[(2,3),(4,5)], [4,-1,-1])
            sage: PG.subset_valence([0])
            1
        """
        if len(V) == len(self.genera()) or len(V) == 0:
            return ZZ(0)
        # return self.extract_subgraph(V)[0].edges()
        EV = len((self.extract_subgraph(V)[0]).edges())
        Vc = [i for i in range(len(self.genera())) if i not in V]
        EVc = len((self.extract_subgraph(Vc)[0]).edges())
        return len(self.edges()) - EV - EVc

    # TODO: overlaps with relabel
    def reorder_vertices(self, vord):
        r"""
        Reorders vertices according to tuple given (permutation of range(len(self._genera)))
        """
        if not self._mutable:
            raise ValueError("the graph is not mutable; use a copy instead")
        new_genera = [self._genera[j] for j in vord]
        new_legs = [self._legs[j] for j in vord]
        self._genera = new_genera
        self._legs = new_legs

    def extract_subgraph(self, vertices, outgoing_legs=None, rename=True, mutable=False):
        r"""
        Extracts from self a subgraph induced by the list vertices

        if the list outgoing_legs is given, the markings of the subgraph are
        called 1,2,..,m corresponding to the elements of outgoing_legs in this
        case, all edges involving outgoing edges should be cut returns a triple
        (Gamma,dicv,dicl), where

        - Gamma is the induced subgraph

        - dicv, dicl are (surjective) dictionaries associating vertex/leg
          labels in self to the vertex/leg labels in Gamma

        if ``rename=False``, do not rename any legs when extracting

        EXAMPLES::

            sage: from admcycles import StableGraph

            sage: gam = StableGraph([3,5],[[1,3,7],[2,4]],[(1,2)])
            sage: gam.extract_subgraph([0])
            ([3] [[1, 2, 3]] [], {0: 0}, {1: 1, 3: 2, 7: 3})
        """
        attachedlegs = {l for v in vertices for l in self._legs[v]}
        if outgoing_legs is None:
            alllegs = attachedlegs.copy()
            for (e0, e1) in self._edges:
                if e0 in alllegs and e1 in alllegs:
                    alllegs.remove(e0)
                    alllegs.remove(e1)
            outgoing_legs = list(alllegs)

        shift = len(outgoing_legs) + 1
        if rename:
            dicl = {outgoing_legs[i]: i + 1 for i in range(shift - 1)}
        else:
            dicl = {l: l for l in self.leglist()}

        genera = [self._genera[v] for v in vertices]
        legs = [[dicl.setdefault(l, l + shift) for l in self._legs[v]] for v in vertices]
        edges = [(dicl[e0], dicl[e1]) for (e0, e1) in self._edges if (
            e0 in attachedlegs and e1 in attachedlegs and (e0 not in outgoing_legs) and (e1 not in outgoing_legs))]
        dicv = {vertices[i]: i for i in range(len(vertices))}

        return (StableGraph(genera, legs, edges, mutable=mutable), dicv, dicl)

    def vanishes(self, moduli):
        if moduli == MODULI_ST:
            return False
        elif moduli == MODULI_TL:
            return self.num_edges() - self.num_loops() != self.num_verts() - 1
        elif moduli == MODULI_CT:
            return self.num_edges() != self.num_verts() - 1
        elif moduli == MODULI_RT:
            return (self.num_edges() != self.num_verts() - 1) or \
                sum(bool(g) for g in self._genera) != 1
        elif moduli == MODULI_SM:
            return bool(self._edges)
        else:
            raise ValueError('unknown moduli')

    def boundary_pushforward(self, classes=None):
        r"""
        Computes the pushforward of a product of tautological classes (one for each vertex) under the
        boundary gluing map for this stable graph.

        INPUT:

        - ``classes``  -- list (default: `None`); list of tautclasses, one for each vertex of the stable
          graph. The genus of the ith class is assumed to be the genus of the ith vertex, the markings
          of the ith class are supposed to be 1, ..., ni where ni is the number of legs at the ith vertex.
          Note: the jth leg at vertex i corresponds to the marking j of the ith class.
          For classes=None, place the fundamental class at each vertex.

        EXAMPLES::

            sage: from admcycles import StableGraph, TautologicalRing
            sage: B=StableGraph([2,1],[[4,1,2],[3,5]],[(4,5)])
            sage: Bclass=B.boundary_pushforward() # class of undecorated boundary divisor
            sage: Bclass*Bclass
            Graph :      [2, 1] [[4, 1, 2], [3, 5]] [(4, 5)]
            Polynomial : -psi_5 - psi_4
            sage: R1 = TautologicalRing(2,3)
            sage: R2 = TautologicalRing(1,2)
            sage: si1=B.boundary_pushforward([R1.fundamental_class(),-R2.psi(2)]); si1
            Graph :      [2, 1] [[4, 1, 2], [3, 5]] [(4, 5)]
            Polynomial : -psi_5
            sage: si2=B.boundary_pushforward([-R1.psi(1), R2.fundamental_class()]); si2
            Graph :      [2, 1] [[4, 1, 2], [3, 5]] [(4, 5)]
            Polynomial : -psi_4
            sage: a = Bclass*Bclass-si1-si2
            sage: a.simplify()
            0
        """
        from .admcycles import prodtautclass
        return prodtautclass(self.copy(mutable=False), protaut=classes).pushforward()

    # TODO: adapt to TautologicalRing
    def boundary_pullback(self, other):
        r"""
        Pulls back the TautologicalClass or decstratum other to self and
        returns a prodtautclass with gamma=self.

        EXAMPLES::

            sage: from admcycles import StableGraph, psiclass
            sage: G = StableGraph([0, 2], [[1, 2, 4, 3], [5]], [(3, 5)])
            sage: H = StableGraph([2],[[1,2,4]],[])
            sage: a = H.boundary_pushforward([psiclass(3,2,3)]); a
            Graph :      [2] [[1, 2, 4]] []
            Polynomial : psi_4
            sage: G.boundary_pullback(a)
            Outer graph : [0, 2] [[1, 2, 4, 3], [5]] [(3, 5)]
            Vertex 0 :
            Graph :      [0] [[1, 2, 3, 4]] []
            Polynomial : psi_3
            Vertex 1 :
            Graph :      [2] [[1]] []
            Polynomial : 1
        """
        from .tautological_ring import TautologicalClass
        from .admcycles import decstratum

        if isinstance(other, TautologicalClass):
            from .admcycles import prodtautclass
            result = prodtautclass(self.copy(mutable=False), [])
            for t in other._terms.values():
                result += self.boundary_pullback(t)
            return result
        elif isinstance(other, decstratum):
            # NOTE: this is using much more than just stable graphs
            # I would suggest to move it out of this class
            from .admcycles import (common_degenerations, prodtautclass,
                                    onekppoly, kppoly, kappacl, psicl)
            rename = not (set(self.list_markings()) == set(range(1, self.n() + 1)))
            commdeg = common_degenerations(self, other.gamma, modiso=True, rename=rename)
            result = prodtautclass(self.copy(mutable=False), [])

            for (Gamma, dicv1, dicl1, dicv2, dicl2) in commdeg:
                numvert = len(Gamma._genera)
                # first determine edges that are covered by self and other - for excess int. terms
                legcount = {l: 0 for l in Gamma.leglist()}
                for l in dicl1.values():
                    legcount[l] += 1
                for l in dicl2.values():
                    legcount[l] += 1

                excesspoly = onekppoly(numvert)
                for e in Gamma._edges:
                    if legcount[e[0]] == 2:
                        excesspoly *= ((-1) * (psicl(e[0], numvert) + psicl(e[1], numvert)))

                # partition vertices of Gamma according to where they go in self
                v1preim = [[] for v in range(len(self._genera))]
                for w in dicv1:
                    v1preim[dicv1[w]].append(w)

                graphpartition = [Gamma.extract_subgraph(
                    v1preim[v], outgoing_legs=[dicl1[l] for l in self._legs[v]]) for v in range(len(self._genera))]

                v2preim = [[] for v in range(len(other.gamma._genera))]
                for w in dicv2:
                    v2preim[dicv2[w]].append(w)

                resultpoly = kppoly([], [])
                # now the stage is set to go through the polynomial of other term by term, pull them back according to dicv2, dicl2 and also add the excess-intersection terms
                for (kappa, psi, coeff) in other.poly:
                    # psi-classes are transferred by dicl2, but kappa-classes might be split up if dicv2 has multiple preimages of same vertex
                    # multiply everything together in a kppoly on Gamma, then split up this polynomial according to graphpartition
                    psipolydict = {dicl2[l]: psi[l] for l in psi}
                    psipoly = kppoly([([[] for i in range(numvert)], psipolydict)], [1])

                    kappapoly = prod([prod([sum([kappacl(w, k + 1, numvert) for w in v2preim[v]])**kappa[v][k]
                                     for k in range(len(kappa[v]))]) for v in range(len(other.gamma._genera))])

                    resultpoly += coeff * psipoly * kappapoly

                resultpoly *= excesspoly
                # TODO: filter for terms that vanish by dimension reasons?

                # now fiddle the terms of resultpoly apart and distribute them to graphpartition
                for (kappa, psi, coeff) in resultpoly:
                    decstratlist = []
                    for v in range(len(self._genera)):
                        kappav = [kappa[w] for w in v1preim[v]]
                        psiv = {graphpartition[v][2][l]: psi[l] for l in graphpartition[v][2] if l in psi}
                        decstratlist.append(decstratum(graphpartition[v][0], kappa=kappav, psi=psiv))
                    tempresu = prodtautclass(self, [decstratlist])
                    tempresu *= coeff
                    result += tempresu
            return result
        else:
            raise TypeError('invalid input other={}'.format(other))

    def to_tautological_class(self, R=None):
        r"""
        Return the pure boundary stratum associated to this stable graph.

        Note: does not divide by automorphisms!

        EXAMPLES::

            sage: from admcycles import StableGraph

            sage: g = StableGraph([0,0], [[1,3,4], [2,5,6]], [(3,5),(4,6)])
            sage: g.to_tautological_class()
            Graph :      [0, 0] [[1, 3, 4], [2, 5, 6]] [(3, 5), (4, 6)]
            Polynomial : 1

        TESTS::

             sage: from admcycles import StableGraph

            sage: g = StableGraph([0,0], [[1,3,4], [2,5,6]], [(3,5),(4,6)])
            sage: g.to_tautclass()
            doctest:...: DeprecationWarning: to_tautclass is deprecated. Please use to_tautological_class instead.
            See https://gitlab.com/modulispaces/admcycles/-/merge_requests/109 for details.
            Graph :      [0, 0] [[1, 3, 4], [2, 5, 6]] [(3, 5), (4, 6)]
            Polynomial : 1
       """
        if R is None:
            from .tautological_ring import TautologicalRing
            R = TautologicalRing(self.g(), self.n())
        return R(self)

    to_tautclass = deprecated_function_alias(109, to_tautological_class)

    def _vertex_module(self):
        nv = len(self._genera)
        return FreeModule(ZZ, nv)

    def _edge_module(self):
        ne = len(self._edges)
        return FreeModule(ZZ, ne)

    # TODO: implement cache as this is used intensively in the flow code below
    # See https://gitlab.com/modulispaces/admcycles/issues/14
    def spanning_tree(self, root=0):
        r"""
        Return a spanning tree.

        INPUT:

        - ``root`` - optional vertex for the root of the spanning tree

        OUTPUT: a triple

        - list of triples ``(vertex ancestor, sign, edge index)`` where the
          triple at position ``i`` correspond to vertex ``i``.

        - the set of indices of extra edges not in the tree

        - vertices sorted according to their heights in the tree (first element is the root
          and the end of the list are the leaves). In other words, a topological sort of
          the vertices with respect to the spanning tree.

        EXAMPLES::

            sage: from admcycles import StableGraph
            sage: G = StableGraph([0,0,0], [[1,2],[3,4,5],[6,7]], [(1,3),(4,6),(5,7)])
            sage: G.spanning_tree()
            ([None, (0, -1, 0), (1, -1, 1)], {2}, [0, 1, 2])
            sage: G.spanning_tree(1)
            ([(1, 1, 0), None, (1, -1, 1)], {2}, [1, 0, 2])
            sage: G.spanning_tree(2)
            ([(1, 1, 0), (2, 1, 1), None], {2}, [2, 1, 0])
        """
        from collections import deque

        nv = len(self._genera)
        ne = len(self._edges)

        out_edges = [[] for _ in range(nv)]
        for i, (lu, lv) in enumerate(self._edges):
            u = self.vertex(lu)
            v = self.vertex(lv)
            out_edges[u].append((v, -1, i))
            out_edges[v].append((u, 1, i))

        ancestors = [None] * nv
        ancestors[root] = None
        unseen = [True] * nv
        unseen[root] = False
        todo = deque()
        todo.append(root)
        extra_edges = set(range(ne))
        vertices = [root]

        while todo:
            u = todo.popleft()
            for v, s, i in out_edges[u]:
                if unseen[v]:
                    ancestors[v] = (u, s, i)
                    todo.append(v)
                    unseen[v] = False
                    extra_edges.remove(i)
                    vertices.append(v)

        return ancestors, extra_edges, vertices

    def cycle_basis(self):
        r"""
        Return a basis of the cycles as vectors of length the number of edges in the graph.

        The coefficient at a given index in a vector corresponds to the edge
        of this index in the list of edges of the stable graph. The coefficient is
        +1 or -1 depending on the orientation of the edge in the cycle.

        EXAMPLES::

            sage: from admcycles import StableGraph
            sage: G = StableGraph([0,0,0], [[1,2,3], [4,5,6], [7,8]], [(1,4),(5,2),(3,7),(6,8)])
            sage: G.cycle_basis()
            [(1, 1, 0, 0), (1, 0, -1, 1)]
        """
        ne = len(self._edges)
        V = self._edge_module()

        ancestors, extra_edges, _ = self.spanning_tree()
        basis = []

        for i in extra_edges:
            vec = [0] * ne

            # contribution of the edge
            vec[i] = 1

            lu, lv = self._edges[i]
            u = self.vertex(lu)
            v = self.vertex(lv)

            # contribution of the path from root to u
            while ancestors[u] is not None:
                u, s, i = ancestors[u]
                vec[i] -= s

            # contribution of the path from v to root
            while ancestors[v] is not None:
                v, s, i = ancestors[v]
                vec[i] += s

            basis.append(V(vec))

        return basis

    def cycle_space(self):
        r"""
        Return the subspace of the edge module generated by the cycles.

        EXAMPLES::

            sage: from admcycles import StableGraph
            sage: G = StableGraph([0,0,0], [[1,2,3], [4,5,6], [7,8]], [(1,4),(5,2),(3,7),(6,8)])
            sage: C = G.cycle_space()
            sage: C
            Free module of degree 4 and rank 2 over Integer Ring
            Echelon basis matrix:
            [ 1  0 -1  1]
            [ 0  1  1 -1]
            sage: G.flow_divergence(C.random_element()).is_zero()
            True
        """
        return self._edge_module().submodule(self.cycle_basis())

    def flow_divergence(self, flow):
        r"""
        Return the divergence of the given ``flow``.

        The divergence at a given vertex is the sum of the flow on the outgoing
        edges at this vertex.

        EXAMPLES::

            sage: from admcycles import StableGraph
            sage: G = StableGraph([1,0,0], [[1,2],[3,4,5,6],[7,8]], [(1,3),(4,2),(5,8),(7,6)])
            sage: G.flow_divergence([1,1,1,1])
            (0, 0, 0)
            sage: G.flow_divergence([1,0,0,0])
            (1, -1, 0)
        """
        flow = self._edge_module()(flow)
        deriv = self._vertex_module()()
        for i, (lu, lv) in enumerate(self._edges):
            u = self.vertex(lu)
            v = self.vertex(lv)
            deriv[u] += flow[i]
            deriv[v] -= flow[i]

        return deriv

    def flow_solve(self, vertex_weights):
        r"""
        Return a solution for the flow equation with given vertex weights.

        EXAMPLES::

            sage: from admcycles import StableGraph

            sage: G = StableGraph([0,0,0], [[1,2,3], [4,5,6], [7,8]], [(1,4),(5,2),(3,7),(6,8)])
            sage: flow = G.flow_solve((-3, 2, 1))
            sage: flow
            (-2, 0, -1, 0)
            sage: G.flow_divergence(flow)
            (-3, 2, 1)
            sage: div = vector((-34, 27, 7))
            sage: flow = G.flow_solve(div)
            sage: G.flow_divergence(flow) == div
            True
            sage: C = G.cycle_space()
            sage: G.flow_divergence(flow + C.random_element()) == div
            True

            sage: G = StableGraph([0,0,0], [[1],[2,3],[4]], [(1,2),(3,4)])
            sage: G.flow_solve((-1, 0, 1))
            (-1, -1)
            sage: G.flow_divergence((-1, -1))
            (-1, 0, 1)
            sage: G.flow_solve((-1, 3, -2))
            (-1, 2)
            sage: G.flow_divergence((-1, 2))
            (-1, 3, -2)

        TESTS::

            sage: V = ZZ**4
            sage: vectors = [V((-1, 0, 0, 1)), V((-3, 1, -2, 4)), V((5, 2, -13, 6))]
            sage: G1 = StableGraph([0,0,0,0], [[1], [2,3], [4,5], [6]], [(1,2), (3,4), (5,6)])
            sage: G2 = StableGraph([0,0,0,0], [[1], [2,3], [4,5], [6]], [(1,2), (3,4), (6,5)])
            sage: G3 = StableGraph([0,0,0,0], [[1], [2,3], [4,5], [6]], [(2,1), (3,4), (6,5)])
            sage: G4 = StableGraph([0,0,0,0], [[1], [2,3], [4,5], [6]], [(1,2), (4,3), (5,6)])
            sage: for G in [G1,G2,G3,G4]:
            ....:     for v in vectors:
            ....:         flow = G.flow_solve(v)
            ....:         assert G.flow_divergence(flow) == v, (v,flow,G)

            sage: V = ZZ**6
            sage: G = StableGraph([0,0,0,0,0,0], [[1,5], [2,3], [4,6,7,10], [8,9,11,13], [14,16], [12,15]], [(1,2),(4,3),(5,6),(7,8),(9,10),(12,11),(13,14),(15,16)])
            sage: for _ in range(10):
            ....:     v0 = V.random_element()
            ....:     for u in V.basis():
            ....:         v = v0 - sum(v0) * u
            ....:         flow = G.flow_solve(v)
            ....:         assert G.flow_divergence(flow) == v, (v, flow)
        """
        # NOTE: if we compute the divergence matrix, one can also use solve_right
        # directly. It might be faster on some large instances.
        nv = len(self._genera)
        if len(vertex_weights) != nv or sum(vertex_weights) != 0:
            raise ValueError("vertex_weights must have length nv and sum up to zero")

        ancestors, _, vertices = self.spanning_tree()
        vertices.reverse()   # move leaves first and root last
        vertices.pop()       # remove the root

        new_vertex_weights = self._vertex_module()(vertex_weights)
        if new_vertex_weights is vertex_weights and vertex_weights.is_mutable():
            new_vertex_weights = vertex_weights.__copy__()
        vertex_weights = new_vertex_weights

        V = self._edge_module()
        vec = V()
        for u in vertices:
            v, s, i = ancestors[u]
            vec[i] += s * vertex_weights[u]
            vertex_weights[v] += vertex_weights[u]

        return vec

    def plot(self, vord=None, vpos=None, eheight=None):
        r"""
        Return a graphics object in which ``self`` is plotted.

        If ``vord`` is ``None``, the method uses the default vertex order.

        If ``vord`` is ``[]``, the parameter ``vord`` is used to give back the vertex order.

        EXAMPLES::

            sage: from admcycles import *
            sage: G = StableGraph([1,2],[[1,2],[3,4,5,6]],[(1,3),(2,4)])
            sage: G.plot()
            Graphics object consisting of 12 graphics primitives

        TESTS::

            sage: from admcycles import *
            sage: G = StableGraph([1,2],[[1,2],[3,4,5,6]],[(1,3),(2,4)])
            sage: vertex_order = []
            sage: P =  G.plot(vord=vertex_order)
            sage: vertex_order
            [0, 1]
        """
        # some parameters
        mark_dx = 1       # x-distance of different markings
        mark_dy = 1       # y-distance of markings from vertices
        mark_rad = 0.2    # radius of marking-circles
        v_dxmin = 1       # minimal x-distance of two vertices
        ed_dy = 0.7       # max y-distance of different edges between same vertex-pair

        vsize = 0.4       # (half the) size of boxes representing vertices

        if not vord:
            default_vord = list(range(len(self._genera)))
            if vord is None:
                vord = default_vord
            else:
                vord += default_vord
        reord_self = self.copy()
        reord_self.reorder_vertices(vord)

        if not vpos:
            default_vpos = [(0, 0)]
            for i in range(1, len(self._genera)):
                default_vpos += [(default_vpos[i - 1][0] + mark_dx * (len(reord_self.list_markings(i - 1)) + 2 * len(reord_self.edges_between(
                    i - 1, i - 1)) + len(reord_self.list_markings(i)) + 2 * len(reord_self.edges_between(i, i))) / ZZ(2) + v_dxmin, 0)]
            if vpos is None:
                vpos = default_vpos
            else:
                vpos += default_vpos

        if not eheight:
            ned = {(i, j): 0 for i in range(len(reord_self._genera)) for j in range(i + 1, len(reord_self._genera))}
            default_eheight = {}
            for e in reord_self._edges:
                ver1 = reord_self.vertex(e[0])
                ver2 = reord_self.vertex(e[1])
                if ver1 != ver2:
                    default_eheight[e] = abs(ver1 - ver2) - 1 + ned[(min(ver1, ver2), max(ver1, ver2))] * ed_dy
                    ned[(min(ver1, ver2), max(ver1, ver2))] += 1

            if eheight is None:
                eheight = default_eheight
            else:
                eheight.update(default_eheight)

        # now the drawing starts
        # vertices
        vertex_graph = [polygon2d([[vpos[i][0] - vsize, vpos[i][1] - vsize], [vpos[i][0] + vsize, vpos[i][1] - vsize], [vpos[i][0] + vsize, vpos[i][1] + vsize], [vpos[i][0] - vsize, vpos[i][1] + vsize]],
                                  color='white', fill=True, edgecolor='black', thickness=1, zorder=2) + text('g=' + repr(reord_self._genera[i]), vpos[i], fontsize=20, color='black', zorder=3) for i in range(len(reord_self._genera))]

        # non-self edges
        edge_graph = []
        for e in reord_self._edges:
            ver1 = reord_self.vertex(e[0])
            ver2 = reord_self.vertex(e[1])
            if ver1 != ver2:
                x = (vpos[ver1][0] + vpos[ver2][0]) / ZZ(2)
                y = (vpos[ver1][1] + vpos[ver2][1]) / ZZ(2) + eheight[e]
                edge_graph += [bezier_path([[vpos[ver1], (x, y), vpos[ver2]]], color='black', zorder=1)]

        marking_graph = []

        for v in range(len(reord_self._genera)):
            se_list = reord_self.edges_between(v, v)
            m_list = reord_self.list_markings(v)
            v_x0 = vpos[v][0] - (2 * len(se_list) + len(m_list) - 1) * mark_dx / ZZ(2)

            for e in se_list:
                edge_graph += [bezier_path([[vpos[v], (v_x0, -mark_dy),
                                           (v_x0 + mark_dx, -mark_dy), vpos[v]]], zorder=1)]
                v_x0 += 2 * mark_dx
            for l in m_list:
                marking_graph += [line([vpos[v], (v_x0, -mark_dy)], color='black', zorder=1) + circle((v_x0, -mark_dy), mark_rad, fill=True,
                                                                                                      facecolor='white', edgecolor='black', zorder=2) + text(repr(l), (v_x0, -mark_dy), fontsize=10, color='black', zorder=3)]
                v_x0 += mark_dx
        G = sum(marking_graph) + sum(edge_graph) + sum(vertex_graph)
        G.axes(False)
        return G

    def _unicode_art_(self):
        """
        Return unicode art for the stable graph ``self``.

        EXAMPLES::

            sage: from admcycles import *
            sage: A = StableGraph([1, 2],[[1, 2, 3], [4]],[(3, 4)])
            sage: unicode_art(A)
             ╭────╮
             3    4
            ╭┴─╮ ╭┴╮
            │1 │ │2│
            ╰┬┬╯ ╰─╯
             12

            sage: A = StableGraph([333, 4444],[[1, 2, 3], [4]],[(3, 4)])
            sage: unicode_art(A)
             ╭─────╮
             3     4
            ╭┴──╮ ╭┴───╮
            │333│ │4444│
            ╰┬┬─╯ ╰────╯
             12

            sage: B = StableGraph([3,5], [[1,3,5],[2]], [(1,2),(3,5)])
            sage: unicode_art(B)
             ╭─────╮
             │╭╮   │
             135   2
            ╭┴┴┴╮ ╭┴╮
            │3  │ │5│
            ╰───╯ ╰─╯

            sage: C = StableGraph([3,5], [[3,1,5],[2,4]], [(1,2),(3,5)])
            sage: unicode_art(C)
              ╭────╮
             ╭─╮   │
             315   2
            ╭┴┴┴╮ ╭┴╮
            │3  │ │5│
            ╰───╯ ╰┬╯
                   4
        """
        from sage.typeset.unicode_art import UnicodeArt
        N = self.num_verts()
        all_half_edges = self.halfedges()
        half_edges = {i: [j for j in legs_i if j in all_half_edges]
                      for i, legs_i in zip(range(N), self._legs)}
        open_edges = {i: [j for j in legs_i if j not in all_half_edges]
                      for i, legs_i in zip(range(N), self._legs)}
        left_box = [u' ', u'╭', u'│', u'╰', u' ']
        right_box = [u'  ', u'╮ ', u'│ ', u'╯ ', u'  ']
        positions = {}
        boxes = UnicodeArt()
        total_width = 0
        for vertex in range(N):
            t = list(left_box)
            for v in half_edges[vertex]:
                w = str(v)
                positions[v] = total_width + len(t[0])
                t[0] += w
                t[1] += u'┴' + u'─' * (len(w) - 1)
            for v in open_edges[vertex]:
                w = str(v)
                t[4] += w
                t[3] += u'┬' + u'─' * (len(w) - 1)
            t[2] += str(self._genera[vertex])
            length = max(len(line) for line in t)
            for i in [0, 2, 4]:
                t[i] += u' ' * (length - len(t[i]))
            for i in [1, 3]:
                t[i] += u'─' * (length - len(t[i]))
            for i in range(5):
                t[i] += right_box[i]
            total_width += length + 2
            boxes += UnicodeArt(t)
        num_edges = self.num_edges()
        matchings = [[u' '] * (1 + max(positions.values()))
                     for _ in range(num_edges)]
        for i, (a, b) in enumerate(self.edges()):
            xa = positions[a]
            xb = positions[b]
            if xa > xb:
                xa, xb = xb, xa
            for j in range(xa + 1, xb):
                matchings[i][j] = u'─'
            matchings[i][xa] = u'╭'
            matchings[i][xb] = u'╮'
            for j in range(i + 1, num_edges):
                matchings[j][xa] = u'│'
                matchings[j][xb] = u'│'
        matchings = [u''.join(line) for line in matchings]
        return UnicodeArt(matchings + list(boxes))


# This function is about to be deprecated. Instead use
#   - StableGraph.is_isomorphic
#   - StableGraph.automorphism_number


# computes union of dictionaries

def dicunion(*dicts):
    return dict(itertools.chain.from_iterable(dct.items() for dct in dicts))


def GraphIsom(G, H, check=False):
    # TODO: Insert quick hash-check if G,H can be isomorphic at all
    if (G.invariant() != H.invariant()):
        return []

    Isomlist = []    # list of isomorphisms that will be returned
    IsoV = {}  # working vertex-dictionary
    IsoL = {j: j for j in G.list_markings()}  # working leg-dictionary

    for j in G.list_markings():
        vG = G.vertex(j)
        vH = H.vertex(j)

        # if vertices containing j have different genera or degrees in G, there is no automorphism
        # also if the markings give contradictory information where the vertices go, there is no automorphism
        if (G._genera[vG] != H._genera[vH]) or (len(G._legs[vG]) != len(H._legs[vH])) or (vG in IsoV and IsoV[vG] != vH):
            return []
        # otherwise add known association of vertices to IsoV
        IsoV[vG] = vH
    # Now vG and vH contain all information prescribed by markings, proceed to assign markingless vertices
    # Create dictionaries gdG, gdH associating to tuples (genus, degree) the indices of markingless vertices in G,H with those data
    gdG = {}
    gdH = {}

    for v in range(len(G._genera)):
        if v not in IsoV:
            gd = (G._genera[v], len(G._legs[v]))
            if gd in gdG:
                gdG[gd] += [v]
            else:
                gdG[gd] = [v]
    for v in range(len(H._genera)):
        if v not in IsoV.values():
            gd = (H._genera[v], len(H._legs[v]))
            if gd in gdH:
                gdH[gd] += [v]
            else:
                gdH[gd] = [v]

    if set(gdG) != set(gdH):
        return []

    # list (for all keys (g,d) of gdG) of lists of all possible dictionary-bijections from gdG(gd) to gdH(gd)
    VertIm = []

    for gd in gdG:
        if len(gdG[gd]) != len(gdH[gd]):
            return []
        P = Permutations(len(gdG[gd]))
        ind = list(range(len(gdG[gd])))
        VertIm += [[{gdG[gd][i]: gdH[gd][p[i] - 1] for i in ind} for p in P]]

    # Now VertIm is a list of the form [[{0:0, 1:1},{0:1, 1:0}], [{2:2}]]
    # Iterate over all possible combinations
    for VI in itertools.product(*VertIm):
        continueloop = False
        IsoV2 = dicunion(IsoV, *VI)  # IsoV2 is now complete dictionary of vertices

        # list (for all (ordered) pairs of vertices of G) of lists of dictionaries associating legs of edges connecting the pair to legs in H connecting the image pair
        LegIm = []

        # TODO: possibly want quick check that now graphs are actually isomorphic

        # first look at loops of G
        for v in range(len(G._genera)):
            EdG = G.edges_between(v, v)

            EdH = H.edges_between(IsoV2[v], IsoV2[v])
            if len(EdG) != len(EdH):
                continueloop = True
                break

            LegImvv = []

            # P gives the ways to biject from EdG to EdH, but additionally for each edge we have to decide to which of the two legs of the target edge it goes
            P = Permutations(len(EdG))
            ran = list(range(len(EdG)))
            choic = len(EdG) * [[0, 1]]
            for p in P:
                for o in itertools.product(*choic):
                    # Example: EdG=[(1,2),(3,4)], EdH=[(6,7),(9,11)], p=[2,1], o=[0,1] -> {1:9, 2:11, 3:7, 4:6}
                    di = dicunion({EdG[i][0]: EdH[p[i] - 1][o[i]]
                                  for i in ran}, {EdG[i][1]: EdH[p[i] - 1][1 - o[i]] for i in ran})
                    LegImvv += [di]
            LegIm += [LegImvv]
        if continueloop:
            continue

        # now look at edges from v to w
        for v in range(len(G._genera)):
            if continueloop:
                break
            for w in range(v + 1, len(G._genera)):
                EdG = G.edges_between(v, w)
                EdH = H.edges_between(IsoV2[v], IsoV2[w])
                if len(EdG) != len(EdH):
                    continueloop = True
                    break

                LegImvw = []

                # P gives the ways to biject from EdG to EdH
                P = Permutations(len(EdG))
                ran = list(range(len(EdG)))
                for p in P:
                    # Example: EdG=[(1,2),(3,4)], EdH=[(6,7),(9,11)], p=[2,1] -> {1:9, 2:11, 3:6, 4:7}
                    di = dicunion({EdG[i][0]: EdH[p[i] - 1][0]
                                  for i in ran}, {EdG[i][1]: EdH[p[i] - 1][1] for i in ran})
                    LegImvw += [di]
                LegIm += [LegImvw]

        if continueloop:
            continue

        # if program runs to here, then IsoV2 is a bijection of vertices respecting the markings,
        # LegIm is a list of lists of dictionaries giving bijections of non-marking legs that respect
        # the map of vertices and edges; it remains to add the various elements to IsoL and return them
        Isomlist += [[IsoV2, dicunion(IsoL, *LegDics)] for LegDics in itertools.product(*LegIm)]

        if check and Isomlist:
            return Isomlist

    return Isomlist
