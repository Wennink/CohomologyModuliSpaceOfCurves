r"""
Decorated graphs and morphisms

This modules contain two main classes : :class:`DecoratedGraph`
and :class:`DecoratedGraphMorphism`.

A :class:`DecoratedGraph` is a graph with genera and markings
at each vertex. It is similar to
:class:`~admcycles.stable_graph.StableGraph` but without labellings
of the legs. A :class:`DecoratedGraphMorphism` is an edge contraction
between two :class:`DecoratedGraph` s.

.. WARNING::

    This module is experimental and is being developped to become
    a replacement of :class:`~admcycles.stable_graph.StableGraph`.
"""

from collections import defaultdict
import itertools
import numbers

from sage.structure.sage_object import SageObject
from sage.libs.gap.libgap import libgap
from sage.arith.misc import binomial, factorial
from sage.graphs.graph import Graph
from sage.graphs.base.static_sparse_backend import StaticSparseBackend
from sage.groups.perm_gps.permgroup import PermutationGroup
from sage.sets.disjoint_set import DisjointSet_of_integers

from .integer_list import integer_lists_mod_perm_group, is_trivial_group
from .moduli import MODULI_SM, MODULI_RT, MODULI_CT, MODULI_TL, MODULI_ST, get_moduli, num_edges_bound


def _edge(u, v):
    r"""
    TESTS::

        sage: from admcycles.decorated_graph import _edge
        sage: _edge(0, 1)
        (0, 1)
        sage: _edge(1, 0)
        (0, 1)
    """
    return (u, v) if u <= v else (v, u)


def to_exp_list(p):
    r"""
    EXAMPLES::

        sage: from admcycles.decorated_graph import to_exp_list
        sage: to_exp_list([3, 1, 1])
        ([3, 1], [1, 2])
        sage: to_exp_list([3, 3, 1])
        ([3, 1], [2, 1])
        sage: to_exp_list([2, 2, 2])
        ([2], [3])
    """
    if not p:
        return [], []
    parts = []
    mults = []
    i = 0
    while i < len(p):
        c = p[i]
        m = 1
        i += 1
        while i < len(p) and p[i] == c:
            i += 1
            m += 1
        parts.append(c)
        mults.append(m)
    return parts, mults


def static_sparse_graph(graph):
    r"""
    Return a copy of ``graph`` as a static sparse graph.

    This function is much faster than calling ``graph.copy(immutable=True)`` but
    still not optimal. See https://gitlab.com/modulispaces/admcycles/-/issues/95.

    EXAMPLES::

        sage: from admcycles.decorated_graph import static_sparse_graph
        sage: G = Graph([(0, 1, 2), (2, 3, 5), (0, 3, 4)], weighted=True, loops=False, multiedges=False)
        sage: H = static_sparse_graph(G)
        sage: H == G
        True
        sage: G._backend
        <sage.graphs.base.sparse_graph.SparseGraphBackend object at ...>
        sage: H._backend
        <sage.graphs.base.static_sparse_backend.StaticSparseBackend object at ...>
    """
    ans = Graph.__new__(Graph)
    ans._backend = StaticSparseBackend(graph, loops=False, multiedges=False)
    ans._immutable = True
    ans._pos = None
    ans._weighted = True
    ans._latex_opts = None
    return ans


class DecoratedGraph(SageObject):
    r"""
    A decorated graph is a graph on {0, 1, ..., num_verts-1} with allowed loops and
    multiple edges that has "genus" and "marking" decorations at its vertices.

    It is represented as a list of genera (as many as vertices), a list of loops
    (as many as vertices), a list of markings (as many as vertices) and an
    underlying simple sage graphs whose edge labels encode the edge multiplicities.

    EXAMPLES::

        sage: from admcycles.decorated_graph import DecoratedGraph

    A decorated graph is constructed from a list of genera (one for each
    vertex), a list of markings (as many lists as vertices) and a list of
    edges. The edges are specified as triples ``(u, v, m)`` where ``u`` and
    ``v`` are the extremities of the edge and ``m`` is the multiplicity of
    the edge.

    The graph with a single vertex carrying genus 3 and no edge::

        sage: DecoratedGraph([3], [[]], [])
        DecoratedGraph([3], [[]], [])

    The graph with a single vertex carrying genus 0 and markings ``[1, 2, 3]``
    and no edge::

        sage: DecoratedGraph([0], [[1, 2, 3]], [])
        DecoratedGraph([0], [[3, 2, 1]], [])

    Note that markings are automatically sorted by decreasing order.

    A graph with two vertices of genus zero and a triple edge between them::

        sage: DecoratedGraph([0, 0], [[], []], [(0, 1, 3)])
        DecoratedGraph([0, 0], [[], []], [(0, 1, 3)])

    For multiplicity one edges ``m`` can be omitted::

        sage: DecoratedGraph([1, 1], [[], []], [(0, 0, 2), (0, 1)])
        DecoratedGraph([1, 1], [[], []], [(0, 1, 1), (0, 0, 2)])

    Be aware that if an edge is repeated several times, only the last
    occurrence matters::

        sage: DecoratedGraph([1, 1], [[], []], [(0, 1, 4), (0, 1), (0, 1, 3)])
        DecoratedGraph([1, 1], [[], []], [(0, 1, 3)])
    """
    __slots__ = ['_graph',  # underlying sage graph on vertex set {0, 1, ..., num_verts - 1}
                            # with multiplicity encoded as edge labels
                 '_genera',  # list of genera at the vertices
                 '_loops',  # list of loop multiplicity (not stored in _graph)
                 '_markings',  # list of lists of integers; the markings at each vertex
                 '_mutable',  # mutability flag
                 '_vertex_partition',  # cache
                 '_canonical_label',  # cache
                 '_automorphism_group']  # cache

    def __init__(self, genera=None, markings=None, edges=None, mutable=False):
        r"""
        INPUT:

        genera: list
          a genus for each vertex

        markings: list of lists
          the marking for each vertex

        edges: list of pairs or triples
          the list of edges specified as pairs of vertices or pair of vertices
          and multiplicity

        mutable: boolean
          whether the graph is mutable
        """
        nv = None
        if genera is not None:
            try:
                nv = len(genera)
            except TypeError:
                nv = int(genera)
                genera = None
        elif markings is not None:
            nv = len(markings)
        if nv is not None:
            graph = Graph(nv, loops=True, multiedges=False)
            if edges is not None:
                graph.add_edges(edges)
        else:
            graph = Graph(edges, loops=True, multiedges=False)
            nv = max(graph.vertices()) + 1

        self._graph = Graph(nv, loops=False, multiedges=False, weighted=True)
        self._loops = [0] * nv
        for i, j, m in graph.edges(sort=False):
            if m is None:
                m = 1
            if not (0 <= i < nv and 0 <= j < nv and isinstance(m, numbers.Integral) and m > 0):
                raise ValueError('invalid graph')
            if i == j:
                self._loops[i] = m
            else:
                self._graph.add_edge(i, j, m)
        if genera is None:
            self._genera = [0] * nv
        else:
            self._genera = list(map(int, genera))
            if len(self._genera) != nv:
                raise ValueError('invalid genera')

        # TODO: allow markings to be None instead of a list of empty lists?
        if markings is None:
            self._markings = [[] for _ in range(nv)]
        else:
            self._markings = [sorted(m, reverse=True) for m in markings]
            if len(self._markings) != len(self._genera):
                raise ValueError('invalid markings')
        self._mutable = True
        if not mutable:
            self.set_immutable()

    @staticmethod
    def _from_stable_graph(stgraph):
        r"""
        Build a ``DecoratedGraph`` from a ``StableGraph``.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: from admcycles.stable_graph import StableGraph
            sage: st = StableGraph([1, 1], [[1, 2, 3], [4, 5]], [(1, 4), (2, 3)])
            sage: G, edge_to_legs = DecoratedGraph._from_stable_graph(st)
            sage: G
            DecoratedGraph([1, 1], [[], [5]], [(0, 1, 1), (0, 0, 1)])
            sage: edge_to_legs[0, 1]
            [(1, 4)]
            sage: edge_to_legs[0, 0]
            [(2, 3)]
        """
        ans = DecoratedGraph.__new__(DecoratedGraph)
        nv = len(stgraph._genera)
        ans._genera = stgraph._genera[:]
        ans._loops = [0] * nv
        ans._graph = Graph(nv, loops=False, multiedges=False, weighted=True)

        leg_to_vertex = {}
        for v, legs in enumerate(stgraph._legs):
            for l in legs:
                leg_to_vertex[l] = v
        edge_to_legs = defaultdict(list)
        for lu, lv in stgraph._edges:
            u = leg_to_vertex[lu]
            v = leg_to_vertex[lv]
            if u <= v:
                edge_to_legs[(u, v)].append((lu, lv))
            else:
                edge_to_legs[(v, u)].append((lv, lu))
        half_edges = set().union(*stgraph._edges)
        ans._markings = [sorted((h for h in l if h not in half_edges), reverse=True) for l in stgraph._legs]
        for (u, v), value in edge_to_legs.items():
            if u == v:
                ans._loops[u] += len(value)
            else:
                ans._graph.add_edge(u, v, len(value))
        ans._mutable = True
        ans.set_immutable()
        return ans, dict(edge_to_legs)

    def _check_vertex(self, v):
        r"""
        TESTS::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: dg = DecoratedGraph([2, 3], [[1, 2], [3]], [(0, 1, 2)])
            sage: dg._check_vertex(0)
            0
            sage: dg._check_vertex('hello')
            Traceback (most recent call last):
            ...
            TypeError: not a vertex
            sage: dg._check_vertex(-1)
            Traceback (most recent call last):
            ...
            ValueError: vertex out of range
            sage: dg._check_vertex(3)
            Traceback (most recent call last):
            ...
            ValueError: vertex out of range
        """
        if not isinstance(v, numbers.Integral):
            raise TypeError('not a vertex')
        v = int(v)
        if v < 0 or v >= len(self._genera):
            raise ValueError('vertex out of range')
        return v

    def _check_edge(self, u, v):
        r"""
        TESTS::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: dg = DecoratedGraph([2, 3, 1], [[1, 2], [3], [3]], [(0, 0, 1), (0, 1, 2), (0, 2, 1)])
            sage: dg._check_edge(1, 1)
            Traceback (most recent call last):
            ...
            ValueError: not an edge
            sage: dg._check_edge(1, 2)
            Traceback (most recent call last):
            ...
            ValueError: not an edge
        """
        u = self._check_vertex(u)
        v = self._check_vertex(v)
        if u == v:
            if not self._loops[u]:
                raise ValueError('not an edge')
        elif not self._graph.has_edge(u, v):
            raise ValueError('not an edge')
        return (u, v)

    def has_edge(self, u, v, check=True):
        r"""
        Return whether this graph has an edge between the vertices ``u` and ``v``.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: g = DecoratedGraph([0, 0, 0], [[], [], []], [(0, 1, 1), (0, 0, 1), (0, 2, 1)])
            sage: g.has_edge(0, 0)
            True
            sage: g.has_edge(0, 1)
            True
            sage: g.has_edge(1, 1)
            False
            sage: g.has_edge(1, 2)
            False
        """
        if check:
            u = self._check_vertex(u)
            v = self._check_vertex(v)
        return bool(self._loops[u]) if u == v else self._graph.has_edge(u, v)

    def add_edge(self, u, v, m=1, check=True):
        r"""
        Add an edge ``(u, v)`` in this graph.

        Both ``u`` and ``v`` must be vertices of the graph.

        INPUT:

        u, v : integers
          two vertices of this decorated graph

        m : integer (default 1)
          a multiplicity for the edge

        check : boolean (default ``True``)
          if set to ``True`` perform some validity checks on the input

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: G = DecoratedGraph([1, 2, 3], [[2, 1], [1], []], [(0, 1, 2)], mutable=True); G
            DecoratedGraph([1, 2, 3], [[2, 1], [1], []], [(0, 1, 2)], mutable=True)
            sage: G.add_edge(0, 2); G
            DecoratedGraph([1, 2, 3], [[2, 1], [1], []], [(0, 1, 2), (0, 2, 1)], mutable=True)
            sage: G.add_edge(0, 1, 2); G
            DecoratedGraph([1, 2, 3], [[2, 1], [1], []], [(0, 1, 4), (0, 2, 1)], mutable=True)
            sage: G.add_edge(0, 0, 3); G
            DecoratedGraph([1, 2, 3], [[2, 1], [1], []], [(0, 1, 4), (0, 2, 1), (0, 0, 3)], mutable=True)
        """
        if not self._mutable:
            raise ValueError('immutable graph')
        if check:
            if not isinstance(m, numbers.Integral) and m >= 0:
                raise ValueError('invalid multiplicity')
            u = self._check_vertex(u)
            v = self._check_vertex(v)
            m = int(m)
        if u == v:
            self._loops[u] += m
        else:
            if self._graph.has_edge(u, v):
                self._graph.set_edge_label(u, v, self._graph.edge_label(u, v) + m)
            else:
                self._graph.add_edge(u, v, m)

    def set_genus(self, v, g, check=True):
        r"""
        Set the genus of vertex v to be g.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: G = DecoratedGraph([1, 2], [[2, 1], [1]], [(0, 1, 2)], mutable=True); G
            DecoratedGraph([1, 2], [[2, 1], [1]], [(0, 1, 2)], mutable=True)
            sage: G.set_genus(0, 5)
            sage: G
            DecoratedGraph([5, 2], [[2, 1], [1]], [(0, 1, 2)], mutable=True)
        """
        if not self._mutable:
            raise ValueError('immutable graph')
        if check:
            if not isinstance(g, numbers.Integral) and g >= 0:
                raise ValueError('invalid genus')
            g = int(g)
            v = self._check_vertex(v)
        self._genera[v] = int(g)

    def degree(self, v=None):
        r"""
        Return the list of degrees or the degree of a single vertex if ``v`` is specified.

        The degree takes into account edges, loops and markings (with multiplicities).

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: g = DecoratedGraph([0, 1, 0], [[2, 1, 1], [], [3, 2]], [(0, 0, 2), (0, 1, 3), (1, 2, 1)])
            sage: g.degree()
            [10, 4, 3]
            sage: g.degree(2)
            3
        """
        if v is not None:
            v = self._check_vertex(v)
            return len(self._markings[v]) + 2 * self._loops[v] + sum(self._graph.edge_label(v, w) for w in self._graph.neighbor_iterator(v))
        return [self.degree(v) for v in self.vertices()]

    def copy(self, mutable=None):
        r"""
        Return a copy of this stable graph.

        When asking for an immutable copy of an immutable graph, no copy is
        performed.

        INPUT:

        mutable : boolean or ``None`` (default ``None``)
          if ``None`` the output has the same mutability status as this
          stable graph. If ``mutable`` is set to ``True`` or ``False``
          then the copy will respectively be mutable or immutable.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: g1 = DecoratedGraph([0, 0], [[], []], [(0, 1, 1)], mutable=True)
            sage: g2 = DecoratedGraph([0, 0], [[], []], [(0, 1, 1)], mutable=False)
            sage: g3 = g1.copy(mutable=True)
            sage: g4 = g1.copy(mutable=False)
            sage: g5 = g2.copy(mutable=True)
            sage: g6 = g2.copy(mutable=False)
            sage: g3.contract_edge(0, 1)
            sage: g5.contract_edge(0, 1)
            sage: g1 == g2 == g4 == g6
            True
            sage: g3 == g5
            True
            sage: g2 is g6
            True
        """
        if mutable is None:
            mutable = self._mutable
        if not mutable and not self._mutable:
            # do not copy immutable graphs
            return self

        ans = DecoratedGraph.__new__(DecoratedGraph)
        ans._markings = [m[:] for m in self._markings]
        ans._genera = self._genera[:]
        ans._loops = self._loops[:]
        ans._mutable = mutable
        ans._graph = self._graph.copy(immutable=not mutable)
        return ans

    def markings(self, v=None):
        r"""
        Return the list of markings.

        If a vertex ``v`` is provided, then return the list of markings at ``v``.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: g = DecoratedGraph([1, 1], [[2, 1], [3, 1]], [(0, 1)])
            sage: g.markings()
            [3, 2, 1, 1]
            sage: g.markings(0)
            [2, 1]
            sage: g.markings(1)
            [3, 1]
        """
        if v is None:
            all_markings = sum(self._markings, [])
            all_markings.sort(reverse=True)
            return all_markings
        return self._markings[v][:]

    def num_verts(self):
        r"""
        Return the number of vertices of this decorated graph.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: g = DecoratedGraph([2], [[]], [])
            sage: g.num_verts()
            1
        """
        return len(self._genera)

    def num_edges(self, multiplicities=True):
        r"""
        Return the number of edges of this decorated graph.

        INPUT:

        multiplicities : boolean (default ``True``)
          if set to ``False`` return the number of edges without multiplities

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: g = DecoratedGraph([0, 1], [[1, 2], [3]], [(0, 0, 2), (0, 1, 1)])
            sage: g.num_edges()
            3
            sage: g.num_edges(multiplicities=False)
            2
        """
        if multiplicities:
            return sum(m for _, _, m in self._graph.edges(sort=False)) + sum(self._loops)
        else:
            return self._graph.num_edges() + sum(map(bool, self._loops))

    def num_loops(self, multiplicities=True):
        r"""
        Return the number of loops.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: g = DecoratedGraph([0, 1], [[1, 2], [3]], [(0, 0, 2), (0, 1, 1)])
            sage: g.num_loops()
            2
            sage: g.num_loops(multiplicities=False)
            1
        """
        if multiplicities:
            return sum(self._loops)
        else:
            return sum(map(bool, self._loops))

    def edge_multiplicity(self, u, v, check=True):
        r"""
        Return the multiplicity of the edge from ``u`` to ``v``.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: g = DecoratedGraph([1, 1, 1], [[], [], []], [(0, 0, 2), (0, 1), (0, 2)])
            sage: g.edge_multiplicity(0, 0)
            2
            sage: g.edge_multiplicity(0, 1)
            1
            sage: g.edge_multiplicity(1, 1)
            0
            sage: g.edge_multiplicity(1, 2)
            0
        """
        if check:
            u = self._check_vertex(u)
            v = self._check_vertex(v)
        if u == v:
            return self._loops[u]
        elif self._graph.has_edge(u, v):
            return self._graph.edge_label(u, v)
        else:
            return 0

    def vertices(self):
        r"""
        Return a ``range`` object corresponding to the vertex set of this graph.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: DecoratedGraph([0], [[1, 2, 3]], []).vertices()
            range(0, 1)
        """
        return range(len(self._genera))

    def edges(self, multiplicities=True, loops=True, sort=False):
        r"""
        Iterate through the edges of this decorated graph.

        If ``multiplicities`` is set to ``True`` (the default) then return a list
        of triples ``(u, v, edge_multiplicity)``. Otherwise, just return pairs
        ``(u, v)``.
        If ``loops`` is set to ``True`` (the default), include the edges from
        vertices to themselves.
        If ``sort`` is set to ``True`` (default: False), sort the edges, where
        the iteration starts with edges between different vertices, and then
        (possibly) enumerates the loops.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: list(DecoratedGraph([2], [[]], []).edges())
            []
            sage: list(DecoratedGraph([1], [[]], [(0, 0, 1)]).edges())
            [(0, 0, 1)]
            sage: list(DecoratedGraph([0, 0], [[], []], [(0, 1, 3)]).edges())
            [(0, 1, 3)]
        """
        yield from self._graph.edges(labels=multiplicities, sort=sort)
        if loops:
            if multiplicities:
                yield from ((v, v, m) for v, m in enumerate(self._loops) if m)
            else:
                yield from ((v, v) for v, m in enumerate(self._loops) if m)

    def vanishes(self, moduli):
        r"""
        Return whether this decorated graph vanishes for the given ``moduli``.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: dg = DecoratedGraph([0, 0], [[1, 2, 3], [4, 5, 6]], [(0, 1, 1)])
            sage: dg.vanishes('rational_tails') or dg.vanishes('compact_type') or dg.vanishes('tree_like')
            False
            sage: dg.vanishes('smooth')
            True

            sage: DecoratedGraph([0, 0], [[], []], [(0, 1, 3)]).vanishes('tree_like')
            True
            sage: DecoratedGraph([0, 0], [[], []], [(0, 1, 1), (0, 0, 1), (1, 1, 1)]).vanishes('tree_like')
            False
        """
        # NOTE: here
        # - we do not test for stability
        # - we ignore disconnected graphs (the condition ne != nv -1 is not
        #   enough to have a tree)
        # We should probably have something more robust?
        # (see also the method moduli())

        moduli = get_moduli(moduli)

        if moduli == MODULI_ST:
            return False

        nv = len(self._genera)
        if moduli == MODULI_SM:
            return nv > 1 or bool(self._loops[0])

        if moduli <= MODULI_CT and any(self._loops):
            return True
        if moduli == MODULI_RT and sum(bool(g) for g in self._genera) > 1:
            return True

        ne = sum(m for _, _, m in self._graph.edges(sort=False))
        return ne != nv - 1

    def moduli(self):
        r"""
        Return the minimum moduli on which this graph does not vanish.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: DecoratedGraph([0], [[3, 2, 1]], []).moduli()
            0
            sage: DecoratedGraph([0, 0], [[1, 2, 3], [4, 5, 6]], [(0, 1, 1)]).moduli()
            1
            sage: DecoratedGraph([1, 1], [[1], [2]], [(0, 1, 1)]).moduli()
            2
            sage: DecoratedGraph([0], [[3, 2, 1]], [(0, 0, 1)]).moduli()
            3
            sage: DecoratedGraph([0, 0], [[], []], [(0, 1, 1), (0, 0, 1), (1, 1, 1)]).moduli()
            3
            sage: DecoratedGraph([0, 0], [[], []], [(0, 1, 3)]).moduli()
            4
        """
        # NOTE: here
        # - we do not test for stability
        # - we ignore disconnected graphs (the condition ne != nv -1 is not
        #   enough to have a tree)
        # We should probably have something more robust?
        # (see also the method vanishes())

        nv = len(self._genera)
        if nv == 1:
            return MODULI_TL if self._loops[0] else MODULI_SM

        ne = sum(m for _, _, m in self._graph.edges(sort=False))
        if ne != nv - 1:
            return MODULI_ST

        if any(self._loops):
            return MODULI_TL
        if sum(bool(g) for g in self._genera) > 1:
            return MODULI_CT
        return MODULI_RT

    def _to_stable_graph(self, edge_map=False, mutable=False):
        r"""
        Return a leg labelled graph corresponding to this decorated graph.

        The output is of type :class:`admcycles.stable_graph.StableGraph`.

        INPUT:

        edge_map : boolean (default ``False``)
          if set to ``True`` return a pair ``(stgraph, edge_to_legs)`` where
          ``edge_to_legs`` is a dictionary mapping the edge of the decorated
          graph to a list of pairs of legs.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: g = DecoratedGraph([0], [[]], [(0, 0, 2)])
            sage: llg = g._to_stable_graph()
            sage: llg
            [0] [[1, 2, 3, 4]] [(1, 2), (3, 4)]

            sage: g._to_stable_graph(edge_map=True)[0] == llg
            True
            sage: g._to_stable_graph(edge_map=True)[1]
            {(0, 0): [(1, 2), (3, 4)]}
        """
        from .stable_graph import StableGraph

        legs = [sorted(m) for m in self._markings]
        maxleg = max((m[0] for m in self._markings if m), default=0) + 1
        edge_to_legs = {}
        for i, j, mult in self.edges():
            edge_to_legs[(i, j)] = []
            for _ in range(mult):
                l0 = maxleg
                l1 = maxleg + 1
                maxleg += 2
                legs[i].append(l0)
                legs[j].append(l1)
                edge_to_legs[(i, j)].append((l0, l1))

        st = StableGraph.__new__(StableGraph)
        st._genera = self._genera[:]
        st._legs = legs
        st._edges = sum(edge_to_legs.values(), [])
        st._maxleg = maxleg
        st._mutable = bool(mutable)
        st._graph_cache = None
        st._canonical_label_cache = None
        st._hash = None
        return (st, edge_to_legs) if edge_map else st

    def _repr_(self):
        r"""
        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: DecoratedGraph([1, 1], [[], []], [(0, 0, 3)])  # indirect doctest
            DecoratedGraph([1, 1], [[], []], [(0, 0, 3)])
            sage: DecoratedGraph([1, 1], [[], []], [(0, 0, 3)], mutable=True)  # indirect doctest
            DecoratedGraph([1, 1], [[], []], [(0, 0, 3)], mutable=True)
        """
        mut_string = ', mutable=True' if self._mutable else ''

        return 'DecoratedGraph({}, {}, {}{})'.format(self._genera, self._markings, list(self.edges(sort=True)), mut_string)

    def is_mutable(self):
        r"""
        Return whether this graph is mutable.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: DecoratedGraph([1, 1], [[], []], [(0, 0, 3)]).is_mutable()
            False
            sage: DecoratedGraph([1, 1], [[], []], [(0, 0, 3)], mutable=True).is_mutable()
            True
        """
        return self._mutable

    def set_immutable(self):
        r"""
        Set this graph immutable.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: g = DecoratedGraph([1, 1], [[], []], [(0, 0, 3)], mutable=True)
            sage: g.is_mutable()
            True
            sage: g.set_immutable()
            sage: g.is_mutable()
            False
        """
        if self._mutable:
            self._graph = static_sparse_graph(self._graph)
            self._mutable = False

    def __eq__(self, other):
        r"""
        Return whether ``self`` and ``other`` are equal.

        TESTS::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: DecoratedGraph([3], [[]], []) == DecoratedGraph([3], [[]], [])  # indirect doctest
            True
            sage: DecoratedGraph([3], [[]], []) == DecoratedGraph([2, 1], [[], []], [])  # indirect doctest
            False
            sage: DecoratedGraph([3], [[]], []) == DecoratedGraph([3], [[1]], [])  # indirect doctest
            False
            sage: DecoratedGraph([1, 1], [[], []], [(0, 1, 1)]) == DecoratedGraph([1, 1], [[], []], [(0, 1, 2)])  # indirect doctest
            False
            sage: DecoratedGraph([3], [[]], []) == "hello"  # indirect doctest
            False
        """
        if type(self) is not type(other):
            return NotImplemented
        return (self._loops == other._loops and
                self._genera == other._genera and
                self._markings == other._markings and
                self._graph == other._graph)

    def __ne__(self, other):
        r"""
        Return whether ``self`` and ``other`` are different.

        TESTS::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: DecoratedGraph([3], [[]], []) != DecoratedGraph([3], [[]], [])  # indirect doctest
            False
            sage: DecoratedGraph([3], [[]], []) != DecoratedGraph([2, 1], [[], []], [])  # indirect doctest
            True
            sage: DecoratedGraph([3], [[]], []) != DecoratedGraph([3], [[1]], [])  # indirect doctest
            True
            sage: DecoratedGraph([1, 1], [[], []], [(0, 1, 1)]) != DecoratedGraph([1, 1], [[], []], [(0, 1, 2)])  # indirect doctest
            True
            sage: DecoratedGraph([3], [[]], []) != "hello"  # indirect doctest
            True
        """
        if type(self) is not type(other):
            return NotImplemented
        return (self._loops != other._loops or
                self._genera != other._genera or
                self._markings != other._markings or
                self._graph != other._graph)

    def __hash__(self):
        r"""
        Return a hash value.

        The graph must be immutable.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: g = DecoratedGraph([2, 3], [[1, 1], [1, 2]], [(0, 1, 3), (0, 0, 2)], mutable=True)
            sage: hash(g)  # indirect doctest
            Traceback (most recent call last):
            ...
            TypeError: mutable DecoratedGraph; use .set_immutable() first
            sage: g.set_immutable()
            sage: hash(g)  # random # indirect doctest
            -4498902808528948456
        """
        if self._mutable:
            raise TypeError('mutable DecoratedGraph; use .set_immutable() first')
        return hash((self._graph, tuple(self._genera), tuple(self._loops), tuple(map(tuple, self._markings))))

    def genus(self, v=None):
        r"""
        Return the genus of this stable graph

        If ``v`` is specified, return the genus at this vertex.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: G = DecoratedGraph([0], [[2, 1]], [(0, 0, 1)])
            sage: G.genus()
            1
            sage: G.genus(0)
            0

            sage: G = DecoratedGraph([1, 4], [[1], [1]], [(0, 1, 2), (1, 1, 1)])
            sage: G.genus()
            7
            sage: G.genus(0)
            1
            sage: G.genus(1)
            4
            sage: G.genus(2)
            Traceback (most recent call last):
            ...
            ValueError: vertex out of range
        """
        if v is not None:
            v = self._check_vertex(v)
            return self._genera[v]
        return sum(self._genera) + sum(self._loops) + sum(mult for _, _, mult in self._graph.edges(sort=False)) - self._graph.num_verts() + 1

    g = genus

    def num_markings(self):
        r"""
        Return the number of markings of this stable graph.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: G = DecoratedGraph([1, 2], [[1, 2], [1, 1]], [(0, 1, 2)])
            sage: G.num_markings()
            4
        """
        return sum(map(len, self._markings))

    n = num_markings

    def is_stable(self, v=None):
        r"""
        Return whether this decorated graph is stable.

        If a vertex v is specified, return whether v is stable.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: DecoratedGraph([0], [[]], []).is_stable()
            False
            sage: DecoratedGraph([0], [[1, 1]], []).is_stable()
            False
            sage: DecoratedGraph([0], [[]], [(0, 0, 1)]).is_stable()
            False
            sage: DecoratedGraph([1], [[]], []).is_stable()
            False
            sage: DecoratedGraph([0, 0], [[3, 2], [1]], [(0, 1, 1)]).is_stable()
            False

            sage: DecoratedGraph([0], [[1,1,1]], []).is_stable()
            True
            sage: DecoratedGraph([0], [[1]], [(0, 0, 1)]).is_stable()
            True
            sage: DecoratedGraph([0], [[]], [(0, 0, 2)]).is_stable()
            True
            sage: DecoratedGraph([1], [[1]], []).is_stable()
            True
            sage: DecoratedGraph([1], [[]], [(0, 0, 1)]).is_stable()
            True
            sage: DecoratedGraph([0, 0], [[3, 2], [4, 1]], [(0, 1, 1)]).is_stable()
            True
            sage: DecoratedGraph([0, 0], [[1, 1], []], [(0, 1, 1), (1, 1, 1)]).is_stable()
            True
            sage: DecoratedGraph([0, 0], [[1], [1]], [(0, 1, 2)]).is_stable()
            True
        """
        if v is not None:
            v = self._check_vertex(v)
            return 2 * self._genera[v] + 2 * self._loops[v] + len(self._markings[v]) + sum(self._graph.edge_label(v, w) for w in self._graph.neighbor_iterator(v)) >= 3
        return all(self.is_stable(v) for v in self.vertices())

    def is_connected(self):
        r"""
        Return whether the graph is connected.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: DecoratedGraph([1, 4], [[1], [1]], [(0, 1, 2), (1, 1, 1)]).is_connected()
            True
            sage: DecoratedGraph([1, 4], [[1], [1]], [(1, 1, 1)]).is_connected()
            False
        """
        return self._graph.is_connected()

    def dimension(self, v=None):
        """
        Return dimension of moduli space at vertex ``v``.

        If v=None, return dimension of the entire stratum parametrized by the graph.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: G = DecoratedGraph([3, 5], [[7], []], [(0,0,1),(0,1,1)])
            sage: G.dim(0), G.dim(1), G.dim()
            (10, 13, 23)
            sage: DecoratedGraph([0], [[]], [(0, 0, 2)]).dim()
            1
            sage: DecoratedGraph([0, 0], [[], []], [(0, 0, 3)]).dim()
            0
        """
        if v is None:
            return 3 * sum(self._genera) - 3 * len(self._genera) + 2 * sum(self._loops) + 2 * sum(m for _, _, m in self._graph.edges(sort=False)) + sum(map(len, self._markings))
        v = self._check_vertex(v)
        return 3 * self._genera[v] - 3 + 2 * self._loops[v] + sum(self._graph.edge_label(v, w) for w in self._graph.neighbor_iterator(v)) + len(self._markings[v])

    dim = dimension

    def relabel(self, perm, inplace=False, mutable=None):
        r"""
        Return this graph with relabelled vertices.

        INPUT:

        perm: permutation (as a list or a sage permutation)
          the permutation used to relabel the vertices

        inplace: boolean (default ``False``)
          if ``inplace=True``, the graph is relabelled in place.

        mutable: boolean or ``None`` (default ``None``)
          the mutability status of the returned graph. If set to
          ``True`` or ``False`` then ``inplace`` must be ``False``.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: g = DecoratedGraph([0, 1, 2, 0], [[1], [2], [1], [2, 1]], [(0, 1), (0, 2, 2), (0, 3, 3)])
            sage: g.relabel([1, 3, 0, 2])
            DecoratedGraph([2, 0, 0, 1], [[1], [1], [2, 1], [2]], [(0, 1, 2), (1, 2, 3), (1, 3, 1)])

            sage: g.relabel([1, 3, 0, 2], inplace=True)
            Traceback (most recent call last):
            ...
            ValueError: cannot relabel immutable decorated graph inplace; use a mutable copy instead
            sage: h = g.copy(mutable=True)
            sage: h
            DecoratedGraph([0, 1, 2, 0], [[1], [2], [1], [2, 1]], [(0, 1, 1), (0, 2, 2), (0, 3, 3)], mutable=True)
            sage: h.relabel([1, 3, 0, 2], inplace=True)
            DecoratedGraph([2, 0, 0, 1], [[1], [1], [2, 1], [2]], [(0, 1, 2), (1, 2, 3), (1, 3, 1)], mutable=True)

            sage: g.relabel([1, 3, 0, 2], mutable=True)
            DecoratedGraph([2, 0, 0, 1], [[1], [1], [2, 1], [2]], [(0, 1, 2), (1, 2, 3), (1, 3, 1)], mutable=True)
        """
        if not isinstance(perm, (tuple, list, dict)):
            # assume we have an automorphism, ie a PermutationGroupElement
            perm = perm.domain()

        if len(perm) != len(self._genera):
            raise ValueError('invalid permutation')

        if inplace:
            if not self._mutable:
                raise ValueError('cannot relabel immutable decorated graph inplace; use a mutable copy instead')
            if mutable is not None:
                raise ValueError('if inplace, mutable must be None')
            self._graph.relabel(perm, inplace=True)
            ans = self
        else:
            if mutable is None:
                mutable = self._mutable
            ans = DecoratedGraph.__new__(DecoratedGraph)
            ans._graph = self._graph.relabel(perm, inplace=False, immutable=not mutable)
            ans._mutable = mutable

        # NOTE: if this turns out to be too slow, we can do
        # inplace operations here
        nv = len(self._genera)
        genera = [None] * nv
        loops = [None] * nv
        markings = [None] * nv
        for v in range(nv):
            genera[perm[v]] = self._genera[v]
            loops[perm[v]] = self._loops[v]
            markings[perm[v]] = self._markings[v]

        ans._genera = genera
        ans._loops = loops
        ans._markings = markings

        return ans

    def identity_morphism(self):
        r"""
        Return the identity morphism contracting no edge.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: DecoratedGraph([0], [[1, 2, 3]], []).identity_morphism()
            DecoratedGraphMorphism(
                domain=DecoratedGraph([0], [[3, 2, 1]], []),
                codomain=DecoratedGraph([0], [[3, 2, 1]], []),
                vertex_images=(0,),
                edge_preimages={})
            sage: DecoratedGraph([2, 2], [[], []], [(0, 1, 2), (0, 0, 1)]).identity_morphism()
            DecoratedGraphMorphism(
                domain=DecoratedGraph([2, 2], [[], []], [(0, 1, 2), (0, 0, 1)]),
                codomain=DecoratedGraph([2, 2], [[], []], [(0, 1, 2), (0, 0, 1)]),
                vertex_images=(0, 1),
                edge_preimages={(0, 0): {(0, 0): 1}, (0, 1): {(0, 1): 2}})
        """
        return DecoratedGraphMorphism(self, self, tuple(self.vertices()), {(u, v): {(u, v): m} for (u, v, m) in self.edges()}, check=False)

    def trivial_morphism(self, codomain=None, check=True):
        r"""
        Return the trivial morphism contracting all edges.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: DecoratedGraph([0], [[1, 2, 3]], []).trivial_morphism()
            DecoratedGraphMorphism(
                domain=DecoratedGraph([0], [[3, 2, 1]], []),
                codomain=DecoratedGraph([0], [[3, 2, 1]], []),
                vertex_images=(0,),
                edge_preimages={})
            sage: DecoratedGraph([2, 2], [[], []], [(0, 1, 2), (0, 0, 1)]).trivial_morphism()
            DecoratedGraphMorphism(
                domain=DecoratedGraph([2, 2], [[], []], [(0, 1, 2), (0, 0, 1)]),
                codomain=DecoratedGraph([6], [[]], []),
                vertex_images=(0, 0),
                edge_preimages={})

        TESTS::

            sage: g = DecoratedGraph([3, 3], [[], []], [])
            sage: g.trivial_morphism()
            Traceback (most recent call last):
            ...
            NotImplementedError: disconnected decorated graph
        """
        if codomain is None:
            if not self._graph.is_connected():
                raise NotImplementedError('disconnected decorated graph')
            codomain = trivial_decorated_graph(self.genus(), self.markings())
        return DecoratedGraphMorphism(self, codomain, (0,) * self.num_verts(), {}, check=check)

    def relabelling_morphism(self, perm, codomain=None):
        r"""
        Return the relabelling from this graph to the one relabelled with the permutation
        ``perm`` of the vertices.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: g = DecoratedGraph([0, 1, 2], [[1], [1, 2], [1, 2, 3]], [(0, 0, 1), (0, 1, 1), (0, 2, 2)])
            sage: g.relabelling_morphism([0, 1, 2])
            DecoratedGraphMorphism(
                domain=DecoratedGraph([0, 1, 2], [[1], [2, 1], [3, 2, 1]], [(0, 1, 1), (0, 2, 2), (0, 0, 1)]),
                codomain=DecoratedGraph([0, 1, 2], [[1], [2, 1], [3, 2, 1]], [(0, 1, 1), (0, 2, 2), (0, 0, 1)]),
                vertex_images=(0, 1, 2),
                edge_preimages={(0, 0): {(0, 0): 1}, (0, 1): {(0, 1): 1}, (0, 2): {(0, 2): 2}})
            sage: g.relabelling_morphism([1, 0, 2])
            DecoratedGraphMorphism(
                domain=DecoratedGraph([0, 1, 2], [[1], [2, 1], [3, 2, 1]], [(0, 1, 1), (0, 2, 2), (0, 0, 1)]),
                codomain=DecoratedGraph([1, 0, 2], [[2, 1], [1], [3, 2, 1]], [(0, 1, 1), (1, 2, 2), (1, 1, 1)]),
                vertex_images=(1, 0, 2),
                edge_preimages={(0, 1): {(0, 1): 1}, (1, 1): {(0, 0): 1}, (1, 2): {(0, 2): 2}})
            sage: g.relabelling_morphism([1, 2, 0])
            DecoratedGraphMorphism(
                domain=DecoratedGraph([0, 1, 2], [[1], [2, 1], [3, 2, 1]], [(0, 1, 1), (0, 2, 2), (0, 0, 1)]),
                codomain=DecoratedGraph([2, 0, 1], [[3, 2, 1], [1], [2, 1]], [(0, 1, 2), (1, 2, 1), (1, 1, 1)]),
                vertex_images=(1, 2, 0),
                edge_preimages={(0, 1): {(0, 2): 2}, (1, 1): {(0, 0): 1}, (1, 2): {(0, 1): 1}})

        TESTS::

            sage: g = DecoratedGraph([0, 0, 0], [[], [], []], [(0, 1, 1), (0, 2, 1), (1, 2, 1)])
            sage: for aut in g.automorphism_group():
            ....:     assert g.relabelling_morphism(aut, codomain=g) == g.relabelling_morphism(aut)
        """
        if not isinstance(perm, (tuple, list, dict)):
            # assume we have an automorphism, ie a PermutationGroupElement
            perm = perm.domain()

        if codomain is None:
            codomain = self.copy(mutable=True)
            codomain.relabel(perm, inplace=True)
            codomain.set_immutable()

        return DecoratedGraphMorphism(self, codomain, perm, {(perm[u], perm[v]) if perm[u] < perm[v] else (perm[v], perm[u]): {(u, v): m} for u, v, m in self.edges()}, check=False)

    def vertex_partition(self):
        r"""
        Helper for canonical labelling and automorphism group.

        OUTPUT:

        a triple ``(partition, features, atom_id)`` where

        - ``partition`` - is a list of lists representating an ordered
          partition of the vertices. The partition is equivariant under
          relabelling.

        - ``features`` - is a list of tuples of the same length as
          ``partition``. Each element in this list represents a characteristic
          of the vertices in the corresponding atom of the partition.

        - ``atom_id`` - is a list of integers of the same length as the number
          of vertices in this graph such that the element at position ``v`` is
          the atom number of ``v`` in ``partition``

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: g = DecoratedGraph([0, 0, 0, 1], [[1], [], [], []], [(0, 1, 1), (0, 2, 1), (1, 1, 1), (2, 2, 1), (0, 3, 1)])
            sage: partition, features, atom_id = g.vertex_partition()
            sage: partition
            ((1, 2), (3,), (0,))
            sage: atom_id
            (2, 0, 0, 1)
        """
        try:
            return self._vertex_partition
        except AttributeError:
            pass
        nv = self._graph.num_verts()
        partition = defaultdict(list)
        for v in range(nv):
            markings = tuple(self._markings[v])
            multiplicities = tuple(sorted(self._graph.edge_label(v, w) for w in self._graph.neighbor_iterator(v)))
            dimension = 3 * self._genera[v] - 3 + 2 * self._loops[v] + sum(multiplicities) + len(markings)
            feature = (markings, dimension, self._genera[v], self._loops[v], multiplicities)
            partition[feature].append(v)
        atom_id = [None] * nv
        atoms = []

        features = sorted(partition)
        for i, key in enumerate(features):
            atoms.append(partition[key])
            for v in partition[key]:
                atom_id[v] = i

        ans = (tuple(tuple(atom) for atom in atoms), tuple(features), tuple(atom_id))
        if not self._mutable:
            self._vertex_partition = ans
        return ans

    def canonical_label(self, certificate=False):
        r"""
        Return a canonical labelling of this stable graph.

        The output is always immutable. Make a copy if you need to mutate it.
        If ``certificate`` is set to ``True`` also return a mapping.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: sg1 = DecoratedGraph([2, 1, 1], [[1], [1], [1]], [(0, 1, 1), (1, 2, 1)])
            sage: sg2 = DecoratedGraph([1, 2, 1], [[1], [1], [1]], [(1, 2, 1), (2, 0, 1)])
            sage: sg3 = DecoratedGraph([2, 1, 1], [[1], [2], [3]], [(0, 0, 1), (0, 1, 1), (1, 2, 1)])
            sage: sg4 = DecoratedGraph([2, 1, 1], [[3], [2], [1]], [(0, 0, 1), (1, 1, 2), (0, 1, 1), (1, 2, 1)])
            sage: sg5 = DecoratedGraph([0, 0, 0, 0], [[], [], [], []], [(0, 1, 2), (1, 2, 1), (2, 3, 2), (3, 0, 1)])

            sage: for sg in [sg1, sg2, sg3, sg4, sg5]:
            ....:     assert sg.is_isomorphic(sg.canonical_label()) and sg.canonical_label().is_isomorphic(sg)
            ....:     can, phi = sg.canonical_label(certificate=True)
            ....:     assert sg.relabel(phi, inplace=False) == can, sg
        """
        try:
            return self._canonical_label if certificate else self._canonical_label[0]
        except AttributeError:
            pass

        partition = self.vertex_partition()[0]
        nv = self._graph.num_verts()
        if all(len(atom) == 1 for atom in partition):
            # trivial partition
            perm = [None] * nv
            trivial_perm = True
            for i, atom in enumerate(partition):
                perm[atom[0]] = i
                trivial_perm &= atom[0] == i
            if trivial_perm:
                # trivial relabelling (avoids a lot of graph copies)
                h = self._graph.copy(immutable=True)
            else:
                h = self._graph.relabel(perm, inplace=False, immutable=True)
            perm = tuple(perm)
        else:
            h, perm = self._graph.canonical_label(partition=partition, edge_labels=True, certificate=True)
            h = static_sparse_graph(h)
            perm = tuple(perm[v] for v in range(nv))

        H = DecoratedGraph.__new__(DecoratedGraph)
        H._graph = h
        H._genera = [None] * nv
        H._loops = [None] * nv
        H._markings = [None] * nv
        H._mutable = False
        for v, g, l, m in zip(perm, self._genera, self._loops, self._markings):
            H._genera[v] = g
            H._loops[v] = l
            H._markings[v] = m[:]
        H._canonical_label = (H, tuple(range(nv)))
        canonical_label = (H, perm)
        if not self._mutable:
            self._canonical_label = canonical_label
        return canonical_label if certificate else canonical_label[0]

    def canonical_relabelling_morphism(self):
        r"""
        Return the morphism from this graph to its canonical labels.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: g = DecoratedGraph([0, 0, 0], [[], [], []], [(0, 0, 1), (0, 1, 1), (0, 2, 2)])
            sage: mor = g.canonical_relabelling_morphism()
            sage: mor # random
            sage: mor.codomain() == g.canonical_label()
            True
        """
        can, relabel = self.canonical_label(certificate=True)
        return self.relabelling_morphism(relabel, codomain=can)

    def is_isomorphic(self, other, certificate=False):
        r"""
        Return whether ``self`` and ``other`` are isomorphic.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: sg1 = DecoratedGraph([1, 1, 2], [[1], [1], [1]], [(0, 1, 1), (1, 2, 1)])
            sage: sg2 = DecoratedGraph([1, 2, 1], [[1], [1], [1]], [(1, 2, 1), (2, 0, 1)])
            sage: sg3 = DecoratedGraph([2, 1, 1], [[1], [1], [1]], [(0, 1, 1), (1, 2, 1)])
            sage: for s in [sg1, sg2, sg3]:
            ....:     for t in [sg1, sg2, sg3]:
            ....:         ans = s.is_isomorphic(t)
            ....:         assert ans, (s, t)
            ....:         ans, phi = s.is_isomorphic(t, certificate=True)
            ....:         assert ans, (s, t)
            ....:         assert s.relabel(phi) == t

            sage: sg1 = DecoratedGraph([1, 1, 2], [[1], [2], [3]], [(0, 0, 1), (0, 1, 1), (1, 2, 1)])
            sage: sg2 = DecoratedGraph([1, 2, 1], [[1], [3], [2]], [(0, 0, 1), (1, 2, 1), (2, 0, 1)])
            sage: sg3 = DecoratedGraph([2, 1, 1], [[3], [2], [1]], [(2, 2, 1), (0, 1, 1), (1, 2, 1)])
            sage: for s in [sg1, sg2, sg3]:
            ....:     for t in [sg1, sg2, sg3]:
            ....:         ans = s.is_isomorphic(t)
            ....:         assert ans, (s, t)
            ....:         ans, phi = s.is_isomorphic(t, certificate=True)
            ....:         assert ans, (s, t)
            ....:         assert s.relabel(phi) == t
            sage: sg4 = DecoratedGraph([2, 1, 1], [[3], [2], [1]], [(2, 2, 2), (0, 1, 1), (1, 2, 1)])
            sage: sg3.is_isomorphic(sg4)
            False
        """
        partition_self, features_self, _ = self.vertex_partition()
        partition_other, features_other, _ = other.vertex_partition()
        if features_self != features_other or any(len(atom_self) != len(atom_other) for atom_self, atom_other in zip(partition_self, partition_other)):
            return (False, None) if certificate else False

        if not certificate:
            return self.canonical_label() == other.canonical_label()
        H1, phi = self.canonical_label(True)
        H2, psi = other.canonical_label(True)
        if H1 == H2:
            nv = len(self._genera)
            psi_inv = [None] * nv
            for i, j in enumerate(psi):
                psi_inv[j] = i
            return (True, [psi_inv[phi[i]] for i in range(nv)])
        else:
            return (False, None)

    def automorphism_group(self):
        r"""
        Return the automorphism group of the underlying graph.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: DecoratedGraph([1, 1, 1], [[], [], []], [(0, 1, 1), (0, 2, 1), (1, 2, 1)]).automorphism_group()
            Permutation Group with generators [(1,2), (0,1)]
            sage: DecoratedGraph([1, 1, 1], [[1], [1], [2]], [(0, 1, 1), (0, 2, 1), (1, 2, 1)]).automorphism_group()
            Permutation Group with generators [(0,1)]
            sage: DecoratedGraph([1, 1, 1], [[], [], []], [(0, 1, 1), (1, 2, 1)]).automorphism_group()
            Permutation Group with generators [(0,2)]
            sage: DecoratedGraph([1, 1, 1], [[], [], []], [(0, 1, 1), (1, 2, 2)]).automorphism_group()
            Permutation Group with generators [()]
            sage: DecoratedGraph([1, 1, 2], [[], [], []], [(0, 1, 1), (1, 2, 1)]).automorphism_group()
            Permutation Group with generators [()]
        """
        try:
            return self._automorphism_group
        except AttributeError:
            pass
        partition = self.vertex_partition()[0]
        if all(len(atom) == 1 for atom in partition):
            group = PermutationGroup([[]], domain=list(self.vertices()))
        else:
            group = self._graph.automorphism_group(partition=partition, edge_labels=True)
            # TODO: graph automorphism makes crazy domain when there is a partition
            # sage: g = Graph([(0,1),(1,2)])
            # sage: g.automorphism_group(partition=[(1,),(0,2)])
            # PermutationsGroup with generators [(0,2)]
            # sage: g.automorphism_group(partition=[(1,),(0,2)]).domain()
            # {1, 0, 2}
            if list(group.domain()) != list(range(self.num_verts())):
                group = PermutationGroup(group.gens(), domain=list(range(self.num_verts())))
        if not self._mutable:
            self._automorphism_group = group
        return group

    def vertices_are_in_same_orbit(self, v1, v2, check=True):
        r"""
        Return whether the vertices ``v1`` and ``v2`` belong to the same orbit
        under the automorphism group of this graph.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: stg = DecoratedGraph([1, 1, 1], [[], [], []], [(0, 1, 1), (1, 2, 1)])
            sage: [(u, v) for u in stg.vertices() for v in stg.vertices() if stg.vertices_are_in_same_orbit(u, v)]
            [(0, 0), (0, 2), (1, 1), (2, 0), (2, 2)]
        """
        if check:
            v1 = self._check_vertex(v1)
            v2 = self._check_vertex(v2)

        # equality
        if v1 == v2:
            return True

        # try to avoid computing the automorphism group by looking at the vertex partition
        atom_id = self.vertex_partition()[2]
        if atom_id[v1] != atom_id[v2]:
            return False

        group = self.automorphism_group()
        if all(g.is_one() for g in group.gens()):
            # trivial automorphism group
            return False
        v1 = group._domain_to_gap[v1]
        v2 = group._domain_to_gap[v2]
        return libgap.RepresentativeAction(group, v1, v2) != libgap.fail

    def edge_orbit_representatives(self):
        r"""
        Return a list of representatives of edge orbits under the action
        of the automorphism group.

        The output is a list of triples ``(u, v, orbit_size)`` where ``(u, v)``
        is an edge and ``orbit_size`` the size of its orbit under the
        automorphism group.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: DecoratedGraph([0, 0, 0], [[], [], []], [(0, 0, 1), (0, 1, 1), (1, 1, 1), (1, 2, 1), (2, 2, 1)]).edge_orbit_representatives()
            [(0, 1, 2), (0, 0, 2), (1, 1, 1)]
        """
        aut = self.automorphism_group()
        if is_trivial_group(aut):
            return [(u, v, 1) for u, v in self.edges(multiplicities=False)]

        edges = []
        for u, v in self._graph.edges(labels=False, sort=False):
            U = aut._domain_to_gap[u]
            V = aut._domain_to_gap[v]
            edges.append([U, V] if U <= V else [V, U])
        edge_orbits = libgap.Orbits(aut, edges, libgap.OnSets)

        loops = [aut._domain_to_gap[u] for u in self.vertices() if self._loops[u]]
        loop_orbits = libgap.Orbits(libgap(aut), loops, libgap.OnPoints)

        return [(aut._domain_from_gap[int(orbit[0][0])], aut._domain_from_gap[int(orbit[0][1])], int(orbit.Size())) for orbit in edge_orbits] + [(aut._domain_from_gap[int(orbit[0])], aut._domain_from_gap[int(orbit[0])], int(orbit.Size())) for orbit in loop_orbits]

    def edges_are_in_same_orbit(self, u1, v1, u2, v2, oriented=True, check=True):
        r"""
        Return whether the edges ``(u1, v1)`` and ``(u2, v2)`` belong to the same orbit
        under the automorphism group of this graph.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: stg = DecoratedGraph([1, 1, 1], [[], [], []], [(0, 0, 1), (0, 1, 1), (1, 2, 1), (2, 2, 1)])
            sage: edges = list(stg.edges(multiplicities=False))
            sage: edges.extend([(v,u) for u,v in edges if u != v])
            sage: [(e1, e2) for e1 in edges for e2 in edges if stg.edges_are_in_same_orbit(*e1, *e2) if e1 != e2]
            [((0, 1), (2, 1)),
             ((1, 2), (1, 0)),
             ((0, 0), (2, 2)),
             ((2, 2), (0, 0)),
             ((1, 0), (1, 2)),
             ((2, 1), (0, 1))]
            sage: [(e1, e2) for e1 in edges for e2 in edges if stg.edges_are_in_same_orbit(*e1, *e2, oriented=False) if e1 != e2]
            [((0, 1), (1, 2)),
             ((0, 1), (1, 0)),
             ((0, 1), (2, 1)),
             ((1, 2), (0, 1)),
             ((1, 2), (1, 0)),
             ((1, 2), (2, 1)),
             ((0, 0), (2, 2)),
             ((2, 2), (0, 0)),
             ((1, 0), (0, 1)),
             ((1, 0), (1, 2)),
             ((1, 0), (2, 1)),
             ((2, 1), (0, 1)),
             ((2, 1), (1, 2)),
             ((2, 1), (1, 0))]
        """
        if check:
            u1, v1 = self._check_edge(u1, v1)
            u2, v2 = self._check_edge(u2, v2)

        # equality
        if (u1, v1) == (u2, v2) or (not oriented and (u1, v1) == (v2, u2)):
            return True

        # loop case
        if u1 == v1 or u2 == v2:
            return u1 == v1 and u2 == v2 and self._loops[u1] and self._loops[u2] and self.vertices_are_in_same_orbit(u1, u2)

        # try to avoid computing the automorphism group by looking at the vertex partition
        atom_id = self.vertex_partition()[2]
        if oriented:
            if (atom_id[u1], atom_id[v1]) != (atom_id[u2], atom_id[v2]):
                return False
        elif (atom_id[u1], atom_id[v1]) != (atom_id[u2], atom_id[v2]) and (atom_id[u1], atom_id[v1]) != (atom_id[v2], atom_id[u2]):
            return False

        group = self.automorphism_group()
        if is_trivial_group(group):
            return False
        u1 = group._domain_to_gap[u1]
        v1 = group._domain_to_gap[v1]
        u2 = group._domain_to_gap[u2]
        v2 = group._domain_to_gap[v2]
        e1 = [u1, v1]
        e2 = [u2, v2]
        if oriented:
            return libgap.RepresentativeAction(group, e1, e2, libgap.OnTuples) != libgap.fail
        else:
            e1 = sorted(e1)
            e2 = sorted(e2)
            return libgap.RepresentativeAction(group, e1, e2, libgap.OnSets) != libgap.fail

    #############
    # Surgeries #
    #############

    def contract_edge(self, u, v):
        r"""
        Contract an edge between the vertices ``u`` and ``v``.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: sg = DecoratedGraph([0], [[]], [(0, 0, 2)], mutable=True)
            sage: sg.contract_edge(0, 0)
            sage: sg
            DecoratedGraph([1], [[]], [(0, 0, 1)], mutable=True)

            sage: sg = DecoratedGraph([0, 1], [[2, 1], [3, 1]], [(0, 1, 1)], mutable=True)
            sage: sg.contract_edge(0, 1)
            sage: sg
            DecoratedGraph([1], [[3, 2, 1, 1]], [], mutable=True)

            sage: sg = DecoratedGraph([0, 1], [[2, 1], [3, 1]], [(0, 0, 1), (1, 1, 1), (0, 1, 3)], mutable=True)
            sage: sg.contract_edge(0, 1)
            sage: sg
            DecoratedGraph([1], [[3, 2, 1, 1]], [(0, 0, 4)], mutable=True)
        """
        if not self._mutable:
            raise ValueError('immutable graph')
        u, v = self._check_edge(u, v)
        if u == v:
            if self._loops[u] == 0:
                raise ValueError('not an edge in this stable graph')
            self._loops[u] -= 1
            self._genera[u] += 1
        else:
            if u > v:
                u, v = v, u
            graph = self._graph
            mult = graph.edge_label(u, v)
            neighbors = [(w, self._graph.edge_label(v, w)) for w in graph.neighbor_iterator(v) if w != u]
            graph.delete_vertex(v)
            for w, m in neighbors:
                if graph.has_edge(u, w):
                    graph.set_edge_label(u, w, graph.edge_label(u, w) + m)
                else:
                    graph.add_edge(u, w, m)
            self._genera[u] += self._genera[v]
            self._genera.pop(v)
            self._loops[u] += self._loops[v] + mult - 1
            self._loops.pop(v)
            if self._markings[v]:
                self._markings[u] += self._markings[v]
                self._markings[u].sort(reverse=True)
            self._markings.pop(v)
            self._graph.relabel()

    def edge_contraction_morphism(self, edges, check=True):
        r"""
        Return the morphism obtained by contracting ``edges``.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph

            sage: sg = DecoratedGraph([0], [[]], [(0, 0, 2)])
            sage: sg.edge_contraction_morphism([(0, 0, 1)])
            DecoratedGraphMorphism(
                domain=DecoratedGraph([0], [[]], [(0, 0, 2)]),
                codomain=DecoratedGraph([1], [[]], [(0, 0, 1)]),
                vertex_images=(0,),
                edge_preimages={(0, 0): {(0, 0): 1}})
            sage: sg.edge_contraction_morphism([(0, 0, 2)])
            DecoratedGraphMorphism(
                domain=DecoratedGraph([0], [[]], [(0, 0, 2)]),
                codomain=DecoratedGraph([2], [[]], []),
                vertex_images=(0,),
                edge_preimages={})

            sage: sg = DecoratedGraph([0, 1], [[2, 1], [3, 1]], [(0, 0, 1), (1, 1, 1), (0, 1, 3)])
            sage: sg.edge_contraction_morphism([(0, 1, 1)])
            DecoratedGraphMorphism(
                domain=DecoratedGraph([0, 1], [[2, 1], [3, 1]], [(0, 1, 3), (0, 0, 1), (1, 1, 1)]),
                codomain=DecoratedGraph([1], [[3, 2, 1, 1]], [(0, 0, 4)]),
                vertex_images=(0, 0),
                edge_preimages={(0, 0): {(0, 0): 1, (0, 1): 2, (1, 1): 1}})
            sage: sg.edge_contraction_morphism([(0, 0, 1), (0, 1, 2)])
            DecoratedGraphMorphism(
                domain=DecoratedGraph([0, 1], [[2, 1], [3, 1]], [(0, 1, 3), (0, 0, 1), (1, 1, 1)]),
                codomain=DecoratedGraph([3], [[3, 2, 1, 1]], [(0, 0, 2)]),
                vertex_images=(0, 0),
                edge_preimages={(0, 0): {(0, 1): 1, (1, 1): 1}})

            sage: g = DecoratedGraph([0, 1, 0], [[], [], []], [(0, 2, 3), (1, 2, 1)])
            sage: g.edge_contraction_morphism([(1, 2, 1)])
            DecoratedGraphMorphism(
                domain=DecoratedGraph([0, 1, 0], [[], [], []], [(0, 2, 3), (1, 2, 1)]),
                codomain=DecoratedGraph([0, 1], [[], []], [(0, 1, 3)]),
                vertex_images=(0, 1, 1),
                edge_preimages={(0, 1): {(0, 2): 3}})

            sage: g = DecoratedGraph([0, 0, 0], [[], [], [1]], [(0, 1, 1), (1, 2, 2), (0, 0, 1)])
            sage: g.edge_contraction_morphism([(0, 1, 1)])
            DecoratedGraphMorphism(
                domain=DecoratedGraph([0, 0, 0], [[], [], [1]], [(0, 1, 1), (1, 2, 2), (0, 0, 1)]),
                codomain=DecoratedGraph([0, 0], [[], [1]], [(0, 1, 2), (0, 0, 1)]),
                vertex_images=(0, 0, 1),
                edge_preimages={(0, 0): {(0, 0): 1}, (0, 1): {(1, 2): 2}})
        """
        if check:
            for u, v, m in edges:
                u, v = self._check_edge(u, v)
                if m > self.edge_multiplicity(u, v):
                    raise ValueError('invalid edges')

        nv = self.num_verts()
        codomain = self.copy(mutable=True)
        graph = codomain._graph
        genera = codomain._genera
        loops = codomain._loops
        markings = codomain._markings
        U = DisjointSet_of_integers(nv)
        remaining_edges = {(u, v): uv_mult for u, v, uv_mult in self.edges()}
        for u, v, m in edges:
            ru = U.find(u)
            rv = U.find(v)
            if ru == rv:
                # loop contraction, nothing to do on the graph
                genera[ru] += m
                loops[ru] -= m
            else:
                if ru > rv:
                    ru, rv = rv, ru

                mult = graph.edge_label(ru, rv)
                neighbors = [(w, graph.edge_label(rv, w)) for w in graph.neighbor_iterator(v) if w != u]
                graph.delete_vertex(rv)
                for w, w_mult in neighbors:
                    if graph.has_edge(u, w):
                        graph.set_edge_label(u, w, graph.edge_label(u, w) + w_mult)
                    else:
                        graph.add_edge(u, w, w_mult)

                loops[ru] += mult - m + loops[rv]
                genera[ru] += genera[rv] + m - 1
                if markings[rv]:
                    markings[ru].extend(markings[rv])
                    markings[ru].sort(reverse=True)
                U.union(u, v)
            remaining_edges[(u, v)] -= m
            assert remaining_edges[(u, v)] >= 0

        roots = [i for i in range(nv) if U.find(i) == i]
        roots_relabelling = {r: i for i, r in enumerate(roots)}
        graph.relabel(roots_relabelling)
        codomain._loops = [loops[r] for r in roots]
        codomain._genera = [genera[r] for r in roots]
        codomain._markings = [markings[r] for r in roots]
        codomain.set_immutable()

        vertex_images = [roots_relabelling[U.find(v)] for v in self.vertices()]

        edge_preimages = {}
        for (u, v), m in remaining_edges.items():
            if not m:
                continue
            im_u = roots_relabelling[U.find(u)]
            im_v = roots_relabelling[U.find(v)]
            if im_u > im_v:
                im_u, im_v = im_v, im_u
            if (im_u, im_v) not in edge_preimages:
                edge_preimages[(im_u, im_v)] = {}
            assert (u, v) not in edge_preimages[(im_u, im_v)]
            edge_preimages[(im_u, im_v)][(u, v)] = m

        return DecoratedGraphMorphism(self, codomain, vertex_images, edge_preimages, check=check)

    def canonical_edge(self):
        r"""
        Return the canonical edge of this graph.

        The canonical edge is oriented. In the output ``(u, v)`` the first
        vertex is the canonical vertex.

        The canonical edge is a choice of an edge which is unique up to the
        automorphism group and invariant under relabelling. It is chosen as
        follows. First the :meth:`vertex_partition` determines a partition
        of the vertices into groups. We consider only edges with one end
        in the last group and its second end maximum possible. Then we
        further discriminate by prioritizing loops and higher multiplicity.
        Finally, in case of ties (or presence of automorphisms) we rely
        on canonical labellings of the underlying graph. This last step
        depends on the particular SageMath version you run and whether bliss is
        present on your machine. The notion of canonical edge is hence
        consistent on a given machine but might differ in distinct setups.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: gr = DecoratedGraph([1,1,1,1], [[], [], [], []], [(0, 1, 1), (0, 2, 1), (0, 3, 1)])
            sage: gr.canonical_edge()  # random
            (0, 3)

            sage: gr = DecoratedGraph([0, 0, 0, 0], [[1], [2], [], []], [(0, 2, 2), (1, 3, 2), (2, 3, 1)])
            sage: e = gr.canonical_edge()
            sage: gr.edge_is_canonical(e[0], e[1])
            True
            sage: gr.edge_is_canonical(e[1], e[0])
            False

        TESTS::

            sage: from admcycles.decorated_graph import stable_graphs
            sage: for (g, n) in [(0, 5), (1, 2), (3, 0)]:
            ....:     dim = 3 * g - 3 + n
            ....:     sgs = stable_graphs(g, n, dim)
            ....:     for r in range(1, dim + 1):
            ....:         for st in sgs[r]:
            ....:             perm = list(range(st.num_verts()))
            ....:             for _ in range(10):
            ....:                 shuffle(perm)
            ....:                 st2 = st.relabel(perm)
            ....:                 u, v = st.canonical_edge()
            ....:                 u2, v2 = st2.canonical_edge()
            ....:                 assert st2.edge_is_canonical(perm[u], perm[v])
            ....:                 assert st2.edge_is_canonical(u2, v2)
            ....:                 assert st2.edges_are_in_same_orbit(perm[u], perm[v], u2, v2), (st, perm)
        """
        if self._graph.num_edges() == 0 and not any(self._loops):
            raise ValueError('stable graph with no edge')

        partition, _, atom_id = self.vertex_partition()

        max_atom = len(partition) - 1
        max_part = partition[max_atom]
        vmax = max_part[0]
        if self._loops[vmax]:
            if len(max_part) == 1:
                return (vmax, vmax)
            _, phi = self.canonical_label(certificate=True)
            vmax = max(max_part, key=lambda v: phi[v])
            return (vmax, vmax)

        max_atom_neighbor = 0
        for v in max_part:
            if max_atom_neighbor == max_atom:
                break
            max_atom_neighbor = max(max_atom_neighbor, max(atom_id[w] for w in self._graph.neighbor_iterator(v)))

        candidates = [(u, v, self._graph.edge_label(u, v)) for u in partition[-1] for v in self._graph.neighbor_iterator(u) if atom_id[v] == max_atom_neighbor]
        max_edge = max(m for _, _, m in candidates)
        candidates = [(u, v) for u, v, m in candidates if m == max_edge]
        if len(candidates) == 1:
            return candidates[0]
        _, phi = self.canonical_label(certificate=True)
        return max(candidates, key=lambda x: (phi[x[0]], phi[x[1]]))

    def edge_is_canonical(self, u, v, check=True):
        r"""
        Return whether the edge ``(u, v)`` is canonical.

        This function is one of the crucial ingredient to make isomorphism-free
        generation of stable graphs as in [MKa98]_.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: g = DecoratedGraph([1, 1], [[], []], [(0, 1, 1)])
            sage: g.canonical_edge() # random
            (0, 1)
            sage: g.edge_is_canonical(0, 1)
            True
            sage: g.edge_is_canonical(1, 0)
            True
        """
        if check:
            if self._graph.num_edges() == 0 and not any(self._loops):
                raise ValueError('stable graph with no edge')
            u, v = self._check_edge(u, v)

        # only perform some quick False
        # (quick True are done automatically)
        partition, _, atom_id = self.vertex_partition()
        max_atom = len(partition) - 1
        if atom_id[u] != max_atom or atom_id[v] > atom_id[u]:
            return False
        max_loop = max(self._loops[v] for v in partition[-1])
        if max_loop:
            if u != v or self._loops[u] != max_loop:
                return False
        elif atom_id[u] != atom_id[v]:
            uv_mult = self._graph.edge_label(u, v)
            if any(atom_id[w2] > atom_id[v] or (atom_id[w2] == atom_id[v] and self._graph.edge_label(w, w2) > uv_mult) for w in partition[-1] for w2 in self._graph.neighbor_iterator(w)):
                return False

        umax, vmax = self.canonical_edge()
        return self.edges_are_in_same_orbit(u, v, umax, vmax, oriented=True, check=check)

    def degenerate_non_separating(self, v):
        r"""
        Steal a genus at ``v`` to create a loop.

        INPUT:

        v: integer
          a vertex in the graph with genus at least one

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: sg = DecoratedGraph([1, 1], [[], []], [(0, 1)], mutable=True)
            sage: sg.degenerate_non_separating(0)
            sage: sg
            DecoratedGraph([0, 1], [[], []], [(0, 1, 1), (0, 0, 1)], mutable=True)
        """
        if not self._mutable:
            raise ValueError("immutable graph; use a copy")
        v = self._check_vertex(v)
        if not self._genera[v]:
            raise ValueError("no genus availabe at vertex v")
        self._genera[v] -= 1
        self._loops[v] += 1

    def degenerate_separating(self, v, mult, g, markings, loops, edges, check=True):
        r"""
        Degenerate the vertex ``v`` into two vertices.

        The newly created vertex gets label ``nv`` where ``nv`` is the number
        of vertices of the this graph. This new vertex steals some of the
        markings, genus and edges of ``v``. The original graph can be retrieved
        by contracting the edge between vertex ``v`` and ``nv``. See
        :meth:`contract_edge` and the examples below.

        INPUT:

        v: integer
          the vertex to be split

        mult: positive integer
          the multiplicity of the edges between ``v`` and ``nv`` after
          the splitting

        g: non-negative integer
          the genus of the newly created vertex ``nv``

        markings: list of non-negative integers
          the markings to be put on ``nv``

        edges: list of pairs ``(u, m)``
          the list of neighbors of ``v`` with multiplicities that
          are transplanted on ``nv``.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: sg = DecoratedGraph([0], [[2, 1]], [(0, 0, 1)], mutable=True)
            sage: sg.degenerate_separating(0, 2, 0, [2], 0, [])
            sage: sg
            DecoratedGraph([0, 0], [[1], [2]], [(0, 1, 2)], mutable=True)
            sage: sg.contract_edge(0, 1)
            sage: sg
            DecoratedGraph([0], [[2, 1]], [(0, 0, 1)], mutable=True)

            sage: sg = DecoratedGraph([3, 0, 0],[[1], [1], []], [(0, 0, 3), (0, 1, 3), (0, 2, 1)], mutable=True)
            sage: sg.degenerate_separating(0, 2, 1, [1], 2, [(1, 1), (2, 0)])
            sage: sg
            DecoratedGraph([2, 0, 0, 1], [[], [1], [], [1]], [(0, 1, 2), (0, 2, 1), (0, 3, 2), (1, 3, 1), (3, 3, 2)], mutable=True)
            sage: sg.contract_edge(0, 3)
            sage: sg
            DecoratedGraph([3, 0, 0], [[1], [1], []], [(0, 1, 3), (0, 2, 1), (0, 0, 3)], mutable=True)
        """
        if not self._mutable:
            raise ValueError("immutable graph")

        if check:
            v = self._check_vertex(v)
            if not isinstance(g, numbers.Integral):
                raise ValueError("invalid genera")
            g = int(g)
            if g < 0 or g > self._genera[v]:
                raise ValueError("invalid genera")
            if not isinstance(mult, numbers.Integral):
                raise ValueError("invalid multiplicity")
            mult = int(mult)
            if not isinstance(loops, numbers.Integral):
                raise ValueError("invalid loops")
            loops = int(loops)
            if mult <= 0 or mult + loops - 1 > self._loops[v]:
                raise ValueError("invalid loops and multiplicity")

        nv = len(self._genera)
        self._graph.add_vertex(nv)
        self._graph.add_edge(v, nv, mult)

        self._genera.append(g)
        self._genera[v] -= g

        self._markings.append([])
        for i in markings:
            self._markings[v].remove(i)
            self._markings[nv].append(i)

        self._loops.append(0)
        self._loops[v] -= mult + loops - 1
        self._loops[nv] = loops

        for w, m in edges:
            if check:
                if not isinstance(m, numbers.Integral):
                    raise ValueError("invalid edges")
                m = int(m)
                if m < 0:
                    raise ValueError("invalid edges")
                if not self._graph.has_edge(v, w):
                    raise ValueError("invalid edges")
            vw_mult = self._graph.edge_label(v, w)
            if m > vw_mult:
                raise ValueError("invalid edges")
            elif m == vw_mult:
                self._graph.delete_edge(v, w)
            else:
                self._graph.set_edge_label(v, w, vw_mult - m)
            if m:
                self._graph.add_edge(nv, w, m)

    def _canonical_splitting_data(self, v,
                                  min_multiplicity,
                                  max_multiplicity,
                                  min_genus,
                                  max_genus):
        r"""
        Iterate through all the 5-tuples ``(mult, g, marking, loops, edges)``
        to be fed to :meth:`degenerate_separating`.

        If ``up_to_automorphism`` is set to ``True`` then only generate data up
        to the automorphism group. If ``skip_non_canonical`` is set to ``True``
        then ignores data that will not generate canonical degenerations.
        Though it is not guaranteed that the data will generate canonical
        degenerations.
        """
        # The vertex we create (corresponding to the data
        # (edges0, markings0, loops0)) must be a vertex in the maximal
        # partition in the target.
        # TODO: the second vertex (corresponding to the data
        # (edges1, markings1, loops1)) can not be too small. Implement
        # the proper bounds
        # TODO: in some instances, we could shortcut the iteration based on
        # stability and dimensions

        # v must be in the largest partition after the splitting. Hence, it
        # must be alone in partition[-1] because the splitting will necessarily
        # decrease the vertex features.
        partition, features, atom_id = self.vertex_partition()
        max_atom = len(partition) - 1
        if atom_id[v] != max_atom or len(partition[max_atom]) > 1:
            return
        snd_feature = None if len(features) == 1 else features[max_atom - 1]

        g = self._genera[v]
        l = self._loops[v]
        if min_genus > g:
            return
        if min_multiplicity > l + 1:
            return

        markings = self._markings[v]
        neighbors = list(self._graph.neighbor_iterator(v))
        edge_mults = [self._graph.edge_label(v, w) for w in neighbors]

        # stability condition
        stab = 2 * g + 2 * l + sum(edge_mults) + len(markings)
        dim = features[max_atom][1]
        assert stab >= 3
        if stab == 3:
            return

        # automorphisms (when required)
        group = self.automorphism_group()
        if not is_trivial_group(group):
            # compute the action of the stabilizer of v on neighbours
            gens = []
            for gen in group.stabilizer(v):
                gen = [gen(v) for v in neighbors]
                if gen != neighbors:  # not the identity
                    gens.append(gen)
            group = None
            if gens:
                group = PermutationGroup(gens, domain=neighbors)
                if is_trivial_group(group):
                    group = None
        else:
            group = None

        def split_edges():
            yield from integer_lists_mod_perm_group(0, sum(edge_mults), [0] * len(neighbors), edge_mults, group)

        def split_loops():
            return range(min_multiplicity, max_multiplicity + 1)

        parts, marking_mults = to_exp_list(markings)

        def split_markings():
            if not markings:
                return iter([()])

            # the largest marking must go (as it is the first item in vertex features)
            return itertools.product(*(range(i == 0, c + 1) for i, c in enumerate(marking_mults)))

        def split_genus():
            return range(min_genus, max_genus + 1)

        # NOTE: all loops must go to the other vertex (the smaller one) because we put
        # priority on loops for canonical_edge
        l0 = 0
        for edges0_mults in split_edges():
            for markings0_mults in split_markings():
                for g0 in split_genus():
                    for mult in split_loops():
                        # check stability condition
                        l1 = l - mult + 1
                        g1 = g - g0
                        edges1_mults = [m - m0 for m, m0 in zip(edge_mults, edges0_mults)]
                        markings1_mults = tuple([m - m0 for m, m0 in zip(marking_mults, markings0_mults)])
                        stab0 = mult + 2 * g0 + 2 * l0 + sum(edges0_mults) + sum(markings0_mults)
                        stab1 = mult + 2 * g1 + 2 * l1 + sum(edges1_mults) + sum(markings1_mults)
                        assert stab0 + stab1 == stab + 2
                        if stab0 >= 3 and stab1 >= 3:
                            dim0 = stab0 + g0 - 3
                            dim1 = stab1 + g1 - 3
                            assert dim == dim0 + dim1 + 1
                            markings0 = sum(((c,) * m for c, m in zip(parts, markings0_mults)), ())
                            markings1 = sum(((c,) * m for c, m in zip(parts, markings1_mults)), ())
                            mults0 = [m for m in edges0_mults if m]
                            mults0.append(mult)
                            mults0.sort()
                            mults0 = tuple(mults0)
                            mults1 = [m for m in edges1_mults if m]
                            mults1.append(mult)
                            mults1.sort()
                            mults1 = tuple(mults1)
                            new_feature0 = (markings0, dim0, g0, l0, mults0)
                            new_feature1 = (markings1, dim1, g1, l1, mults1)
                            if new_feature1 > new_feature0:
                                continue
                            # NOTE: we can not compare the full features since the
                            # multiplicities of snd_feature might change after splitting
                            if snd_feature is not None and new_feature0[:4] < snd_feature[:4]:
                                continue
                            if any(new_feature1[:4] < features[atom_id[w]][:4] for w, m in zip(neighbors, edges0_mults) if m):
                                continue
                            yield (mult, g0, markings0, l0, [(w, m) for w, m in zip(neighbors, edges0_mults) if m])

    def canonical_degenerations(self, target_max_moduli=None, current_moduli=None, target_moduli=None, mutable=False, verbose=False):
        r"""
        Iterate through the canonical degenerations of this stable graph.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: sg = DecoratedGraph([0, 0, 0, 0], [[2, 1], [4, 3], [], []], [(0, 2, 1), (1, 3, 1), (2, 3, 2)])
            sage: u, v = sg.canonical_edge()
            sage: sg2 = sg.copy(mutable=True)
            sage: sg2.contract_edge(u, v)
            sage: sg2.set_immutable()
            sage: assert(sg.canonical_label() in [sg3.canonical_label() for sg3 in sg2.canonical_degenerations()])

        TESTS::

            sage: def by_moduli(graph_list):
            ....:     answer = [set() for _ in range(5)]
            ....:     for g in graph_list:
            ....:         answer[g.moduli()].add(g)
            ....:     return answer

        From smooth::

            sage: for g in [DecoratedGraph([0], [[1, 2, 3, 4, 5]], []),
            ....:           DecoratedGraph([3], [[]], []),
            ....:           DecoratedGraph([3], [[1]], []),
            ....:           DecoratedGraph([3], [[2, 1]], [])]:
            ....:     l1 = by_moduli(g.canonical_degenerations())
            ....:     l2 = [set(g.canonical_degenerations(current_moduli=0, target_moduli=m)) for m in range(5)]
            ....:     assert l1 == l2

        From rational tail not smooth::

            sage: for g in [DecoratedGraph([0, 0], [[3, 2, 1], [3, 2, 1]], [(0, 1, 1)]),
            ....:           DecoratedGraph([1, 0], [[2, 1], [1, 1]], [(0, 1, 1)]),
            ....:           DecoratedGraph([1, 0], [[1, 1], [2, 1]], [(0, 1, 1)])]:
            ....:     l1 = by_moduli(g.canonical_degenerations())
            ....:     assert not l1[0]
            ....:     del l1[0]
            ....:     l2 = [set(g.canonical_degenerations(current_moduli=1, target_moduli=m)) for m in range(1, 5)]
            ....:     assert l1 == l2

        From compact type not rational tails::

            sage: for g in [DecoratedGraph([1, 1], [[3, 2, 1], [3, 2, 1]], [(0, 1, 1)]),
            ....:           DecoratedGraph([2, 1], [[2, 1], [1, 1]], [(0, 1, 1)]),
            ....:           DecoratedGraph([2, 1], [[1, 1], [2, 1]], [(0, 1, 1)])]:
            ....:     l1 = by_moduli(g.canonical_degenerations())
            ....:     assert not l1[0] and not l1[1]
            ....:     del l1[0:2]
            ....:     l2 = [set(g.canonical_degenerations(current_moduli=2, target_moduli=m)) for m in range(2, 5)]
            ....:     assert l1 == l2

        From tree like not compact type::

            sage: for g in [DecoratedGraph([0, 0], [[3, 2, 1], [3, 2, 1]], [(0, 1, 1), (1, 1, 1)]),
            ....:           DecoratedGraph([1, 0], [[2, 1], [1, 1]], [(0, 1, 1), (1, 1, 3)]),
            ....:           DecoratedGraph([1, 0], [[1, 1], [2, 1]], [(0, 1, 1), (1, 1, 3)])]:
            ....:     l1 = by_moduli(g.canonical_degenerations())
            ....:     assert not l1[0] and not l1[1] and not l1[2]
            ....:     del l1[0:3]
            ....:     l2 = [set(g.canonical_degenerations(current_moduli=3, target_moduli=m)) for m in range(3, 5)]
            ....:     assert l1 == l2

        From stable not tree like::

            sage: for g in [DecoratedGraph([1, 0, 0, 0, 0], [[], [], [], [], []], [(i, j, 1) for i in range(5) for j in range(i, 5)]),
            ....:           DecoratedGraph([1, 0], [[], []], [(0, 1, 4)])]:
            ....:     l1 = by_moduli(g.canonical_degenerations())
            ....:     assert not l1[0] and not l1[1] and not l1[2] and not l1[3]
            ....:     del l1[0:4]
            ....:     l2 = [set(g.canonical_degenerations(current_moduli=4, target_moduli=m)) for m in range(4, 5)]
            ....:     assert l1 == l2
        """
        if target_moduli is None and target_max_moduli is None:
            target_max_moduli = MODULI_ST
        elif target_moduli is not None and target_max_moduli is not None:
            raise ValueError('at most one of target_moduli and target_max_moduli could be set')
        if target_moduli is not None:
            assert current_moduli is not None and target_moduli >= current_moduli
            if target_moduli == MODULI_SM:
                return
        elif target_max_moduli == MODULI_SM:
            return

        nv = self._graph.num_verts()
        if nv == 1:
            v = 0
        else:
            partition, features, atom_id = self.vertex_partition()
            # we must have a single vertex of maximal dimension
            # the dimension is the element at index 1 of vertex features
            if len(partition[-1]) > 1 or (features[-1][0] == () and features[-1][1] == features[-2][1]):
                return
            v = partition[-1][0]

        g = self._genera[v]
        l = self._loops[v]

        if g > 0:
            if target_moduli is None:
                create_loop = target_max_moduli >= MODULI_TL
            else:
                if target_moduli < MODULI_TL:
                    create_loop = False
                elif target_moduli == MODULI_TL:
                    create_loop = True
                else:
                    create_loop = current_moduli == MODULI_ST
        else:
            create_loop = False

        # loop creation
        if create_loop:
            possibly_canonical = True
            if nv > 1 and len(features) > 1:
                markings, dimension, g, l, mults = features[-1]
                new_feature = (markings, dimension - 1, g - 1, l + 1, mults)
                if new_feature < features[-2]:
                    possibly_canonical = False
            if possibly_canonical:
                sg = self.copy(mutable=True)
                sg.degenerate_non_separating(v)
                if not mutable:
                    sg.set_immutable()
                if sg.edge_is_canonical(v, v, check=False):
                    yield sg
                elif verbose:
                    print('non canonical loop generation')
                    print('  self      = {}'.format(self))
                    print('  v         = {}'.format(v))

        # vertex splitting
        if target_moduli is None:
            if target_max_moduli <= MODULI_RT:
                if g == 0:
                    splitting_data = self._canonical_splitting_data(v, 1, 1, 0, 0)
                elif g == 1:
                    splitting_data = self._canonical_splitting_data(v, 1, 1, 0, 1)
                else:
                    splitting_data = itertools.chain(self._canonical_splitting_data(v, 1, 1, 0, 0),
                                                     self._canonical_splitting_data(v, 1, 1, g, g))
            elif target_max_moduli == MODULI_CT or target_max_moduli == MODULI_TL:
                splitting_data = self._canonical_splitting_data(v, 1, 1, 0, g)
            else:
                assert target_max_moduli == MODULI_ST
                splitting_data = self._canonical_splitting_data(v, 1, l + 1, 0, g)
        else:
            if target_moduli == MODULI_RT:
                # current_moduli is SM or RT
                if g == 0:
                    splitting_data = self._canonical_splitting_data(v, 1, 1, 0, 0)
                elif g == 1:
                    splitting_data = self._canonical_splitting_data(v, 1, 1, 0, 1)
                else:
                    splitting_data = itertools.chain(self._canonical_splitting_data(v, 1, 1, 0, 0),
                                                     self._canonical_splitting_data(v, 1, 1, g, g))
            elif target_moduli == MODULI_CT:
                if current_moduli < MODULI_CT:
                    splitting_data = self._canonical_splitting_data(v, 1, 1, 1, g - 1)
                else:
                    splitting_data = self._canonical_splitting_data(v, 1, 1, 0, g)
            if target_moduli == MODULI_TL:
                if current_moduli < MODULI_TL:
                    return
                splitting_data = self._canonical_splitting_data(v, 1, 1, 0, g)
            if target_moduli == MODULI_ST:
                if current_moduli < MODULI_ST:
                    splitting_data = self._canonical_splitting_data(v, 2, l + 1, 0, g)
                else:
                    splitting_data = self._canonical_splitting_data(v, 1, l + 1, 0, g)

        for mult, g0, markings0, l0, edges0 in splitting_data:
            sg = self.copy(mutable=True)
            sg.degenerate_separating(v, mult, g0, markings0, l0, edges0, check=False)
            if not mutable:
                sg.set_immutable()
            if sg.edge_is_canonical(nv, v, check=False):
                yield sg
            elif verbose:
                print('non canonical splitting')
                print('  self      = {}'.format(self))
                print('  v         = {}'.format(v))
                print('  mult      = {}'.format(mult))
                print('  markings0 = {}'.format(markings0))
                print('  loops0    = {}'.format(l0))
                print('  edges0    = {}'.format(edges0))


class DecoratedGraphMorphism(SageObject):
    r"""
    Map between two decorated graphs obtained by contracting a certain number
    of edges and performing a relabelling of the vertices.

    Such a morphism is usually created from a given :class:`DecoratedGraph` using the
    methods :meth:`DecoratedGraph.relabelling_morphism` or
    :meth:`DecoratedGraph.edge_contraction_morphism`.

    As with permutations, morphisms are composed from left to right using the
    operator ``*``. In other words, morphisms should be thought as acting on
    the right.

    EXAMPLES::

        sage: from admcycles.decorated_graph import DecoratedGraph, DecoratedGraphMorphism
        sage: dom = DecoratedGraph([0, 0], [[], []], [(0, 0, 2), (0, 1, 3)])
        sage: codom = DecoratedGraph([1], [[]], [(0, 0, 3)])
        sage: DecoratedGraphMorphism(dom, codom, (0, 0), {(0, 0): {(0, 0): 1, (0, 1): 2}})
        DecoratedGraphMorphism(
            domain=DecoratedGraph([0, 0], [[], []], [(0, 1, 3), (0, 0, 2)]),
            codomain=DecoratedGraph([1], [[]], [(0, 0, 3)]),
            vertex_images=(0, 0),
            edge_preimages={(0, 0): {(0, 0): 1, (0, 1): 2}})
        sage: DecoratedGraphMorphism(dom, codom, (0, 0), {(0, 0): {(0, 0): 2, (0, 1): 1}})
        DecoratedGraphMorphism(
            domain=DecoratedGraph([0, 0], [[], []], [(0, 1, 3), (0, 0, 2)]),
            codomain=DecoratedGraph([1], [[]], [(0, 0, 3)]),
            vertex_images=(0, 0),
            edge_preimages={(0, 0): {(0, 0): 2, (0, 1): 1}})
    """
    __slot__ = ['_domain', '_codomain', '_vertex_images', '_edge_preimages', '_hash']

    def __init__(self, domain, codomain, vertex_images, edge_preimages, check=True):
        r"""
        INPUT:

        domain : a `~admcycles.decorated_graph.DecoratedGraph`

        codomain: a `~admcycles.decorated_graph.DecoratedGraph`

        vertex_images : list of length ``domain.num_verts()``
          the (surjective) map from the vertices of ``domain`` to the vertices of
          ``codomain``

        edge_preimages: dictionary of dictionaries
          the (injective) map from the edges of ``codomain`` to the edges of
          ``domain``. Dictionary whose keys are the edges in codomain (without
          multiplicity) and the values are dictionaries whose keys are edges in
          the domain and values the (non-zero) multiplicities.

        check: optional boolean (default is ``True``)
          whether to check that input is consistent
        """
        if not isinstance(domain, DecoratedGraph):
            raise ValueError

        self._domain = domain.copy(mutable=False)
        self._codomain = codomain.copy(mutable=False)
        self._vertex_images = tuple(vertex_images)
        self._edge_preimages = edge_preimages

        if check:
            self._check()

    def _check(self):
        r"""
        TESTS::

            sage: from admcycles.decorated_graph import DecoratedGraph, DecoratedGraphMorphism
            sage: dg1 = DecoratedGraph([0, 0], [[], []], [(0, 1, 1), (0, 0, 1), (1, 1, 1)])
            sage: dg2 = DecoratedGraph([0, 0], [[], []], [(0, 1, 1), (0, 0, 1), (1, 1, 1)])
            sage: m = DecoratedGraphMorphism(dg1, dg2, (1, 0), {(0, 0): {(0, 0): 1}, (0, 1): {(0, 1): 1}, (1, 1): {(1, 1): 1}})  # indirect doctest
        """
        if not isinstance(self._domain, DecoratedGraph):
            raise ValueError('invalid domain')
        if not isinstance(self._codomain, DecoratedGraph):
            raise ValueError('invalid codomain')
        if len(self._vertex_images) != self._domain.num_verts() or \
           not all(isinstance(v, numbers.Integral) and 0 <= v < self._codomain.num_verts() for v in self._vertex_images):
            raise ValueError('invalid vertex_images')
        if len(self._edge_preimages) != self._codomain.num_edges(multiplicities=False):
            raise ValueError('invalid edge_preimages')
        for (u1, v1), preimage in self._edge_preimages.items():
            if (not self._codomain.has_edge(u1, v1) or
                    u1 > v1 or
                    not all(isinstance(m, numbers.Integral) and m > 0 for m in preimage.values()) or
                    sum(preimage.values()) != self._codomain.edge_multiplicity(u1, v1)):
                raise ValueError('invalid edge_preimages {}'.format(self._edge_preimages))
            if any(not self._domain.has_edge(u2, v2) or
                   u2 > v2 or
                   m > self._domain.edge_multiplicity(u2, v2) and
                   (u1, v1) != _edge(self._vertex_images[u2], self._vertex_images[v2])
                   for (u2, v2), m in preimage.items()):
                raise ValueError('invalid edge_preimages')

    def __eq__(self, other):
        r"""
        Return whether the morphism are equal.
        """
        if type(self) is not type(other):
            return NotImplemented
        return (self._domain == other._domain and
                self._codomain == other._codomain and
                self._vertex_images == other._vertex_images and
                self._edge_preimages == other._edge_preimages)

    def __ne__(self, other):
        r"""
        Return whether the morphism are different.
        """
        if type(self) is not type(other):
            return NotImplemented
        return (self._domain != other._domain or
                self._codomain != other._codomain or
                self._vertex_images != other._vertex_images or
                self._edge_preimages != other._edge_preimages)

    def __hash__(self):
        r"""
        TESTS::

            sage: from admcycles.decorated_graph import DecoratedGraph, DecoratedGraphMorphism
            sage: dg1 = DecoratedGraph([0, 0], [[], []], [(0, 1, 1), (0, 0, 1), (1, 1, 1)])
            sage: dg2 = DecoratedGraph([0, 0], [[], []], [(0, 1, 1), (0, 0, 1), (1, 1, 1)])
            sage: m = DecoratedGraphMorphism(dg1, dg2, (1, 0), {(0, 0): {(0, 0): 1}, (0, 1): {(0, 1): 1}, (1, 1): {(1, 1): 1}})
            sage: hash(m)  # random # indirect doctest
            5458910276680072441
        """
        try:
            return self._hash
        except AttributeError:
            pass
        preimages = tuple(sorted((e, tuple(sorted(preimages.items()))) for e, preimages in self._edge_preimages.items()))
        self._hash = hash((self._domain, self._codomain, self._vertex_images, preimages))
        return self._hash

    def _repr_(self):
        r"""
        String representation.
        """
        edge_preimages_str = '{' + ', '.join('{e1}: {value}'.format(e1=e1, value='{' + ', '.join('{e2}: {mult}'.format(e2=e2, mult=self._edge_preimages[e1][e2]) for e2 in sorted(self._edge_preimages[e1])) + '}') for e1 in sorted(self._edge_preimages)) + '}'
        return 'DecoratedGraphMorphism(\n    domain={},\n    codomain={},\n    vertex_images={},\n    edge_preimages={})'.format(self._domain, self._codomain, self._vertex_images, edge_preimages_str)

    def domain(self):
        r"""
        Return the domain of this morphism

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: g = DecoratedGraph([0, 0], [[1, 2], [3, 4]], [(0, 1, 2)])
            sage: m = g.edge_contraction_morphism([(0, 1, 1)])
            sage: m.domain()
            DecoratedGraph([0, 0], [[2, 1], [4, 3]], [(0, 1, 2)])
        """
        return self._domain

    def codomain(self):
        r"""
        Return the codomain of this morphism.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: g = DecoratedGraph([0, 0], [[2, 1], [4, 3]], [(0, 1, 2)])
            sage: m = g.edge_contraction_morphism([(0, 1, 1)])
            sage: m.codomain()
            DecoratedGraph([0], [[4, 3, 2, 1]], [(0, 0, 1)])
        """
        return self._codomain

    def num_contracted_edges(self):
        r"""
        Return the number of contracted edges by this morphism.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: g = DecoratedGraph([0, 0, 0], [[], [], []], [(0, 1, 2), (1, 2, 2)])
            sage: g.relabelling_morphism([2, 1, 0]).num_contracted_edges()
            0
            sage: g.edge_contraction_morphism([(0, 1, 2)]).num_contracted_edges()
            2
        """
        return self._domain.num_edges() - self._codomain.num_edges()

    def is_relabelling(self):
        r"""
        Return whether this morphism is an automorphism.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: g = DecoratedGraph([0, 0, 0], [[], [], []], [(0, 1, 2), (1, 2, 2)])
            sage: g.relabelling_morphism([2, 1, 0]).is_relabelling()
            True
            sage: g.edge_contraction_morphism([(0, 1, 2)]).is_relabelling()
            False
        """
        return self._domain.num_edges() == self._codomain.num_edges()

    def vertex_image(self, v):
        r"""
        Return the image of the vertex ``v``.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: g = DecoratedGraph([0, 1, 0, 0], [[], [], [], []], [(0, 1, 2), (1, 2, 1), (1, 3, 2), (2, 3, 1), (3, 3, 1)])
            sage: m = g.edge_contraction_morphism([(0, 1, 1), (2, 3, 1), (3, 3, 1)])
            sage: m.vertex_image(1)
            0
        """
        v = self._domain._check_vertex(v)
        return self._vertex_images[v]

    def vertex_preimage(self, v):
        r"""
        Return the preimage of the vertex ``v`` under the morphism.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: g = DecoratedGraph([0, 1, 0, 0], [[], [], [], []], [(0, 1, 2), (1, 2, 1), (1, 3, 2), (2, 3, 1), (3, 3, 1)])
            sage: m = g.edge_contraction_morphism([(0, 1, 1), (2, 3, 1), (3, 3, 1)])
            sage: m.codomain()
            DecoratedGraph([1, 1], [[], []], [(0, 1, 3), (0, 0, 1)])
            sage: m.vertex_preimage(0)
            [0, 1]
            sage: m.vertex_preimage(1)
            [2, 3]
        """
        v = self._codomain._check_vertex(v)
        return [u for u in self._domain.vertices() if self._vertex_images[u] == v]

    def edge_preimage(self, u, v, check=True):
        r"""
        Return the preimage of the edge ``(u, v)`` under the morphism.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: g = DecoratedGraph([0, 1, 0, 0], [[], [], [], []], [(0, 1, 2), (1, 2, 1), (1, 3, 2), (2, 3, 1), (3, 3, 1)])
            sage: m = g.edge_contraction_morphism([(0, 1, 1), (2, 3, 1), (3, 3, 1)])
            sage: m.edge_preimage(0, 1)
            {(1, 2): 1, (1, 3): 2}
        """
        if check:
            u, v = self._codomain._check_edge(u, v)
        return self._edge_preimages[(u, v)]

    def domain_vertex_partition(self):
        r"""
        Return the partition of the vertex domain induced by this morphism.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: g = DecoratedGraph([0, 1, 0, 0], [[], [], [], []], [(0, 1, 2), (1, 2, 1), (1, 3, 2), (2, 3, 1), (3, 3, 1)])
            sage: m = g.edge_contraction_morphism([(0, 1, 1), (2, 3, 1), (3, 3, 1)])
            sage: m.domain_vertex_partition()
            [[0, 1], [2, 3]]
        """
        partition = [[] for _ in range(self._codomain.num_verts())]
        for u in self._domain.vertices():
            partition[self._vertex_images[u]].append(u)
        return partition

    def inverse(self):
        r"""
        Return the inverse of this morphism.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: g = DecoratedGraph([0, 1], [[], []], [(0, 1, 3)])
            sage: g.relabelling_morphism((1, 0)).inverse()
            DecoratedGraphMorphism(
                domain=DecoratedGraph([1, 0], [[], []], [(0, 1, 3)]),
                codomain=DecoratedGraph([0, 1], [[], []], [(0, 1, 3)]),
                vertex_images=(1, 0),
                edge_preimages={(0, 1): {(0, 1): 3}})
        """
        if not self.is_relabelling():
            raise ValueError('not invertible')

        nv = self._domain.num_verts()
        relabel_inv = [None] * nv
        for i in range(nv):
            relabel_inv[self._vertex_images[i]] = i

        # TODO: turn check to False
        return DecoratedGraphMorphism(self._codomain, self._domain, relabel_inv, {ee: {e: m} for e, preimages in self._edge_preimages.items() for ee, m in preimages.items()}, check=True)

    def remaining_edges(self):
        r"""
        Iterator through the non-contracted edges.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: g = DecoratedGraph([0, 0, 0], [[], [], []], [(0, 1, 1), (1, 1, 2), (0, 2, 2), (2, 2, 1)])
            sage: m = g.edge_contraction_morphism([(0, 2, 1), (2, 2, 1)])
            sage: sorted(m.remaining_edges())
            [(0, 1, 1), (0, 2, 1), (1, 1, 2)]
        """
        for edges in self._edge_preimages.values():
            for (u, v), m in edges.items():
                yield (u, v, m)

    def contracted_edges(self):
        r"""
        Return the list of contracted edges.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph
            sage: g = DecoratedGraph([0, 0, 0], [[], [], []], [(0, 1, 1), (1, 1, 2), (0, 2, 2), (2, 2, 1)])
            sage: m = g.edge_contraction_morphism([(0, 2, 1), (2, 2, 1)])
            sage: sorted(m.contracted_edges())
            [(0, 2, 1), (2, 2, 1)]
        """
        original_edges = set(self._domain.edges(multiplicities=False))
        for edges in self._edge_preimages.values():
            for (u, v), m1 in edges.items():
                m0 = self._domain.edge_multiplicity(u, v)
                if m0 != m1:
                    yield (u, v, m0 - m1)
                original_edges.remove((u, v))
        for u, v in original_edges:
            yield (u, v, self._domain.edge_multiplicity(u, v))

    def multiplicity(self):
        r"""
        Return the number of leg labelled morphisms represented by this
        decorated graph morphism.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph, DecoratedGraphMorphism
            sage: g1 = DecoratedGraph([0], [[]], [(0, 0, 2)])
            sage: g2 = DecoratedGraph([1], [[]], [(0, 0, 1)])
            sage: DecoratedGraphMorphism(g1, g2, [0], {(0, 0): {(0, 0): 1}}).multiplicity()
            4

            sage: g1 = DecoratedGraph([0, 1], [[], []], [(0, 1, 1), (0, 0, 1)])
            sage: g2 = DecoratedGraph([1, 1], [[], []], [(0, 1, 1)])
            sage: DecoratedGraphMorphism(g1, g2, [0, 1], {(0, 1): {(0, 1): 1}}).multiplicity()
            1

            sage: g1 = DecoratedGraph([0, 0], [[], []], [(0, 1, 3)])
            sage: g2 = DecoratedGraph([1], [[]], [(0, 0, 1)])
            sage: DecoratedGraphMorphism(g1, g2, [0, 0], {(0, 0): {(0, 1): 1}}).multiplicity()
            6

            sage: g1 = DecoratedGraph([0, 0], [[], []], [(0, 1, 3)])
            sage: g2 = DecoratedGraph([0], [[]], [(0, 0, 2)])
            sage: DecoratedGraphMorphism(g1, g2, [0, 0], {(0, 0): {(0, 1): 2}}).multiplicity()
            24

            sage: g1 = DecoratedGraph([0, 0], [[], []], [(0, 1, 1), (0, 0, 1), (1, 1, 1)])
            sage: g2 = DecoratedGraph([0], [[]], [(0, 0, 2)])
            sage: DecoratedGraphMorphism(g1, g2, [0, 0], {(0, 0): {(0, 0): 1, (1, 1): 1}}).multiplicity()
            8
        """
        mult = 1
        for U, V, M in self._codomain.edges():
            mult *= factorial(M)
            if U == V:
                mult *= 2 ** M

            preimage = self._edge_preimages[(U, V)]
            for (u, v), m in preimage.items():
                m0 = self._domain.edge_multiplicity(u, v)
                mult *= binomial(m0, m)
        return mult

    def permutation_is_domain_automorphism_stabilizer(self, perm, check=True):
        r"""
        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph, DecoratedGraphMorphism
            sage: g = DecoratedGraph([0, 0, 0, 0, 0, 0],
            ....:                    [[], [], [], [], [], []],
            ....:                    [(0, 1, 1), (1, 2, 1), (2, 0, 1), (3, 4, 1), (4, 5, 1), (5, 3, 1),
            ....:                     (0, 3, 1), (1, 4, 1), (2, 5, 1)])
            sage: h = DecoratedGraph([0], [[]], [(0, 0, 3)])
            sage: mor = DecoratedGraphMorphism(g, h, [0] * 6, {(0, 0): {(0, 1): 1, (1, 2): 1, (0, 2): 1}})
            sage: sum(1 for perm in g.automorphism_group() if mor.domain_automorphism_action(perm) == mor)
            6
            sage: sum(mor.permutation_is_domain_automorphism_stabilizer(perm) for perm in g.automorphism_group())
            6

            sage: mor = DecoratedGraphMorphism(g, h, [0] * 6, {(0, 0): {(0, 3): 1, (1, 4): 1, (2, 5): 1}})
            sage: sum(1 for perm in g.automorphism_group() if mor.domain_automorphism_action(perm) == mor)
            12
            sage: sum(mor.permutation_is_domain_automorphism_stabilizer(perm) for perm in g.automorphism_group())
            12
        """
        if check:
            if self.domain().relabel(perm) != self.domain():
                raise ValueError('not an automorphism')

        if not isinstance(perm, (tuple, list, dict)):
            # assume we have an automorphism, ie a PermutationGroupElement
            perm = perm.domain()

        return (all(self._vertex_images[v] == self._vertex_images[perm[v]] for v in self._domain.vertices()) and
                all(preimages == {_edge(perm[u1], perm[v1]): m for (u1, v1), m in preimages.items()} for (u2, v2), preimages in self._edge_preimages.items()))

    def domain_automorphism_action(self, perm, check=True):
        r"""
        Precompose by an automorphism of the domain.

        EXAMPLES::

            sage: from admcycles.decorated_graph import DecoratedGraph, DecoratedGraphMorphism
            sage: g = DecoratedGraph([0, 0, 0, 0, 0, 0],
            ....:                    [[], [], [], [], [], []],
            ....:                    [(0, 1, 1), (1, 2, 1), (2, 0, 1), (3, 4, 1), (4, 5, 1), (5, 3, 1),
            ....:                     (0, 3, 1), (1, 4, 1), (2, 5, 1)])
            sage: h = DecoratedGraph([0], [[]], [(0, 0, 4)])
            sage: mor = DecoratedGraphMorphism(g, h, [0] * 6, {(0, 0): {(0, 1): 1, (1, 2): 1, (1, 4): 1, (4, 5): 1}})
            sage: mor.domain_automorphism_action([1, 2, 0, 4, 5, 3])
            DecoratedGraphMorphism(
                domain=DecoratedGraph([0, 0, 0, 0, 0, 0], [[], [], [], [], [], []], [(0, 1, 1), (0, 2, 1), (0, 3, 1), (1, 2, 1), (1, 4, 1), (2, 5, 1), (3, 4, 1), (3, 5, 1), (4, 5, 1)]),
                codomain=DecoratedGraph([0], [[]], [(0, 0, 4)]),
                vertex_images=(0, 0, 0, 0, 0, 0),
                edge_preimages={(0, 0): {(0, 2): 1, (1, 2): 1, (2, 5): 1, (3, 5): 1}})
        """
        if check:
            if self.domain().relabel(perm) != self.domain():
                raise ValueError('not an automorphism')

        if not isinstance(perm, (tuple, list, dict)):
            # assume we have an automorphism, ie a PermutationGroupElement
            perm = perm.domain()

        vertex_images = tuple(self._vertex_images[perm[v]] for v in self._domain.vertices())
        edge_preimages = {(u2, v2): {_edge(perm[u1], perm[v1]): m for (u1, v1), m in preimages.items()}
                          for (u2, v2), preimages in self._edge_preimages.items()}
        return DecoratedGraphMorphism(self._domain, self._codomain, vertex_images, edge_preimages)


def trivial_decorated_graph(g, markings):
    r"""
    Return the trivial stable graph with the given genus ``g`` and ``markings``.

    EXAMPLES::

        sage: from admcycles.decorated_graph import trivial_decorated_graph
        sage: trivial_decorated_graph(2, 0)
         DecoratedGraph([2], [[]], [])
        sage: trivial_decorated_graph(0, 3)
        DecoratedGraph([0], [[3, 2, 1]], [])
        sage: trivial_decorated_graph(0, [1, 1, 1])
        DecoratedGraph([0], [[1, 1, 1]], [])
    """
    if not isinstance(g, numbers.Integral) or g < 0:
        raise ValueError('invalid genus g')
    if isinstance(markings, (tuple, list)):
        markings = sorted(map(int, markings), reverse=True)
    elif isinstance(markings, numbers.Integral):
        markings = list(range(markings, 0, -1))
    else:
        raise TypeError('invalid markings')
    if 3 * g - 3 + len(markings) < 0:
        raise ValueError('unstable data')
    return DecoratedGraph([g], [markings])


def stable_graphs(g, markings, rmax=None, moduli=None):
    r"""
    Return the list of stable graphs of genus ``g`` and given ``markings`` up
    to isomorphism.

    The output is a list of lists, where each bucket corresponds to the
    decorated graphs of given dimension. This function is similar to
    :func:`admcycles.admcycles.list_strata` but returns a list of lists of
    :class:`DecoratedGraph` rather than a list of
    :class:`admcycles.stable_graph.StableGraph`.

    This function uses Brendan McKay method of canonical labels to generate
    the list of stable graphs [MKa98]_.

    INPUT:

    g : genus

    markings : integer or list
      the markings

    rmax : integer
      bound for the number of edges

    moduli : string or integer
      a moduli, either ``'stable'``, ``'tree_like'``, ``'compact_type'``,
      ``'rational_tail'`` or ``'smooth'``.

    EXAMPLES::

        sage: from admcycles.decorated_graph import stable_graphs

    Genus zero::

        sage: for n in range(3, 8):
        ....:     print(0, n, list(map(len, stable_graphs(0, n, -3 + n))))
        0 3 [1]
        0 4 [1, 3]
        0 5 [1, 10, 15]
        0 6 [1, 25, 105, 105]
        0 7 [1, 56, 490, 1260, 945]

    Genus 1::

        sage: for n in range(1, 6):
        ....:     print(1, n, list(map(len, stable_graphs(1, n, n))))
        1 1 [1, 1]
        1 2 [1, 2, 2]
        1 3 [1, 5, 10, 7]
        1 4 [1, 12, 43, 68, 39]
        1 5 [1, 27, 171, 470, 610, 297]

    Genus 1 rational tails::

        sage: for n in range(1, 6):
        ....:     print(1, n, list(map(len, stable_graphs(1, n, moduli='rational_tails'))))
        1 1 [1]
        1 2 [1, 1]
        1 3 [1, 4, 3]
        1 4 [1, 11, 25, 15]
        1 5 [1, 26, 130, 210, 105]

    Genus 1 tree like::

        sage: for n in range(1, 6):
        ....:     print(1, n, list(map(len, stable_graphs(1, n, moduli='tree_like'))))
        1 1 [1, 1]
        1 2 [1, 2, 1]
        1 3 [1, 5, 7, 3]
        1 4 [1, 12, 36, 40, 15]
        1 5 [1, 27, 156, 340, 315, 105]

    Genus 2::

        sage: for n in range(0, 5):
        ....:     print(2, n, list(map(len, stable_graphs(2, n, 3 + n))))
        2 0 [1, 2, 2, 2]
        2 1 [1, 2, 5, 5, 3]
        2 2 [1, 4, 13, 24, 23, 10]
        2 3 [1, 9, 40, 112, 179, 156, 58]
        2 4 [1, 20, 134, 526, 1262, 1794, 1406, 465]

    Genus 2 with moduli::

        sage: for n in range(0, 5):
        ....:     for moduli in ['sm', 'rt', 'ct', 'tl']:
        ....:         print(2, n, moduli, list(map(len, stable_graphs(2, n, moduli=moduli))))
        2 0 sm [1]
        2 0 rt [1]
        2 0 ct [1, 1]
        2 0 tl [1, 2, 2, 1]
        2 1 sm [1]
        2 1 rt [1]
        2 1 ct [1, 1, 1]
        2 1 tl [1, 2, 4, 2, 1]
        2 2 sm [1]
        2 2 rt [1, 1]
        2 2 ct [1, 3, 4, 2]
        2 2 tl [1, 4, 10, 12, 7, 2]
        2 3 sm [1]
        2 3 rt [1, 4, 3]
        2 3 ct [1, 8, 20, 22, 9]
        2 3 tl [1, 9, 33, 66, 69, 37, 9]
        2 4 sm [1]
        2 4 rt [1, 11, 25, 15]
        2 4 ct [1, 19, 91, 183, 170, 60]
        2 4 tl [1, 20, 119, 358, 601, 558, 275, 60]

    Genus 3 with moduli::

        sage: for n in range(0, 3):
        ....:     for moduli in ['sm', 'rt', 'ct', 'tl', 'st']:
        ....:         print(3, n, moduli, list(map(len, stable_graphs(3, n, moduli=moduli))))
        3 0 sm [1]
        3 0 rt [1]
        3 0 ct [1, 1, 1, 1]
        3 0 tl [1, 2, 4, 6, 4, 2, 1]
        3 0 st [1, 2, 5, 9, 12, 8, 5]
        3 1 sm [1]
        3 1 rt [1]
        3 1 ct [1, 2, 3, 3, 1]
        3 1 tl [1, 3, 8, 15, 16, 11, 5, 1]
        3 1 st [1, 3, 10, 26, 44, 51, 34, 12]
        3 2 sm [1]
        3 2 rt [1, 1]
        3 2 ct [1, 5, 12, 17, 13, 4]
        3 2 tl [1, 6, 22, 55, 88, 89, 57, 22, 4]
        3 2 st [1, 6, 27, 91, 216, 350, 370, 228, 66]

    Genus 4 with moduli::

        sage: for n in range(0, 2):
        ....:     for moduli in ['sm', 'rt', 'ct', 'tl', 'st']:
        ....:         print(4, n, moduli, list(map(len, stable_graphs(4, n, moduli=moduli))))
        4 0 sm [1]
        4 0 rt [1]
        4 0 ct [1, 2, 2, 3, 2, 1]
        4 0 tl [1, 3, 6, 13, 19, 21, 14, 9, 3, 1]
        4 0 st [1, 3, 7, 21, 43, 75, 89, 81, 42, 17]
        4 1 sm [1]
        4 1 rt [1]
        4 1 ct [1, 3, 7, 10, 11, 6, 2]
        4 1 tl [1, 4, 14, 35, 70, 96, 97, 67, 34, 10, 2]
        4 1 st [1, 4, 17, 57, 161, 344, 565, 657, 534, 259, 67]

    The big ones::

        sage: g=0; n=8; print(list(map(len, stable_graphs(g, n, 3 * g - 3 + n)))) # long time ~ 11 secs
        [1, 119, 1918, 9450, 17325, 10395]
        sage: g=1; n=6; print(list(map(len, stable_graphs(g, n, 3 * g - 3 +n)))) # long time ~ 6 secs
        [1, 58, 634, 2802, 6200, 6780, 2865]
        sage: g=2; n=5; print(list(map(len, stable_graphs(g, n, 3 * g - 3 +n)))) # not tested ~ 26 secs
        [1, 43, 457, 2495, 8373, 17528, 22290, 15770, 4725]
        sage: g=3; n=3; print(list(map(len, stable_graphs(g, n, 3 * g - 3 +n)))) # long time ~ 6 secs
        [1, 13, 82, 361, 1132, 2489, 3744, 3649, 2086, 535]
        sage: g=4; n=2; print(list(map(len, stable_graphs(g, n, 3 * g - 3 + n)))) # not tested ~ 17 secs
        [1, 8, 46, 202, 705, 1919, 3999, 6200, 6890, 5188, 2368, 511]
        sage: g=5; n=0; print(list(map(len, stable_graphs(g, n, 3 * g - 3 + n)))) # long time ~ 6 secs
        [1, 3, 11, 34, 100, 239, 492, 784, 1002, 926, 632, 260, 71]

    TESTS:

    All types are the same in genus 0::

        sage: for n in range(3, 8):
        ....:     l_rt = list(stable_graphs(0, n, -3 + n, 'rational_tails'))
        ....:     l_ct = list(stable_graphs(0, n, -3 + n, 'compact_type'))
        ....:     l_tl = list(stable_graphs(0, n, -3 + n, 'tree_like'))
        ....:     l_st = list(stable_graphs(0, n, -3 + n, 'stable'))
        ....:     assert l_rt == l_ct == l_tl == l_st

    Compact type and rational tails are the same in genus 1::

        sage: for n in range(1, 5):
        ....:     l_rt = list(stable_graphs(1, n, moduli='rational_tails'))
        ....:     l_ct = list(stable_graphs(1, n, moduli='compact_type'))
        ....:     assert l_rt == l_ct

    Compare filtering versus restricted canonical generation::

        sage: for g, n in [(0, 3), (0, 4), (0, 5),
        ....:              (1, 1), (1, 2), (1, 3),
        ....:              (2, 0), (2, 1), (2, 2), (2, 3),
        ....:              (3, 0), (3, 1),
        ....:              (4, 0)]:
        ....:     graph_list = stable_graphs(g, n)
        ....:     for moduli in ['sm', 'rt', 'ct', 'tl']:
        ....:         graph_list_moduli = stable_graphs(g, n, moduli=moduli)
        ....:         subgraph_list = [[dg for dg in l if not dg.vanishes(moduli)] for l in graph_list_moduli]
        ....:         length1 = [len(l) for l in graph_list_moduli]
        ....:         length2 = [len(l) for l in subgraph_list if l]
        ....:         assert length1 == length2
    """
    if not isinstance(g, numbers.Integral):
        raise TypeError('stable_graphs: invalid type for g')
    g = int(g)
    if g < 0:
        raise ValueError('invalid input')

    graphs = [[trivial_decorated_graph(g, markings)]]
    n = graphs[0][0].num_markings()
    if 3 * g - 3 + n < 0:
        raise ValueError('stable_graphs: unstable data (g, n)')

    moduli = get_moduli(moduli)
    bound = num_edges_bound(g, n, moduli)
    if rmax is None:
        rmax = bound
    else:
        if not isinstance(rmax, numbers.Integral):
            raise TypeError('stable_graphs: invalid type for rmax')
        rmax = int(rmax)
        if rmax < 0 or rmax > bound:
            raise ValueError('stable_graphs: invalid argument rmax (must be positive integer at most {})'.format(bound))

    for r in range(1, rmax + 1):
        graphs.append([])
        for g in graphs[-2]:
            graphs[-1].extend(g.canonical_degenerations(moduli))
    return graphs
