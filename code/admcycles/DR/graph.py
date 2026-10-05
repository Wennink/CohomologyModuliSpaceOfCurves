r"""
Generators of tautological ring

Each generator is called a stratum and is encoded in a class class:`Graph`. A
stratum is called *pure* if it has neither kappa nor psi marking (ie a stable
graph with no decoration).
"""
from copy import copy
import itertools

from sage.misc.cachefunc import cached_function
from sage.misc.lazy_attribute import lazy_attribute

from sage.rings.all import PolynomialRing, ZZ
from sage.combinat.all import IntegerVectors, Partitions
from sage.functions.other import floor
from sage.matrix.constructor import matrix

from .utils import aut
from .moduli import MODULI_SM, MODULI_RT, MODULI_CT, MODULI_ST, MODULI_SMALL, dim_form
from .. import file_cache
import os
from sage.env import DOT_SAGE


R = PolynomialRing(ZZ, 1, order='lex', names=('X',))
X = R.gen()


class Graph:
    r"""
    A decorated graph representing a tautological class.

    The graph is encoded as a matrix where

    - each row after the first one corresponds to a vertex
    - each column after the first one corresponds to an edge or leg
    - the first column gives the genera of the vertices
    - the first row gives the markings on the legs
    - the other cells are
      - 0 if the vertex and edge/leg are not incident
      - 1 if the vertex and edge/leg are incident once
      - 2 if the edge is a loop at the vertex
    - entries with polynomials in X describe kappa/psi decorations:
    - in the first column, each X^n term corresponds to a kappa_n at that
      vertex
    - in other locations, each X term corresponds to a psi at that half-edge
    - at loops, 2 + aX + bX^2 corresponds to having psi^a on one side of the
      loop and psi^b on the other

    EXAMPLES::

        sage: from admcycles.DR.graph import Graph, X
        sage: gr = Graph(matrix(2, 3, [-1, 1, 2, 1, X + 1, 1]))
        sage: gr
        [   -1     1     2]
        [    1 X + 1     1]
        sage: gr.num_vertices()
        1
        sage: gr.num_edges()
        2
    """
    def __init__(self, M=None, genus_list=None):
        if M:
            self.M = copy(M)
        elif genus_list:
            self.M = matrix(R, len(genus_list) + 1,
                            1, [-1] + genus_list)
        else:
            self.M = matrix(R, 1, 1, -1)

    def __repr__(self):
        return repr(self.M)

    @lazy_attribute
    def degree_vec(self):
        r"""
        Return the tuple of degrees of vertices.

        EXAMPLES::

            sage: from admcycles.DR.graph import Graph, X
            sage: gr = Graph(matrix(2, 3, [-1, 1, 2, 1, X + 1, 1]))
            sage: gr.degree_vec
            (2,)
        """
        res = [0 for i in range(1, self.M.nrows())]
        for i in range(1, self.M.nrows()):
            for j in range(1, self.M.ncols()):
                res[i - 1] += self.M[i, j][0]
        return tuple(res)

    @lazy_attribute
    def target_parity(self):
        ans = 0
        for i in range(1, self.M.nrows()):
            local_parity = 1 + self.M[i, 0][0]
            for j in range(1, self.M.ncols()):
                local_parity += self.M[i, j][1] + self.M[i, j][2]
            for j in range(1, self.M[i, 0].degree() + 1):
                local_parity += j * self.M[i, 0][j]
            local_parity %= 2
            ans += (local_parity << (i - 1))
        return ans

    def degree(self, i):
        r"""
        Return the degree of vertex ``i``.
        """
        return self.degree_vec[i - 1]

    def num_vertices(self):
        return self.M.nrows() - 1

    def num_edges(self):
        return self.M.ncols() - 1

    def h1(self):
        return self.M.ncols() - self.M.nrows() + 1

    def add_vertex(self, g):
        self.M = self.M.stack(matrix(1, self.M.ncols()))
        self.M[-1, 0] = g

    def add_edge(self, i1, i2, marking=0):
        self.M = self.M.augment(matrix(self.M.nrows(), 1))
        self.M[0, -1] = marking
        if i1 > 0:
            self.M[i1, -1] += 1
        if i2 > 0:
            self.M[i2, -1] += 1

    def del_vertex(self, i):
        self.M = self.M[:i].stack(self.M[(i + 1):])

    def del_edge(self, i):
        if i == self.num_edges():
            self.M = self.M[0:, :i]
        else:
            self.M = self.M[0:, :i].augment(self.M[0:, (i + 1):])

    def split_vertex(self, i, row1, row2):
        self.M = self.M.stack(matrix(2, self.M.ncols(), row1 + row2))
        self.add_edge(self.M.nrows() - 2,
                      self.M.nrows() - 1)
        self.del_vertex(i)

    def replace_vertex_with_graph(self, i, G):
        nv = self.num_vertices()
        ne = self.num_edges()
        # i should have degree d, there should be no classes near i, and G should have genus equal to the genus of i
        hedge_list_ones = []
        hedge_list_others = []
        unsym_cols = [-1]
        mark_nr = -1
        for k in range(1, G.M.ncols()):
            if G.M[0, k] > 0:
                if G.M[0, k] == 1:
                    mark_nr += 1
                unsym_cols.append(G.M[0, k] + mark_nr)
            else:
                unsym_cols.append(0)
        for k in range(1, self.M.ncols()):
            for j in range(self.M[i, k][0]):
                if self.M[0, k] == 1:
                    hedge_list_ones.append(k)
                else:
                    hedge_list_others.append(k)
        hedge_list = hedge_list_ones + hedge_list_others
        self.del_vertex(i)
        for j in range(G.num_edges() - len(hedge_list)):
            self.add_edge(0, 0)
        for j in range(G.num_vertices()):
            self.add_vertex(G.M[j + 1, 0])
        col = ne + 1
        for k in range(1, G.M.ncols()):
            if G.M[0, k] > 0:
                mark = ZZ(unsym_cols[k])
                for j in range(G.num_vertices()):
                    if self.M[nv + j, hedge_list[mark - 1]] == 0:
                        self.M[nv + j, hedge_list[mark - 1]] = G.M[j + 1, k]
                    elif G.M[j + 1, k] != 0:
                        a = self.M[nv + j, hedge_list[mark - 1]][1]
                        b = G.M[j + 1, k][1]
                        self.M[nv + j, hedge_list[mark - 1]] = 2 + \
                            max(a, b) * X + min(a, b) * X**2
            else:
                for j in range(G.num_vertices()):
                    self.M[nv + j, col] = G.M[j + 1, k]
                col += 1

    def compute_invariant(self):
        nr, nc = self.M.nrows(), self.M.ncols()
        self.invariant = [[self.M[i, 0], [], [], [
            [] for j in range(1, nr)]] for i in range(1, nr)]
        for k in range(1, nc):
            L = [i for i in range(1, nr)
                 if self.M[i, k] != 0]
            if len(L) == 1:
                if self.M[0, k] != 0:
                    self.invariant[L[0] -
                                   1][2].append((self.M[0, k], self.M[L[0], k]))
                else:
                    self.invariant[L[0] - 1][1].append(self.M[L[0], k])
            else:
                self.invariant[L[0] - 1][3][L[1] - 1].append((self.M[L[0], k],
                                                              self.M[L[1], k]))
                self.invariant[L[1] - 1][3][L[0] - 1].append((self.M[L[1], k],
                                                              self.M[L[0], k]))
        for i in range(1, nr):
            self.invariant[i - 1][3] = [term for term in self.invariant[i - 1][3]
                                        if len(term)]
            for k in range(len(self.invariant[i - 1][3])):
                self.invariant[i - 1][3][k].sort()
                self.invariant[i -
                               1][3][k] = tuple(self.invariant[i - 1][3][k])
            self.invariant[i - 1][3].sort()
            self.invariant[i - 1][3] = tuple(self.invariant[i - 1][3])
            self.invariant[i - 1][2].sort()
            self.invariant[i - 1][2] = tuple(self.invariant[i - 1][2])
            self.invariant[i - 1][1].sort()
            self.invariant[i - 1][1] = tuple(self.invariant[i - 1][1])
            self.invariant[i - 1] = tuple(self.invariant[i - 1])
        vertex_invariants = [[i, self.invariant[i - 1]]
                             for i in range(1, nr)]
        self.invariant.sort()
        self.invariant = tuple(self.invariant)
        vertex_invariants.sort(key=lambda x: x[1])
        self.vertex_groupings = []
        for i in range(nr - 1):
            if i == 0 or vertex_invariants[i][1] != vertex_invariants[i - 1][1]:
                self.vertex_groupings.append([])
            self.vertex_groupings[-1].append(
                vertex_invariants[i][0])

    def purify(self):
        for i in range(self.M.nrows()):
            for j in range(self.M.ncols()):
                self.M[i, j] = R(self.M[i, j][0])

    def contract(self, i, vlist, elist):
        # assumes graph is undecorated
        if self.M[0, i] != 0:
            print("ERROR: cannot contract a marking")
            return
        S = [row for row in range(
            1, self.M.nrows()) if self.M[row, i] != 0]
        if len(S) == 1:
            self.M[S[0], 0] += 1
            self.del_edge(i)
            elist = elist[:(i - 1)] + elist[i:]
        else:
            self.del_edge(i)
            elist = elist[:(i - 1)] + elist[i:]
            self.add_vertex(0)
            self.M[-1] += self.M[S[0]]
            self.M[-1] += self.M[S[1]]
            self.del_vertex(S[1])
            self.del_vertex(S[0])
            vlist = vlist[:(S[0] - 1)] + vlist[S[0]:(S[1] - 1)] + \
                vlist[S[1]:] + [vlist[S[0] - 1] + vlist[S[1] - 1]]
        return vlist, elist


def graph_isomorphic(G1, G2):
    r"""
    Return whether ``G1`` and ``G2`` are isomorphic.
    """
    if G1.invariant != G2.invariant:
        return False

    M1 = G1.M
    M2 = G2.M
    group1 = G1.vertex_groupings
    group2 = G2.vertex_groupings

    nr = M1.nrows()
    nc = M1.ncols()
    for sigma_data in itertools.product(*(itertools.permutations(range(len(group))) for group in group1)):
        sigma = [0] * (nr - 1)
        for i in range(len(group1)):
            for j in range(len(group1[i])):
                sigma[group1[i][j] - 1] = group2[i][sigma_data[i][j]]
        good = True
        for i in range(1, nr):
            ii = sigma[i - 1]
            for j in range(1, i):
                jj = sigma[j - 1]
                L1 = []
                for k in range(1, nc):
                    if M1[i, k] != 0 and M1[j, k] != 0:
                        L1.append([M1[i, k], M1[j, k]])
                L1.sort()
                L2 = []
                for k in range(1, nc):
                    if M2[ii, k] != 0 and M2[jj, k] != 0:
                        L2.append([M2[ii, k], M2[jj, k]])
                L2.sort()
                if L1 != L2:
                    good = False
                    break
            if good is False:
                break
        if good:
            return True
    return False


def graph_count_automorphisms(G, vertex_orbits=False):
    return count_automorphisms(G.M, G.vertex_groupings, vertex_orbits)


def count_automorphisms(M, grouping, vertex_orbits=False):
    """
    INPUT:

    M: adjacency matrix
    grouping: list of lists
    vertex_orbits: boolean
    """
    nr, nc = M.nrows(), M.ncols()
    count = ZZ.zero()
    if vertex_orbits:
        isom_list = []
    for sigma_data in itertools.product(*(itertools.permutations(range(len(group))) for group in grouping)):
        sigma = [0 for i in range(nr - 1)]
        for i in range(len(grouping)):
            for j in range(len(grouping[i])):
                sigma[grouping[i][j] - 1] = grouping[i][sigma_data[i][j]]
        good = True
        for i in range(1, nr):
            ii = sigma[i - 1]
            for j in range(1, i):
                jj = sigma[j - 1]
                L1 = []
                for k in range(1, nc):
                    if M[i, k] != 0 and M[j, k] != 0:
                        L1.append([M[i, k], M[j, k]])
                L1.sort()
                L2 = []
                for k in range(1, nc):
                    if M[ii, k] != 0 and M[jj, k] != 0:
                        L2.append([M[ii, k], M[jj, k]])
                L2.sort()
                if L1 != L2:
                    good = False
                    break
            if not good:
                break
        if good:
            count += 1
            if vertex_orbits:
                isom_list.append(sigma)

    if vertex_orbits:
        orbit_list = []
        vertices_used = []
        while len(vertices_used) < nr - 1:
            i = next(ii for ii in range(1, nr) if ii not in vertices_used)
            orbit = []
            for sigma in isom_list:
                if sigma[i - 1] not in orbit:
                    orbit.append(sigma[i - 1])
                    vertices_used.append(sigma[i - 1])
            orbit.sort()
            orbit_list.append(orbit)
        return orbit_list

    for i in range(1, nr):
        for k in range(1, nc):
            if M[i, k][0] == 2 and M[i, k][1] == M[i, k][2]:
                count *= 2
        L = []
        for k in range(1, nc):
            if M[i, k] != 0:
                if sum(1 for j in range(1, nr) if M[j, k] != 0) == 1:
                    L.append([M[0, k], M[i, k]])
        count *= aut(L)

        for j in range(1, i):
            L = []
            for k in range(1, nc):
                if M[i, k] != 0 and M[j, k] != 0:
                    L.append([M[i, k], M[j, k]])
            count *= aut(L)
    return count


def graph_list_isomorphisms(G1, G2, only_one=False):
    r"""
    Return the list of isomorphisms from ``G1`` to ``G2``.
    """
    # Warning: does not count loops!
    # If this is too slow, we can probably improve by caching a list of automorphisms and applying those to the first isom found.
    if G1.invariant != G2.invariant:
        return []

    M1 = G1.M
    M2 = G2.M
    group1 = G1.vertex_groupings
    group2 = G2.vertex_groupings

    nr = M1.nrows()
    nc = M2.ncols()
    isom_list = []
    for sigma_data in itertools.product(*(itertools.permutations(range(len(group))) for group in group1)):
        sigma = [0] * (nr - 1)
        for i in range(len(group1)):
            for j in range(len(group1[i])):
                sigma[group1[i][j] - 1] = group2[i][sigma_data[i][j]]
        good = True
        for i in range(1, nr):
            ii = sigma[i - 1]
            for j in range(1, i):
                jj = sigma[j - 1]
                L1 = []
                for k in range(1, nc):
                    if M1[i, k] != 0 and M1[j, k] != 0:
                        L1.append([M1[i, k], M1[j, k]])
                L1.sort()
                L2 = []
                for k in range(1, nc):
                    if M2[ii, k] != 0 and M2[jj, k] != 0:
                        L2.append([M2[ii, k], M2[jj, k]])
                L2.sort()
                if L1 != L2:
                    good = False
                    break
            if not good:
                break
        if good:
            cols1 = [[M1[i, j] for i in range(nr)] for j in range(1, nc)]
            cols2 = [[M2[0, j]] + [M2[sigma[i - 1], j] for i in range(1, nr)]
                     for j in range(1, nc)]
            edge_group1 = []
            edge_group2 = []
            used1 = []
            for j in range(1, nc):
                if j not in used1:
                    edge_group1.append([])
                    edge_group2.append([])
                    for k in range(1, nc):
                        if cols1[k - 1] == cols1[j - 1]:
                            edge_group1[-1].append(k)
                            used1.append(k)
                        if cols2[k - 1] == cols1[j - 1]:
                            edge_group2[-1].append(k)
            for edge_sigma_data in itertools.product(*(itertools.permutations(range(len(edge_group))) for edge_group in edge_group1)):
                edge_sigma = [0 for i in range(nc - 1)]
                for i in range(len(edge_group1)):
                    for j in range(len(edge_group1[i])):
                        edge_sigma[edge_group1[i][j] -
                                   1] = edge_group2[i][edge_sigma_data[i][j]]
                isom_list.append([sigma, edge_sigma])
                if only_one:
                    return isom_list
    return isom_list


def degenerate(G_list, moduli_type=MODULI_ST):
    r"""
    Return the list of degenerations of the graphs in ``G_list`` up to
    isomorphisms.
    """
    mod_size = moduli_type + 1
    if moduli_type == MODULI_SMALL:
        mod_size = MODULI_SM + 1
    G_list_new = [[] for i in range(mod_size)]
    for which_type in range(mod_size):
        for G in G_list[which_type]:
            for i in range(1, G.num_vertices() + 1):
                row = list(G.M[i])
                m = row[0] + sum(row)
                if m < 4:
                    continue
                row1 = [0 for j in range(len(row))]
                while [2 * x for x in row1] <= row:
                    if row1[0] == 1 and moduli_type <= MODULI_RT:
                        break
                    if row1[0] + sum(row1) >= 2 and row1[0] + sum(row1) <= m - 2:
                        row2 = [row[j] - row1[j] for j in range(len(row))]
                        G_copy = Graph(G.M)
                        G_copy.split_vertex(i, row1, row2)
                        new_type = which_type
                        if new_type == MODULI_SM:
                            new_type = MODULI_RT
                        if new_type == MODULI_RT and row1[0] > 0:
                            new_type = MODULI_CT
                        G_list_new[new_type].append(G_copy)
                    row1[-1] += 1
                    for j in range(1, len(row)):
                        if row1[-j] <= row[-j]:
                            break
                        row1[-j] = 0
                        row1[-j - 1] += 1
    for i in range(mod_size):
        G_list_new[i] = remove_isomorphic(G_list_new[i])
    return G_list_new


def decorate(G_list, r, moduli_type=MODULI_ST):
    r"""
    Add decorations to the graphs in ``G_list``.
    """
    mod_size = moduli_type + 1
    if moduli_type == MODULI_SMALL:
        mod_size = MODULI_SM + 1
    G_list_new = [[] for i in range(mod_size)]
    for which_type in range(mod_size):
        for G in G_list[which_type]:
            G_deco = [[] for i in range(mod_size)]
            nr, nc = G.M.nrows(), G.M.ncols()
            two_list = []
            one_list = []
            for i in range(1, nr):
                for j in range(1, nc):
                    if G.M[i, j] == 2:
                        two_list.append([i, j])
                    elif G.M[i, j] == 1:
                        one_list.append([i, j])
            a = nr - 1
            b = len(two_list)
            c = len(one_list)
            dims = [[dim_form(G.M[i + 1, 0][0], G.degree(i + 1), mod_type)
                     for i in range(a)] for mod_type in range(mod_size)]
            for vec in IntegerVectors(r, a + b + c):
                new_type = which_type
                if moduli_type > MODULI_SMALL:
                    test_dims = vec[:a]
                    for i in range(b):
                        test_dims[two_list[i][0] - 1] += vec[a + i]
                    for i in range(c):
                        test_dims[one_list[i][0] - 1] += vec[a + b + i]
                    for mod_type in range(which_type, mod_size):
                        for i in range(a):
                            if test_dims[i] > dims[mod_type][i]:
                                new_type = mod_type + 1
                                break
                    if new_type > moduli_type:
                        continue
                S_list = []
                for i in range(a):
                    S_list.append(Partitions(vec[i]))
                for i in range(a, a + b):
                    S_list.append(
                        [[vec[i] - j, j] for j in range(floor(vec[i] / ZZ(2) + 1))])
                S = itertools.product(*S_list)
                for vec2 in S:
                    G_copy = Graph(G.M)
                    for i in range(a):
                        for j in vec2[i]:
                            G_copy.M[i + 1, 0] += X**j
                    for i in range(a, a + b):
                        G_copy.M[two_list[i - a][0], two_list[i - a]
                                 [1]] += vec2[i][0] * X + vec2[i][1] * X**2
                    for i in range(c):
                        G_copy.M[one_list[i][0],
                                 one_list[i][1]] += vec[i + a + b] * X
                    G_deco[new_type].append(G_copy)
            for mod_type in range(mod_size):
                G_list_new[mod_type] += remove_isomorphic(G_deco[mod_type])
    return G_list_new


def remove_isomorphic(G_list):
    r"""
    Return a list of isomorphism class representatives of the graphs in ``G_list``.
    """
    G_list_new = []
    inv_dict = {}
    count = 0
    for G1 in G_list:
        G1.compute_invariant()
        if G1.invariant not in inv_dict:
            inv_dict[G1.invariant] = []
        good = True
        for i in inv_dict[G1.invariant]:
            if graph_isomorphic(G1, G_list_new[i]):
                good = False
                break
        if good:
            G_list_new.append(G1)
            inv_dict[G1.invariant].append(count)
            count += 1
    return G_list_new


def num_strata(g, r, markings=(), moduli_type=MODULI_ST):
    r"""
    Return the number of strata in given genus, rank, markings and moduli type.

    EXAMPLES::

        sage: from admcycles.DR.moduli import MODULI_SM, MODULI_CT, MODULI_RT, MODULI_ST
        sage: from admcycles.DR.graph import num_strata
        sage: for r in range(4):
        ....:     print('r={}: {} {} {} {}'.format(r,
        ....:           num_strata(2, r, (1, 1), MODULI_SM),
        ....:           num_strata(2, r, (1, 1), MODULI_RT),
        ....:           num_strata(2, r, (1, 1), MODULI_CT),
        ....:           num_strata(2, r, (1, 1), MODULI_ST)))
        r=0: 1 1 1 1
        r=1: 2 3 5 6
        r=2: 0 7 16 28
        r=3: 0 0 38 113
    """
    return len(all_strata(g, r, markings, moduli_type))


def num_pure_strata(g, r, markings=(), moduli_type=MODULI_ST):
    r"""
    Return the number of pure strata in given genus, rank, markings and moduli type.

    EXAMPLES::

        sage: from admcycles.DR.moduli import MODULI_SM, MODULI_CT, MODULI_RT, MODULI_ST
        sage: from admcycles.DR.graph import num_pure_strata
        sage: for r in range(4):
        ....:     print('r={}: {} {} {} {}'.format(r,
        ....:           num_pure_strata(2, r, (1, 1), MODULI_SM),
        ....:           num_pure_strata(2, r, (1, 1), MODULI_RT),
        ....:           num_pure_strata(2, r, (1, 1), MODULI_CT),
        ....:           num_pure_strata(2, r, (1, 1), MODULI_ST)))
        r=0: 1 1 1 1
        r=1: 0 1 3 4
        r=2: 0 0 3 10
        r=3: 0 0 2 19
    """
    return len(all_pure_strata(g, r, markings, moduli_type))


def single_stratum(num, g, r, markings=(), moduli_type=MODULI_ST):
    r"""
    Return the ``num``-th stratum.
    """
    return all_strata(g, r, markings, moduli_type)[num]


def single_pure_stratum(num, g, r, markings=(), moduli_type=MODULI_ST):
    r"""
    Return the ``num``-th pure stratum.
    """
    return all_pure_strata(g, r, markings, moduli_type)[num]


@cached_function
def autom_count(num, g, r, markings=(), moduli_type=MODULI_ST):
    return graph_count_automorphisms(single_stratum(num, g, r, markings, moduli_type))


@cached_function
def pure_strata_autom_count(num, g, r, markings=(), moduli_type=MODULI_ST):
    return graph_count_automorphisms(single_pure_stratum(num, g, r, markings, moduli_type))


@cached_function
def automorphism_cosets(num, g, r, markings=(), moduli_type=MODULI_ST):
    G = single_stratum(num, g, r, markings, moduli_type)
    pureG = Graph(G.M)
    pureG.purify()
    pureG.compute_invariant()
    pure_auts = graph_list_isomorphisms(pureG, pureG)
    num_pure = len(pure_auts)
    impure_auts = graph_list_isomorphisms(G, G)
    num_impure = len(impure_auts)
    chosen_auts = []
    used_auts = []
    v = G.num_vertices()
    e = G.num_edges()
    for i in range(num_pure):
        if i not in used_auts:
            chosen_auts.append(pure_auts[i])
            for g in impure_auts:
                sigma = [[pure_auts[i][0][g[0][k] - 1]
                          for k in range(v)], [pure_auts[i][1][g[1][k] - 1] for k in range(e)]]
                for ii in range(num_pure):
                    if pure_auts[ii] == sigma:
                        used_auts.append(ii)
                        break
    return [num_impure, chosen_auts]


@cached_function
def unpurify_map(g, r, markings=(), moduli_type=MODULI_ST):
    r"""
    Return a dictionary which maps pure strata to list of strata.

    EXAMPLES::

        sage: from admcycles.DR.graph import unpurify_map
        sage: unpurify_map(2, 2)
        {(0, 0): [0, 1], (1, 0): [2, 3], (1, 1): [4, 5], (2, 0): [6], (2, 1): [7]}
    """
    unpurify = {}
    pure_strata = [all_pure_strata(g, r0, markings, moduli_type)
                   for r0 in range(r + 1)]
    impure_strata = all_strata(g, r, markings, moduli_type)
    for i, strati in enumerate(impure_strata):
        G = Graph(strati.M)
        G.purify()
        r0 = G.num_edges() - len(markings)
        found = False
        for j in range(len(pure_strata[r0])):
            if G.M == pure_strata[r0][j].M:
                G_key = (r0, j)
                found = True
                break
        assert found, "failed purification"
        if G_key not in unpurify:
            unpurify[G_key] = []
        unpurify[G_key].append(i)
    return unpurify


@file_cache.file_cached_function(
    directory=os.path.join(DOT_SAGE, "admcycles"),
    key=file_cache.ignore_args_key([]),
    filename=file_cache.ignore_args_filename())
def all_strata(g, r, markings=(), moduli_type=MODULI_ST):
    r"""
    Return the lists of strata with given genus, degree, markings and moduli.

    EXAMPLES::

        sage: from admcycles.DR.graph import all_strata
        sage: all_strata(2, 1, (1, 1))
        [[   -1     1     1]
         [X + 2     1     1],
         [   -1     1     1]
         [    2 X + 1     1],
         [-1  1  1  0]
         [ 0  1  1  1]
         [ 2  0  0  1],
         [-1  1  1  0]
         [ 1  0  0  1]
         [ 1  1  1  1],
         [-1  1  1  0]
         [ 1  0  1  1]
         [ 1  1  0  1],
         [-1  0  1  1]
         [ 1  2  1  1]]
    """
    mod_size = moduli_type + 1
    if moduli_type == MODULI_SMALL:
        mod_size = MODULI_SM + 1
    big_list = [[] for i in range(mod_size)]
    for loops in range(g + 1):
        if loops == 1 and moduli_type <= MODULI_CT:
            break
        if loops > r:
            break
        for edges in range(r - loops + 1):
            if edges == 1 and moduli_type <= MODULI_SM:
                break
            G = Graph()
            G.add_vertex(g - loops)
            for k in range(loops):
                G.add_edge(1, 1)
            for k in markings:
                G.add_edge(1, 0, k)
            GGG = [[] for i in range(mod_size)]
            if loops == 0:
                if edges == 0:
                    GGG[MODULI_SM] = [G]
                else:
                    GGG[MODULI_RT] = [G]
            else:
                GGG[MODULI_ST] = [G]
            for k in range(edges):
                GGG = degenerate(GGG, moduli_type)
            GGG = decorate(GGG, r - loops - edges, moduli_type)
            for i in range(mod_size):
                big_list[i] += GGG[i]
    combined_list = []
    for i in range(mod_size):
        combined_list += big_list[i]
    return combined_list


@cached_function
def all_pure_strata(g, r, markings=(), moduli_type=MODULI_ST):
    r"""
    Return the lists of pure strata with given genus, degree, markings and moduli.

    EXAMPLES::

        sage: from admcycles.DR.graph import all_pure_strata
        sage: from admcycles.DR.moduli import MODULI_CT
        sage: all_pure_strata(2, 0, (1, 1))
        [[-1  1  1]
         [ 2  1  1]]
        sage: all_pure_strata(2, 1, (1, 1), MODULI_CT)
        [[-1  1  1  0]
         [ 0  1  1  1]
         [ 2  0  0  1],
         [-1  1  1  0]
         [ 1  0  0  1]
         [ 1  1  1  1],
         [-1  1  1  0]
         [ 1  0  1  1]
         [ 1  1  0  1]]
    """
    big_list = [[] for i in range(moduli_type + 1)]
    for loops in range(g + 1):
        if loops == 1 and moduli_type <= MODULI_CT:
            break
        if loops > r:
            break
        for edges in range(r - loops, r - loops + 1):
            if edges >= 1 and moduli_type <= MODULI_SM:
                break
            G = Graph()
            G.add_vertex(g - loops)
            for k in range(loops):
                G.add_edge(1, 1)
            for k in markings:
                G.add_edge(1, 0, k)
            G.compute_invariant()
            GGG = [[] for i in range(moduli_type + 1)]
            if loops == 0:
                if edges == 0:
                    GGG[MODULI_SM] = [G]
                else:
                    GGG[MODULI_RT] = [G]
            else:
                GGG[MODULI_ST] = [G]
            for k in range(edges):
                GGG = degenerate(GGG, moduli_type)
            for i in range(moduli_type + 1):
                big_list[i] += GGG[i]
    combined_list = []
    for i in range(moduli_type + 1):
        combined_list += big_list[i]
    return combined_list


@cached_function
def strata_invariant_lookup(g, r, markings=(), moduli_type=MODULI_ST):
    inv_dict = {}
    L = all_strata(g, r, markings, moduli_type)
    for i in range(len(L)):
        if L[i].invariant not in inv_dict:
            inv_dict[L[i].invariant] = []
        inv_dict[L[i].invariant].append(i)
    return inv_dict


@cached_function
def num_of_stratum(G, g, r, markings=(), moduli_type=MODULI_ST):
    r"""
    Return the index of the graph ``G`` in the list of all strata with given
    genus, rank, markings and moduli type.

    This is the inverse of :func:`single_stratum`.

    EXAMPLES::

        sage: from admcycles.DR.graph import Graph, X, R, num_of_stratum
        sage: G = Graph(matrix(R, 2, 3, [-1, 1, 2, X+1, 1, 1]))
        sage: num_of_stratum(G, 1, 1, (1, 2))
        0
    """
    G.compute_invariant()
    L = all_strata(g, r, markings, moduli_type)
    LL = strata_invariant_lookup(g, r, markings, moduli_type)
    x = LL[G.invariant]

    if len(x) == 1:
        return x[0]
    for i in x:
        if graph_isomorphic(G, L[i]):
            return i

    raise ValueError("wrong Graph with g={}, r={}, markings={}, moduli_type={}\n{}".format(
        g, r, markings, moduli_type, G))


def list_strata(g, r, n=0, moduli_type=MODULI_ST):
    """
    Displays the list of all strata.

    EXAMPLES::

        sage: from admcycles.DR.graph import list_strata
        sage: list_strata(1,1,2)
        generator 0
        [   -1     1     2]
        [X + 1     1     1]
        ------------------------------
        generator 1
        [   -1     1     2]
        [    1 X + 1     1]
        ------------------------------
        generator 2
        [   -1     1     2]
        [    1     1 X + 1]
        ------------------------------
        generator 3
        [-1  1  2  0]
        [ 0  1  1  1]
        [ 1  0  0  1]
        ------------------------------
        generator 4
        [-1  0  1  2]
        [ 0  2  1  1]
        ------------------------------
    """
    L = all_strata(g, r, tuple(range(1, n + 1)), moduli_type)
    for i, Li in enumerate(L):
        print("generator %s" % i)
        print(Li.M)
        print("-" * 30)


@cached_function
def contraction_table(g, r, markings=(), moduli_type=MODULI_ST):
    contraction_dict = {}
    pure_strata = [all_pure_strata(g, r0, markings, moduli_type)
                   for r0 in range(r + 1)]
    for r0 in range(r + 1):
        for ii in range(len(pure_strata[r0])):
            G = pure_strata[r0][ii]
            S = [j for j in range(1, G.M.ncols()) if G.M[0, j] == 0]
            contractions = {}
            for edge_subset in itertools.product(*[[0, 1] for i in range(r0)]):
                key = tuple(i for i in range(
                    r0) if edge_subset[i] == 0)
                A = [S[i] for i in key]
                A.reverse()
                vlist = [[i] for i in range(1, G.M.nrows())]
                elist = list(range(1, G.M.ncols()))
                Gcopy = Graph(G.M)
                for i in A:
                    vlist, elist = Gcopy.contract(i, vlist, elist)
                Gcopy.compute_invariant()
                rnew = r0 - len(A)
                contraction_result = []
                for i in range(len(pure_strata[rnew])):
                    L = graph_list_isomorphisms(
                        pure_strata[rnew][i], Gcopy, True)
                    if L:
                        contraction_result.append((rnew, i))
                        contraction_result.append(L[0])
                        break
                contraction_result.append((vlist, elist))
                contractions[key] = contraction_result

            for edge_assignment in itertools.product(*[[0, 1, 2] for i in range(r0)]):
                if sum(1 for i in edge_assignment if i == 1) > r - r0:
                    continue
                key1 = tuple(i for i in range(
                    r0) if edge_assignment[i] == 0)
                B = [S[i]
                     for i in range(r0) if edge_assignment[i] == 1]
                key2 = tuple(i for i in range(
                    r0) if edge_assignment[i] == 2)
                if key1 > key2:
                    continue
                contract1 = contractions[key1]
                contract2 = contractions[key2]
                dict_key = [contract1[0], contract2[0]]
                dict_entry = [contract1[1], contract2[1]]
                if dict_key[0] > dict_key[1]:
                    dict_key.reverse()
                    dict_entry.reverse()
                    dict_entry = [(r0, ii), B, contract2[2],
                                  contract1[2]] + dict_entry
                else:
                    dict_entry = [(r0, ii), B, contract1[2],
                                  contract2[2]] + dict_entry
                dict_key = tuple(dict_key)
                if dict_key not in contraction_dict:
                    contraction_dict[dict_key] = []
                contraction_dict[dict_key].append(dict_entry)
                if dict_key[0] == dict_key[1]:
                    contraction_dict[dict_key].append(
                        dict_entry[:2] + [dict_entry[3], dict_entry[2], dict_entry[5], dict_entry[4]])
    return contraction_dict
