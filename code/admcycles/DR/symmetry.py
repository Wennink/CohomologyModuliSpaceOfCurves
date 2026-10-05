from .graph import all_strata, num_strata, R, Graph, num_of_stratum
from .algebra import get_marks
from .utils import simplify_sparse
from .moduli import MODULI_ST

from collections import defaultdict
from sage.misc.cachefunc import cached_function
from sage.rings.rational_field import QQ

from .. import file_cache
from sage.env import DOT_SAGE
import os


def symmetrize_map_simple(g, r, markings, symm_markings, moduli_type):
    r"""
    Returns the map for symmetrizing a stratum by replacing its ``markings`` with ``symm_markings``.
    Requires ``symm_markings`` to be more symmetrized than ``markings``.
    """
    gens = all_strata(g, r, markings, moduli_type)
    dif = markings.count(1) - 2
    symm_map = []
    for G in gens:
        GG = Graph(G.M)
        for i in range(1, GG.M.ncols()):
            if GG.M[0, i][0] > 0:
                GG.M[0, i] = R(symm_markings[GG.M[0, i][0] + dif])
        symm_map.append(num_of_stratum(GG, g, r, symm_markings, moduli_type))
    return symm_map


@file_cache.file_cached_function(
    directory=os.path.join(DOT_SAGE, "admcycles"),
    key=file_cache.ignore_args_key([]),
    filename=file_cache.ignore_args_filename())
def symmetrize_map(g, r, markings, symm_markings, moduli_type):
    if symm_markings.count(2) <= 1:
        return symmetrize_map_simple(g, r, markings, symm_markings, moduli_type)

    # test if the ordering of the symm_markings and the markings are compatible
    test_dic = defaultdict(list)
    for i, m in enumerate(markings):
        test_dic[m].append(i)
    for L in test_dic.values():
        assert (len(set([symm_markings[i] for i in L])) == 1)

    sorted_symm_markings = tuple(sorted(symm_markings))

    # am assuming all points are ordered in the graph matrices
    gens = all_strata(g, r, markings, moduli_type)
    symm_map = []
    for G in gens:
        GG = Graph(G.M)
        nr = 0
        plus = -1
        for i in range(1, GG.M.ncols()):
            if GG.M[0, i][0] > 0:
                if GG.M[0, i][0] == nr:
                    plus += 1
                nr = GG.M[0, i][0]
                GG.M[0, i] = R(symm_markings[GG.M[0, i][0] + plus])
        symm_map.append(num_of_stratum(GG, g, r, sorted_symm_markings, moduli_type))
    return symm_map


@file_cache.file_cached_function(
    directory=os.path.join(DOT_SAGE, "admcycles/newrels"),
    env_var="ADMCYCLES_CACHE_DIR",
    key=file_cache.ignore_args_key([]),
    filename=file_cache.ignore_args_filename())
def partial_unsymmetrize_map(g, r, markings, symm_markings, moduli_type):
    r"""
    Returns map that replaces a stratum with ``markings`` by a linear
    combination of strata with ``symm_markings``.

    This function is an inverse of :func:`symmetrize_map`. The coefficient of
    each stratum in the output is the size of its orbit under the corresponding
    symmetric action.  Requires ``symm_markings`` to be more symmetrized than
    ``markings``.
    """
    target_symm = markings.count(1)
    symm = symm_markings.count(1)
    n = len(markings)
    if target_symm == symm:
        print("this should not be happening?")
        return -1
    if target_symm + 1 < symm:
        return [partial_unsymmetrize_vec(us, g, r, markings, get_marks(n, target_symm + 1), moduli_type) for us in partial_unsymmetrize_map(g, r, get_marks(n, target_symm + 1), symm_markings, moduli_type)]
    gens = all_strata(g, r, markings, moduli_type)
    orbits = {}
    for i in range(len(gens)):
        if i in orbits.keys():
            continue
        orbits[i] = 1
        G = gens[i]
        for j in range(1, G.M.ncols()):
            if G.M[0, j][0] == 2:
                pt2 = j
                break
        for j in range(1, G.M.ncols()):
            if G.M[0, j][0] == 1:
                GG = Graph(G.M)
                GG.M[0, j] += 1
                GG.M[0, pt2] -= 1
                num = num_of_stratum(GG, g, r, markings, moduli_type)
                if num in orbits.keys():
                    orbits[num] = orbits[num] + 1
                else:
                    orbits[num] = 1
    symm_map = symmetrize_map(g, r, markings, symm_markings, moduli_type)
    result = [[] for i in range(num_strata(g, r, symm_markings, moduli_type))]
    for k in orbits.keys():
        result[symm_map[k]].append([k, orbits[k]])
    return result


def partial_unsymmetrize_vec(vec, g, r, markings, symm_markings, moduli_type):
    r"""
    Applies partial_symmetrize_map to a relation to calculate its unsymmetrized version.
    """
    if markings == symm_markings:
        return vec
    unsym_map = partial_unsymmetrize_map(g, r, markings, symm_markings, moduli_type)
    vec2 = []
    for x in vec:
        aut = 0
        for j in unsym_map[x[0]]:
            aut += j[1]
        for j in unsym_map[x[0]]:
            vec2.append([j[0], x[1] * j[1] / QQ(aut)])
    vec2 = simplify_sparse(vec2)
    return vec2


# this is faster than partial_unsymmetrize_map when both are defined
@cached_function
def unsymmetrize_map(g, r, markings=(), moduli_type=MODULI_ST):
    r"""
    Does the same as partial_unsymmetrize_map but is faster.
    Only works for unsymmetrizing from complete symmetry.
    """
    markings2 = tuple([1 for i in markings])
    sym_map = symmetrize_map(g, r, markings, get_marks(len(markings), len(markings)), moduli_type)
    map = [[] for i in range(num_strata(g, r, markings2, moduli_type))]
    for i in range(len(sym_map)):
        map[sym_map[i]].append(i)
    return map


def unsymmetrize_vec(vec, g, r, markings=(), moduli_type=MODULI_ST):
    unsym_map = unsymmetrize_map(g, r, markings, moduli_type)
    vec2 = []
    for x in vec:
        aut = len(unsym_map[x[0]])
        for j in unsym_map[x[0]]:
            vec2.append([j, x[1] / QQ(aut)])
    vec2 = simplify_sparse(vec2)
    return vec2
