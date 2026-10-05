from .admcycles import generating_indices, genstobasis, Graphtodecstratum, tautgens
from . import DR
from . import file_cache
import os
from sage.env import DOT_SAGE
from .moduli import get_moduli
from .utils import get_marks_part
from .DR.graph import Graph as pixGraph
from .DR.relations import symmetrize_map
from sage.rings.all import QQ
from sage.combinat.all import Partitions
import itertools
from sage.misc.cachefunc import cached_function


@file_cache.file_cached_function(
    directory=os.path.join(DOT_SAGE, "admcycles"),
    env_var="ADMCYCLES_CACHE_DIR",
    key=file_cache.ignore_args_key([5]),
    filename=file_cache.ignore_args_filename())
def generating_indices_Sn(g, n, r, n_part, moduli='st', method=None):
    r"""
    Stores indices of generators of (S_{g,n}^r)^(S_{n_part}) that
    together form a basis for (S_{g,n}^r/P_{g,n}^r)^(S_{n_part})
    """
    if sorted(n_part, reverse=True) != list(n_part):
        raise ValueError('wrong n_part order')
    raise ValueError(f'not in cache for g={g}, n={n}, r={r}, n_part={n_part}, moduli={moduli}')


@file_cache.file_cached_function(
    directory=os.path.join(DOT_SAGE, "admcycles"),
    env_var="ADMCYCLES_CACHE_DIR",
    pickle_wrappers=(file_cache.rational_vectors_to_py, file_cache.py_to_rational_vectors))
def genstobasis_Sn(g, n, r, n_part, moduli='st'):
    r"""
    Stores a map from generators of (S_{g,n}^r)^(S_{n_part})
    to the basis from ``generating_indices_Sn``
    """
    if sorted(n_part, reverse=True) != list(n_part):
        raise ValueError('wrong n_part order')
    raise ValueError(f'not in cache for g={g}, n={n}, r={r}, n_part={n_part}, moduli={moduli}')


def general_generating_indices(g, n, r, n_part, moduli='st', method=None):
    r"""
    A generalization of ``generating_indices`` to (S_{g,n}^r/P_{g,n}^r)^(S_{n_part})
    """
    if n_part.count(1) == len(n_part):
        return generating_indices(g, n, r, moduli=moduli, FZmethod=method)
    return generating_indices_Sn(g, n, r, n_part=tuple(n_part), moduli=moduli, method=method)


def general_genstobasis(g, n, r, n_part, moduli='st'):
    r"""
    A generalization of ``genstobasis`` to (S_{g,n}^r/P_{g,n}^r)^(S_{n_part})
    """
    if n_part.count(1) == len(n_part):
        return genstobasis(g, n, r, moduli=moduli)
    return genstobasis_Sn(g, n, r, n_part=tuple(n_part), moduli=moduli)


def less_symmetric_partitions(part):
    r"""
    Returns a dictionary where the keys are partitions lambda such that lambda <= ``part``
    The values are maps describing how the symmetrization affects the ordering of the marked points

    EXAMPLES::
        sage: from admcycles.symmetry import less_symmetric_partitions
        sage: less_symmetric_partitions([3,2,1])
        {(3, 2, 1): (1, 1, 1, 2, 2, 3),
         (3, 1, 1, 1): (1, 1, 1, 2, 2, 3),
         (2, 2, 1, 1): (1, 1, 2, 2, 1, 3),
         (2, 1, 1, 1, 1): (1, 1, 1, 2, 2, 3),
         (1, 1, 1, 1, 1, 1): (1, 1, 1, 2, 2, 3)}
    """
    parts = {}
    for ip in itertools.product(*[Partitions(p) for p in part]):
        new_part_map = [(a, i + 1) for i, b in enumerate(ip) for a in b]
        new_part_map.sort(key=lambda x: (-x[0], x[1]))
        new_part = tuple([a for a, _ in new_part_map])
        if new_part in parts:
            continue
        markings_map = []
        for a, b in new_part_map:
            markings_map += [b] * a
        parts[new_part] = tuple(markings_map)
    return parts


def better_unsymmetrize_map(g, n, r, n_part):
    symmarks = get_marks_part(n, n_part)
    moduli = get_moduli('st', DRpy=True)
    unsym = [[] for _ in range(len(DR.all_strata(g, r, symmarks, moduli_type=moduli)))]
    for i, s in enumerate(symmetrize_map(g, r, tuple(range(1, n + 1)), symmarks, moduli_type=moduli)):
        unsym[s].append(i)
    return unsym


def get_orbits(g, n, r, n_part):
    r"""
    Returns a list of orbits of tautological generators

    EXAMPLES::
        sage: from admcycles.symmetry import get_orbits
        sage: get_orbits(1,2,1,(2,))
        [[Graph :      [1] [[1, 2]] []
          Polynomial : (kappa_1)_0],
         [Graph :      [1] [[1, 2]] []
          Polynomial : 1/2*psi_1,
          Graph :      [1] [[1, 2]] []
          Polynomial : 1/2*psi_2]]
    """
    # consider doing things in a separate process in order to kill memory
    L = DR.all_strata(g, r, tuple(range(1, n + 1)), moduli_type=get_moduli('st', DRpy=True))
    unsymmap = better_unsymmetrize_map(g, n, r, n_part)
    result = []
    for i in general_generating_indices(g, n, r, n_part):
        temp = []
        # divide by size of orbit
        coeff = QQ((1, len(unsymmap[i])))
        for j in unsymmap[i]:
            temp.append(coeff * Graphtodecstratum(L[j]))
        result.append(temp)
    return result


#############################
# tautgens functions
#############################


# tautgens_sym returns representatives of the sym graphs, unlike tautgens which returns graphs as they are on the Pixton side
@cached_function
def tautgens_sym(g, n, r, n_part, moduli='st', sym_labels=False):
    r"""
    Returns a list of tautlogical generators as ``decstratum`` classes.
    When ``sym_labels`` is False we give representatives of
    the S_{n_part}-equivalence class. When ``sym_labels`` is True we
    label all vertices the same way as they are in the DR code.

    EXAMPLES::
        sage: from admcycles.symmetry import tautgens_sym
        sage: tautgens_sym(1,2,1,(2,),sym_labels=False)[2]
        Graph :      [0, 1] [[1, 2, 4], [5]] [(4, 5)]
        Polynomial : 1
        sage: tautgens_sym(1,2,1,(2,),sym_labels=True)[2]
        Graph :      [0, 1] [[1, 1, 4], [5]] [(4, 5)]
        Polynomial : 1
    """
    if len(n_part) == n:
        return tautgens(g, n, r, decst=True, moduli=moduli)
    L = DR.all_strata(g, r, get_marks_part(n, n_part), moduli_type=get_moduli(moduli, DRpy=True))
    if sym_labels:
        return [Graphtodecstratum(l) for l in L]
    result = []
    for GG in L:
        G = pixGraph(GG.M)
        nr = 1
        for i in range(G.M.ncols()):
            if G.M[0, i] > 0:
                G.M[0, i] = nr
                nr += 1
        result.append(Graphtodecstratum(G))
    return result


def tautgens_single(g, n, r, i, moduli='st', n_part=None, sym_labels=False):
    r"""
    Similar to ``tautgen_sym`` except it returns only the ``i``-th item on the list.
    Unlike ``tautgens_sym``, this does not convert the whole ``DR.all_strata`` list
    to decstrata but only its ``i``-th entry.
    """
    if n_part is None:
        markings = tuple(range(1, n + 1))
    else:
        markings = get_marks_part(n, n_part)
    G = DR.all_strata(g, r, markings, moduli_type=get_moduli(moduli, DRpy=True))[i]
    if not sym_labels:
        G = pixGraph(G.M)
        nr = 1
        for i in range(G.M.ncols()):
            if G.M[0, i] > 0:
                G.M[0, i] = nr
                nr += 1
    return Graphtodecstratum(G)


@cached_function
def tautgens_basis(g, n, r, n_part=None, moduli='st'):
    r"""
    Similar to ``tautgen_sym`` but returns only the basis elements prescribed
    by ``general_generating_indices``.
    """
    if n_part is None:
        markings = tuple(range(1, n + 1))
    else:
        markings = get_marks_part(n, n_part)
    L = DR.all_strata(g, r, markings, moduli_type=get_moduli(moduli, DRpy=True))
    result = []
    for ind in general_generating_indices(g, n, r, n_part, moduli=moduli):
        G = pixGraph(L[ind].M)
        nr = 1
        for i in range(G.M.ncols()):
            if G.M[0, i] > 0:
                G.M[0, i] = nr
                nr += 1
        result.append(Graphtodecstratum(G))
    return result
