from .admcycles import list_strata
from . import file_cache
import os
from sage.env import DOT_SAGE
from sage.matrix.constructor import matrix


@file_cache.file_cached_function(
    directory=os.path.join(DOT_SAGE, "admcycles/cohomology"),
    key=file_cache.ignore_args_key([]),
    filename=file_cache.ignore_args_filename())
def list_strata_can(g, n, r):
    r"""
    Stores a list of the canonical form of all graphs of genus g with n marked points and r edges.
    """
    result = []
    for G in list_strata(g, n, r):
        G2 = G.copy(mutable=True)
        G2.set_canonical_label(sortlegs=True)
        result.append(G2)
    return result


def list_strata_compactification_of_ct(g, n, gamma_r):
    r"""
    Returns the indices of bridgeless graphs
    """
    if gamma_r == 0:
        return [0]
    result = []
    for i, gamma in enumerate(list_strata_can(g, n, gamma_r)):
        cb = gamma.cycle_basis()
        if cb == []:
            continue
        if not any(c.is_zero() for c in matrix(cb).columns()):
            result.append(i)
    return result


def list_strata_compactification_of_rt(g, n, gamma_r):
    r"""
    Returns the indices of graphs without rational tails
    """
    result = []
    for i, gamma in enumerate(list_strata_can(g, n, gamma_r)):
        non_rt = True
        for v, g in enumerate(gamma.genera()):
            if g == 0:
                non_mp_he = 0
                for he in gamma.legs(v):
                    if he > n:
                        non_mp_he += 1
                if non_mp_he < 2:
                    non_rt = False
                    break
        if non_rt:
            result.append(i)
    return result


def get_strata_list_inds(g, n, gamma_r, moduli_type):
    r"""
    Return the indices of graphs appearing in the spectral
    sequence for the moduli of curves of type ``moduli_type``
    """
    if moduli_type == 'sm':
        return list(range(len(list_strata_can(g, n, gamma_r))))
    elif moduli_type == 'ct':
        return list_strata_compactification_of_ct(g, n, gamma_r)
    elif moduli_type == 'rt':
        return list_strata_compactification_of_rt(g, n, gamma_r)
    else:
        raise ValueError(f'cannot accept moduli type {moduli_type}, it should be sm, ct, or rt')
