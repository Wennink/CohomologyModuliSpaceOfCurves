# -*- coding: utf-8 -*-
r"""
The possible different moduli.
"""

import numbers

# Moduli types
MODULI_SM = 0  # smooth (no edge, just the trivial graph)
MODULI_RT = 1  # rational tails (tree with genus 0 vertices but one)
MODULI_CT = 2  # compact type (tree with any kind of vertices)
MODULI_TL = 3  # tree like (tree with self-loops)
MODULI_ST = 4  # stable curves (general case)

_moduli_to_str = {
    MODULI_SM: 'sm',    # smooth curves
    MODULI_RT: 'rt',    # rational tails
    MODULI_CT: 'ct',    # compact type
    MODULI_TL: 'tl',    # tree like
    MODULI_ST: 'st'     # all stable curves
}
_str_to_moduli = {
    'sm': MODULI_SM,
    'SM': MODULI_SM,
    'smooth': MODULI_SM,
    'rt': MODULI_RT,
    'RT': MODULI_RT,
    'rational_tails': MODULI_RT,
    'ct': MODULI_CT,
    'CT': MODULI_CT,
    'compact_type': MODULI_CT,
    'tl': MODULI_TL,
    'TL': MODULI_TL,
    'tree_like': MODULI_TL,
    'st': MODULI_ST,
    'ST': MODULI_ST,
    'stable': MODULI_ST}


def get_moduli(arg, default=MODULI_ST, DRpy=False):
    if DRpy:
        return min(3, get_moduli(arg, default))
    if arg is None:
        return default
    elif isinstance(arg, str):
        try:
            return _str_to_moduli[arg]
        except KeyError:
            raise ValueError('invalid moduli {!r}'.format(arg))
    elif isinstance(arg, numbers.Integral):
        if arg < MODULI_SM or arg > MODULI_ST:
            raise ValueError('invalid moduli {!r}'.format(arg))
        return int(arg)
    else:
        raise TypeError("invalid moduli; must be a string 'sm', 'rt', 'ct', 'tl', or 'st' (got {!r})".format(arg))


def socle_degree(g, n, moduli):
    if moduli == MODULI_ST:
        # stable curves
        return 3 * g - 3 + n
    elif moduli == MODULI_TL:
        # tree-like
        # TODO: this is an over estimation. It is very likely that the socle dimension
        # is smaller.
        return 3 * g - 3 + n
    elif moduli == MODULI_CT:
        # compact type
        return 2 * g - 3 + n
    elif moduli == MODULI_RT:
        # rational tails
        return g - 2 + n - (g == 0)
    elif moduli == MODULI_SM:
        # smooth
        return g - 1 + (g == 0) - (n == 0)
    else:
        raise ValueError('unknown moduli')


def num_edges_bound(g, n, moduli):
    r"""
    Return the maximum number of edges a stable graph with genus
    ``g`` and number of markings ``n`` can have in the given ``moduli``.
    """
    if moduli == MODULI_TL or moduli == MODULI_ST:
        # tree like and stable
        return 3 * g - 3 + n
    elif moduli == MODULI_CT:
        # compact type
        return 2 * g - 3 + n
    elif moduli == MODULI_RT:
        # rational tails
        return n - (n != 0) - 2 * (g == 0)
    elif moduli == MODULI_SM:
        # smooth
        return 0
    else:
        raise ValueError('unknown moduli')
