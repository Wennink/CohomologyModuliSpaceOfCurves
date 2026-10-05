r"""
Moduli types
"""

from sage.rings.integer_ring import ZZ

# NOTE: due to the addition of MODULI_TL in admcycles/moduli.py, which is not
# present in Pixton code there is a mismatch between the values of MODULI_ST
# (3 here and 4 in admcycles/moduli.py).
# All functions calling DR.py with the option moduli_type should use the
# function get_moduli(m, DRpy=True) to correctly translate to the conventions
# of Pixton's DR code.
MODULI_SMALL = -1  # ??
MODULI_SM = 0
MODULI_RT = 1
MODULI_CT = 2
MODULI_ST = 3


def dim_form(g, n, moduli_type=MODULI_ST):
    g = ZZ(g)
    n = ZZ(n)
    if moduli_type == MODULI_ST:
        return 3 * g - 3 + n
    if moduli_type == MODULI_CT:
        return 2 * g - 3 + n
    if moduli_type == MODULI_RT:
        if g > 0:
            return g - 2 + n
        else:
            return n - 3
    if moduli_type == MODULI_SM:
        if n == 0:
            return g - 2
        elif g >= 1:
            return g - 1
        else:
            return ZZ.zero()
    if moduli_type == MODULI_SMALL:
        return ZZ(1000)
    return 3 * g - 3 + n
