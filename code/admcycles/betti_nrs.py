from sage.rings.all import PolynomialRing, ZZ
from sage.combinat.sf.sf import SymmetricFunctions

from .data.eMbar0n import eMbar as e0
from .data.eMbar1n import eMbar as e1
from .data.eMbar2n import eMbar as e2
from .data.eMbar3n import eMbar as e3
from .data.eMbar4n import eMbar as e4
from .data.eMbar5n import eMbar as e5


def get_betti(g, n, r, n_part=None):
    if n_part is None:
        n_part = [1] * n
    R = PolynomialRing(ZZ, 1, ('L'))
    L = R.gens()[0]
    m = SymmetricFunctions(R).monomial()
    eMbar = [e0, e1, e2, e3, e4, e5]
    try:
        return m(eMbar[g][(g, n)]).coefficient(n_part).coefficient({L: r})
    except (IndexError, KeyError):
        return None
