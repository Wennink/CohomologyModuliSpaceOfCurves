r"""
This data comes from upcoming work by Jonas Bergström, Samir Canning, Dan Petersen and Johannes Schmitt.
As of 26/03/26
"""
from sage.rings.all import PolynomialRing, ZZ
from sage.combinat.sf.sf import SymmetricFunctions
R = PolynomialRing(ZZ, 1, ('L'))
L = R.gens()[0]
s = SymmetricFunctions(R).schur()

eMbar = {}
# Sn-equivariant Euler characteristics of moduli spaces of stable n-pointed curves of genus 5
eMbar[(5, 0)] = (L**12 + 4 * L**11 + 19 * L**10 + 65 * L**9 + 165 * L**8 + 291 * L**7 + 355 * L**6 + 291 * L**5 + 165 * L**4 + 65 * L**3 + 19 * L**2 + 4 * L + 1) * s[()]
