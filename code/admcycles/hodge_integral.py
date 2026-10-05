# encoding: utf-8
r"""
Hodge integrals
"""

from admcycles.admcycles import lambdaclass, psiclass, kappaclass

from sage.misc.cachefunc import cached_function
from sage.misc.misc_c import prod


def hodge_integral(g, lambdas, psis, kappas=[], n=None, method='stupid'):
    r"""
        Computes a Hodge integral, i.e. the intersection number given by a monomial of psi- and
        lambda-classes on the moduli space of stable curves.

    INPUT:

    - ``g`` -- integer ; genus of the moduli space of curves

    - ``lambdas`` -- list of integers ; a list of subscripts [a_1,..,a_r] gives the
      monomial: lambda_{a_1}*...*lambda_{a_r}

    - ``psis`` -- list of integers ; a list of subscripts [b_1,..,b_r] gives the
      monomial: psis_{1}^{b_1}*...*psis_{r}^{b_r}

    - ``kappas`` -- list of integers (default: `[]`) ; a list of subscripts [c_1,..,c_r] gives the
      monomial: kappa_{c_1}*...*kappa_{c_r}

    - ``n`` -- integer (default: `None`) ; the number of marked points of the moduli space of curves.
      If no value is provided then n is equal to the length of ``psis``

    - ``method`` -- string (default: `stupid`) ; the method used to compute the Hodge integral.
      The `stupid` method defines the classes in the tautological ring and then evaluates their intersection.

    EXAMPLES::

      sage: from admcycles.hodge_integral import hodge_integral
      sage: hodge_integral(1,[1],[],n=1)
      1/24
      sage: hodge_integral(2,[2],[1,0,1],[1,1])
      7/36
    """
    if n is None:
        n = len(psis)
    else:
        if len(psis) > n:
            raise ValueError("The number of distinct psi-clases is higher than the number of points")
    return cashable_hodge_integral(g, tuple(sorted(lambdas)), tuple([0] * (n - len(psis)) + sorted(psis)), tuple(sorted(kappas)), method=method)


@cached_function
def cashable_hodge_integral(g, lambdas, psis, kappas, method='stupid'):
    r"""
        Computes a Hodge integral and is cashable. Is called by the method ``hodge_integral``.
    """
    if method == 'stupid':
        n = len(psis)
        monomial = prod(lambdaclass(lam, g, n) for lam in lambdas)
        monomial *= prod(psiclass(i + 1, g, n)**psis[i] for i in range(n) if not psis[i] == 0)
        monomial *= prod(kappaclass(i, g, n) for i in kappas)
        return monomial.evaluate()
    raise NotImplementedError("please write a smart hodge integral function")
