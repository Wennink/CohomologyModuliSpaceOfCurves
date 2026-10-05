# -*- coding: utf-8 -*-
r"""
Test the deprecations from the former tautclass (see https://gitlab.com/modulispaces/admcycles/-/merge_requests/109)::

    sage: from admcycles import *
    sage: from admcycles.admcycles import *

    sage: gamma = StableGraph([1,2],[[1,2],[3]],[(2,3)])
    sage: ds1 = decstratum(gamma, kappa=[[1],[]]); ds1
    Graph :      [1, 2] [[1, 2], [3]] [(2, 3)]
    Polynomial : (kappa_1)_0
    sage: ds2 = decstratum(gamma, kappa=[[],[1]]); ds2
    Graph :      [1, 2] [[1, 2], [3]] [(2, 3)]
    Polynomial : (kappa_1)_1
    sage: t = tautclass([ds1, ds2])
    sage: (t - gamma.to_tautclass() * kappaclass(1,3,1)).is_zero()
    doctest:...: DeprecationWarning: to_tautclass is deprecated. Please use to_tautological_class instead.
    See https://gitlab.com/modulispaces/admcycles/-/merge_requests/109 for details.
    True

    sage: b = StableGraph([1],[[1,2,3]],[(2,3)]).to_tautclass()
    sage: b.toTautbasis()
    doctest:...: DeprecationWarning: toTautbasis is deprecated. Please use basis_vector instead.
    See https://gitlab.com/modulispaces/admcycles/-/merge_requests/109 for details.
    (10, -10, -14)
    sage: b.toTautbasis(moduli='ct',r=1)
    (0, 0)
    sage: c = psiclass(1,2,2)**2
    sage: for mod in ('st', 'tl', 'ct', 'rt', 'sm'):
    ....:     print(c.toTautbasis(moduli = mod,r=2))
    doctest:...:     DeprecationWarning: toTautbasis is deprecated. Please use basis_vector instead.
    See https://gitlab.com/modulispaces/admcycles/-/merge_requests/109 for details.
    (0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0)
    (0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0)
    (5/6, -1/6, 1/3, 0, 0)
    (1)
    ()

    sage: a = psiclass(1,2,3)
    sage: t = a + a*a
    sage: t.gnr_list()
    doctest:...: DeprecationWarning: gnr_list is deprecated. Please use degree_list instead.
    See https://gitlab.com/modulispaces/admcycles/-/merge_requests/109 for details.
    [(2, 3, 1), (2, 3, 2)]

    sage: psiclass(1, 1, 1).toprodtautclass(1, 1)
    doctest:...: DeprecationWarning: the arguments 'g' and 'n' of TautologicalClass.toprodtautclass are deprecated.
    See https://gitlab.com/modulispaces/admcycles/-/merge_requests/109 for details.
    Outer graph : [1] [[1]] []
    Vertex 0 :
    Graph :      [1] [[1]] []
    Polynomial : psi_1

    sage: psiclass(1, 1, 1).simplify(1, 1, 1)
    doctest:...: DeprecationWarning: the arguments 'g, n, r'  of TautologicalClass.simplify are deprecated.
    See https://gitlab.com/modulispaces/admcycles/-/merge_requests/109 for details.
    Graph :      [1] [[1]] []
    Polynomial : psi_1

    sage: a = (QQ['x'].gen() * psiclass(1, 1, 1))
    sage: a.coeff_subs(x=1)
    doctest:...: DeprecationWarning: coeff_subs is deprecated. Please use subs instead.
    See https://gitlab.com/modulispaces/admcycles/-/merge_requests/109 for details.
    Graph :      [1] [[1]] []
    Polynomial : psi_1
    sage: a
    Graph :      [1] [[1]] []
    Polynomial : psi_1
"""
