# -*- coding: utf-8 -*-
r"""
Tautological subring of the cohomology ring of the moduli space of curves.
"""

import numbers

from sage.misc.cachefunc import cached_method
from sage.misc.misc_c import prod

from sage.structure.unique_representation import UniqueRepresentation
from sage.structure.richcmp import op_EQ, op_NE
from sage.structure.element import ModuleElement, parent
from sage.structure.all import coercion_model


from sage.categories.functor import Functor
from sage.categories.pushout import ConstructionFunctor
from sage.categories.algebras import Algebras
from sage.categories.rings import Rings

from sage.arith.misc import factorial
from sage.arith.misc import bernoulli
from sage.arith.misc import multinomial
from sage.combinat.partition import Partitions
from sage.combinat.integer_vector import IntegerVectors
from sage.rings.integer_ring import ZZ
from sage.rings.rational_field import QQ
from sage.modules.free_module_element import vector
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.polynomial.term_order import TermOrder
from sage.combinat.integer_vector_weighted import WeightedIntegerVectors
from sage.matrix.constructor import matrix

from .moduli import _moduli_to_str, _str_to_moduli, MODULI_TL, get_moduli, socle_degree
from .admcycles import decstratum
from .stable_graph import StableGraph
from .identify_classes import identify_class

from sage.env import SAGE_VERSION
major, minor = SAGE_VERSION.split('.')[:2]
while not minor[-1].isdigit():
    minor = minor[:-1]
major = int(major)
minor = int(minor)
if (major, minor) >= (10, 5):
    from sage.structure.parent import Parent as AlgebraOrParent
else:
    from sage.rings.ring import Algebra as AlgebraOrParent


_CommutativeRings = Rings().Commutative()


# NOTE: replaces admcycles.tautclass
class TautologicalClass(ModuleElement):
    r"""
    An element of a tautological ring.

    Internally, it is represented by a list ``terms`` of objects of type
    :class:`admcycles.admcycles.decstratum`. Such element should never
    be constructed directly by calling :class:`TautologicalClass`. Instead
    use the parent class :class:`TautologicalRing` or dedicated functions
    as in the examples below

    EXAMPLES::

        sage: from admcycles import *
        sage: R = TautologicalRing(3,1)
        sage: gamma = StableGraph([1,2],[[1,2],[3]],[(2,3)])
        sage: ds1 = R(gamma, kappa=[[1],[]])
        sage: ds1
        Graph :      [1, 2] [[1, 2], [3]] [(2, 3)]
        Polynomial : (kappa_1)_0
        sage: ds2 = R(gamma, kappa=[[],[1]])
        sage: ds2
        Graph :      [1, 2] [[1, 2], [3]] [(2, 3)]
        Polynomial : (kappa_1)_1
        sage: t = ds1 + ds2
        sage: (t - R(gamma) * R.kappa(1)).is_zero()
        True

    Constructing a tautological class from dedicated functions::

        sage: psiclass(1, 2, 1)  # psi_1 on M_{2,1}
        Graph :      [2] [[1]] []
        Polynomial : psi_1
    """

    def __init__(self, parent, terms, clean=True):
        r"""
        INPUT:

        - parent : a class:`TautologicalRing`
        - terms : a list of class:`~admcycles.admcycles.decstratum`
        - clean: boolean (default ``True``)
          whether to apply ``dimension_filter`` and ``consolidate`` on the input
        """
        ModuleElement.__init__(self, parent)

        if isinstance(terms, (tuple, list)):
            self._terms = {}
            for t in terms:
                if not isinstance(t, decstratum):
                    raise TypeError
                if t.gamma.is_mutable():
                    raise ValueError('mutable stable graph in a decstratum when building TautologicalClass')
                if t.gamma.vanishes(parent._moduli):
                    continue
                if clean:
                    t.dimension_filter(parent._moduli)
                    t.consolidate()
                if t.gamma in self._terms:
                    self._terms[t.gamma].poly += t.poly
                    if not self._terms[t.gamma]:
                        del self._terms[t.gamma]
                else:
                    self._terms[t.gamma] = t
        elif isinstance(terms, dict):
            if clean:
                self._terms = {}
                for gamma, term in terms.items():
                    if gamma != term.gamma:
                        raise ValueError
                    if gamma.vanishes(parent._moduli):
                        continue
                    term.dimension_filter(parent._moduli)
                    term.consolidate()
                    if term:
                        if gamma in self._terms:
                            self._terms[gamma] += term
                        else:
                            self._terms[gamma] = term
            else:
                self._terms = terms
        else:
            raise TypeError

    def copy(self):
        P = self.parent()
        return P.element_class(P, {g: t.copy() for g, t in self._terms.items()})

    # TODO: change the name
    # TODO: this should depend on the moduli (though this global check is deactivated in decstratum.dimension_filter)
    def dimension_filter(self):
        for g in list(self._terms):
            self._terms[g].dimension_filter()
            if not self._terms[g]:
                del self._terms[g]

    def _repr_(self):
        if not self._terms:
            return '0'
        return '\n\n'.join(repr(self._terms[g]) for g in sorted(self._terms))

    def _unicode_art_(self):
        r"""
        Return unicode art for the tautological class.

        EXAMPLES::

            sage: from admcycles import *
            sage: D = DR_cycle(1,(2,-2))
            sage: unicode_art(D)
            Graph :
            <BLANKLINE>
            ╭──╮
            │1 │
            ╰┬┬╯
             12
            <BLANKLINE>
            Polynomial : 2*ψ₁ + 2*ψ₂
            Graph :
             ╭╮
             45
            ╭┴┴╮
            │0 │
            ╰┬┬╯
             12
            <BLANKLINE>
            Polynomial : -1/24
        """
        from sage.typeset.unicode_art import unicode_art, UnicodeArt
        if not self._terms:
            return unicode_art('0')
        return prod((self._terms[g]._unicode_art_() for g in sorted(self._terms)), UnicodeArt())

    def is_empty(self):
        return not self._terms

    def is_nilpotent(self):
        r"""
        Return whether this element is nilpotent.

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(1, 1)
            sage: R.one().is_nilpotent()
            False
            sage: R.psi(1).is_nilpotent()
            True
        """
        return self.constant_coefficient().is_nilpotent()

    def is_unit(self):
        r"""
        Return whether this element is a unit.

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(1, 1)
            sage: R.one().is_unit()
            True
            sage: R.psi(1).is_unit()
            False
        """
        return self.constant_coefficient().is_unit()

    def inverse_of_unit(self):
        r"""
        Return the inverse of this element.

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(0, 5)
            sage: (R.one() + R.psi(1)).inverse_of_unit()
            Graph :      [0] [[1, 2, 3, 4, 5]] []
            Polynomial : 1 - psi_1 + psi_1^2
        """
        try:
            from sage.rings.polynomial.misc import inverse_of_unit
        except ImportError:
            # NOTE: this is only in beta versions of sage
            # see https://trac.sagemath.org/ticket/33499
            from .misc import inverse_of_unit
        return inverse_of_unit(self)

    # TODO: shouldn't this be called homogeneous_component?
    def degree_part(self, d):
        r"""
        Return the homogeneous component of degree ``d``.

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(1, 2)
            sage: f = (1 - 2 * R.psi(1) + 3 * R.psi(2)**2)**2
            sage: f.degree_part(0)
            Graph :      [1] [[1, 2]] []
            Polynomial : 1
            sage: f.degree_part(1)
            Graph :      [1] [[1, 2]] []
            Polynomial : -4*psi_1
            sage: f.degree_part(2)
            Graph :      [1] [[1, 2]] []
            Polynomial : 6*psi_2^2 + 4*psi_1^2
        """
        P = self.parent()
        new_terms = {}
        for g, term in self._terms.items():
            term = term.degree_part(d)
            if term:
                new_terms[g] = term
        return P.element_class(P, new_terms)

    def constant_coefficient(self):
        r"""
        Return the coefficient in degree zero as an element in the base ring.

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(2, 1)
            sage: (1/3 - R.psi(1) + R.kappa(2)).constant_coefficient()
            1/3

            sage: A.<x, y> = QQ[]
            sage: R = TautologicalRing(2, 1, base_ring=A)
            sage: f = (1 - x * R.psi(1)) * (1/3 + y * R.kappa(2))
            sage: f.constant_coefficient()
            1/3

        TESTS::

            sage: from admcycles import TautologicalRing, StableGraph
            sage: R = TautologicalRing(3,2)
            sage: Gamma = StableGraph([3],[[2,1]],[]); Gamma
            [3] [[2, 1]] []
            sage: a = R.one() + R(Gamma); a
            Graph :      [3] [[1, 2]] []
            Polynomial : 1
            <BLANKLINE>
            Graph :      [3] [[2, 1]] []
            Polynomial : 1
            sage: a.constant_coefficient()
            2
        """
        return self.fund_evaluate()

    def degree_cap(self, dmax):
        r"""
        Return the class where we drop components of degree above ``dmax``.

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(1, 2)
            sage: f = (1 - 2 * R.psi(1) + 3 * R.psi(2)**2)**2
            sage: f.degree_cap(1)
            Graph :      [1] [[1, 2]] []
            Polynomial : 1 - 4*psi_1
        """
        P = self.parent()
        new_terms = {}
        for g, term in self._terms.items():
            term = term.degree_cap(dmax)
            if term:
                new_terms[g] = term
        return P.element_class(P, new_terms)

    def subs(self, *args, **kwds):
        r"""
        Perform substitution on coefficients.

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: A.<a1, a2> = PolynomialRing(QQ,2)
            sage: R = TautologicalRing(2, 2, base_ring=A)
            sage: t = a1 * R.psi(1) + a2 * R.psi(2)
            sage: t
            Graph :      [2] [[1, 2]] []
            Polynomial : a1*psi_1 + a2*psi_2
            sage: t.subs({a2: 1 - a1})
            Graph :      [2] [[1, 2]] []
            Polynomial : a1*psi_1 + (-a1 + 1)*psi_2
            sage: t
            Graph :      [2] [[1, 2]] []
            Polynomial : a1*psi_1 + a2*psi_2

            sage: t = (a1 - a2) * R.psi(1) + (a1 + a2) * R.psi(2)
            sage: t.subs({a1: a2})
            Graph :      [2] [[1, 2]] []
            Polynomial : 2*a2*psi_2
            sage: t.subs({a1: 0, a2: 0})
            0
            sage: t
            Graph :      [2] [[1, 2]] []
            Polynomial : (a1 - a2)*psi_1 + (a1 + a2)*psi_2
        """
        new_terms = {}
        for g, term in self._terms.items():
            term = term.copy(mutable=False)
            coeffs = term.poly.coeff
            monom = term.poly.monom
            i = 0
            while i < len(coeffs):
                coeffs[i] = coeffs[i].subs(*args, **kwds)
                if not coeffs[i]:
                    coeffs.pop(i)
                    monom.pop(i)
                else:
                    i += 1
            if i:
                new_terms[g] = term
        P = self.parent()
        return P.element_class(P, new_terms)

    # TODO: change the name, maybe simplify_full?
    # TODO: the argument r is very bad as it mutates the tautological class
    def FZsimplify(self, r=None):
        r"""
        Return representation of self as a tautclass formed by a linear combination of
        the preferred tautological basis.

        If ``r`` is given, only take degree r part.

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(0, 4)
            sage: t = 7 + R.psi(1) + 3 * R.psi(2) - R.psi(3)
            sage: t.FZsimplify()
            Graph :      [0] [[1, 2, 3, 4]] []
            Polynomial : 7 + 3*(kappa_1)_0

            sage: t.FZsimplify(r=0)
            Graph :      [0] [[1, 2, 3, 4]] []
            Polynomial : 7
        """
        if self.is_empty():
            return self

        R = self.parent()
        if r is not None:
            return R.from_basis_vector(self.basis_vector(r), r)
        else:
            result = R.zero()
            for r in self.degree_list():
                result += R.from_basis_vector(self.basis_vector(r), r)
            return result

    # TODO: change the name?
    def toprodtautclass(self, g=None, n=None):
        P = self.parent()
        if g is not None or n is not None:
            from .superseded import deprecation
            deprecation(109, "the arguments 'g' and 'n' of TautologicalClass.toprodtautclass are deprecated.")
            if (g is not None and g != P._g) or (n is not None and n != P._n):
                raise ValueError('invalid (g,n) (got ({},{}) instead of ({},{}))'.format(g, n, P._g, P._n))

        from .admcycles import prodtautclass
        return prodtautclass(P.trivial_graph(), [[t.copy()] for t in self._terms.values()])

    # TODO: the method tautclass.simplify used to have more arguments simplify(self,g=None,n=None,r=None)
    # TODO: should we really deprecate the argument r? (one can always do degree_cap followed by a simplify)
    def simplify(self, g=None, n=None, r=None):
        r"""
        Simplifies self by combining terms with same tautological generator, returns self.

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(2, 1)
            sage: t = R.psi(1) + 11*R.psi(1)
            sage: t
            Graph :      [2] [[1]] []
            Polynomial : 12*psi_1
            sage: t.simplify()
            Graph :      [2] [[1]] []
            Polynomial : 12*psi_1
        """
        P = self.parent()
        if g is not None or n is not None or r is not None:
            from .superseded import deprecation
            deprecation(109, "the arguments 'g, n, r'  of TautologicalClass.simplify are deprecated.")
        if r is not None:
            D = [r]
        else:
            D = self.degree_list()

        if self.is_empty():
            # TODO: if elements were immutable we could return self
            return self.copy()
        result = P.zero()
        for d in D:
            result += P.from_vector(self.vector(d), d)
        self._terms = result._terms
        return self

    def simplified(self, g=None, n=None, r=None):
        r"""
        Return a simplified version of self by combining terms with same tautological generator.
        """
        P = self.parent()
        if g is not None or n is not None:
            from .superseded import deprecation
            deprecation(109, "the arguments 'g' and 'n' of TautologicalClass.simplified are deprecated.")
            if (g is not None and g != P._g) or (n is not None and n != P._n):
                raise ValueError('invalid g,n (got ({},{}) instead of ({},{}))'.format(g, n, P._g, P._n))
        if self.is_empty():
            # TODO: if elements were immutable we could return self
            return self.copy()
        if r is not None:
            return P.from_vector(self.vector(r), r)
        self.simplify()
        return self

    def __neg__(self):
        if self.is_empty():
            # TODO: if elements were immutable we could return self
            return self.copy()
        P = self.parent()
        return P.element_class(P, {g: -term for g, term in self._terms.items()}, clean=False)

    def _add_(self, other):
        r"""
        TESTS::

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(1, 1)
            sage: R(1) + 1
            Graph :      [1] [[1]] []
            Polynomial : 2
            sage: 1 + R(1)
            Graph :      [1] [[1]] []
            Polynomial : 2
        """
        if self.is_empty():
            # TODO: if elements were immutable we could return other
            return other.copy()
        if other.is_empty():
            # TODO: if elements were immutable we could return self
            return self.copy()
        P = self.parent()
        new_terms = {g: t.copy() for g, t in self._terms.items()}
        for g, term in other._terms.items():
            if g in new_terms:
                new_terms[g].poly += term.poly
                if not new_terms[g]:
                    del new_terms[g]
            else:
                new_terms[g] = term
        return P.element_class(P, new_terms, clean=False)

    def _lmul_(self, other):
        r"""
        Scalar multiplication by ``other``.

        TESTS::

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(2, 2)
            sage: -3/5 * R.psi(1)
            Graph :      [2] [[1, 2]] []
            Polynomial : -3/5*psi_1
            sage: 0 * R.psi(1) == 1 * R.zero() == R.zero()
            True
            sage: assert (0 * R.psi(1)).parent() is R
            sage: assert (1 * R.zero()).parent() is R
        """
        P = self.parent()
        assert parent(other) is self.base_ring()
        if other.is_zero():
            return P.zero()
        elif other.is_one():
            # TODO: if elements were immutable we could return self
            return self.copy()
        new_terms = {g: other * term for g, term in self._terms.items()}
        return P.element_class(P, new_terms, clean=False)

    def _mul_(self, other):
        r"""
        TESTS::

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(2, 2)
            sage: R.psi(1) * R.psi(2)
            Graph :      [2] [[1, 2]] []
            Polynomial : psi_1*psi_2

            sage: R.generators(1)[3] * R.generators(2)[23]
            Graph :      [0, 1, 1] [[1, 2, 4], [5, 6], [7]] [(4, 5), (6, 7)]
            Polynomial : (kappa_1)_2

            sage: (R.zero() * R.one()) == (R.one() * R.zero()) == R.zero()
            True
            sage: R.one() * R.one() == R.one()
            True

        Multiplication with non-standard markings::

            sage: from admcycles import StableGraph
            sage: R2 = TautologicalRing(1, [4, 7])
            sage: g2 = StableGraph([0], [[1,2,4,7]], [(1,2)])
            sage: R2(g2) * (1 + R2.psi(4)) * (1 + R2.psi(7))
            Graph :      [0] [[1, 2, 4, 7]] [(1, 2)]
            Polynomial : 1 + psi_7 + psi_4
        """
        if self.is_empty() or other.is_empty():
            return self.parent().zero()
        P = self.parent()
        if P._markings and P._markings[-1] != P._n:
            # TODO: maybe we want something more efficient for non-standard markings?
            dic_to_std = {j: i + 1 for i, j in enumerate(P._markings)}
            dic_from_std = {i + 1: j for i, j in enumerate(P._markings)}
            return (self.rename_legs(dic_to_std, inplace=False) * other.rename_legs(dic_to_std, inplace=False)).rename_legs(dic_from_std, inplace=False)

        new_terms = {}
        for t1 in self._terms.values():
            for t2 in other._terms.values():
                for g, term in t1.multiply(t2, P)._terms.items():
                    if g.vanishes(P._moduli):
                        continue
                    term.dimension_filter(moduli=P._moduli)
                    term.poly.consolidate(force=False)
                    if term:
                        if g in new_terms:
                            new_terms[g].poly += term.poly
                        else:
                            new_terms[g] = term
        for g in list(new_terms):
            if not new_terms[g]:
                del new_terms[g]
        return P.element_class(P, new_terms, clean=False)

    def exp(self, dmax=None):
        r"""
        Return the exponential of this tautological class up to degree dmax.

        The exponential is defined as ``exp(x) = 1 + x + 1/2*x^2 + ... ``.
        It is well defined as long as ``x`` has no degree zero term.

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(1, 2)
            sage: R.psi(1).exp()
            Graph :      [1] [[1, 2]] []
            Polynomial : 1 + psi_1 + 1/2*psi_1^2

        TESTS::

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(0, 3)
            sage: R.zero().exp() == R.one()
            True
        """
        if self.vector(0):
            raise ValueError('non-zero degree zero term')
        P = self.parent()
        f = P.one()
        if dmax is None:
            dmax = P.socle_degree()
        if dmax == 0:
            return f
        result = f + self
        y = self
        for k in range(2, dmax + 1):
            y = y * self
            result += QQ((1, factorial(k))) * y
        return result

    # TODO: full support for all moduli
    def evaluate(self, moduli=None):
        r"""
        Computes integral against the fundamental class of the corresponding moduli space,
        e.g. the degree of the zero-cycle part of the tautological class (for moduli='st').

        For non-standard moduli, this computes the socle-evaluation, which is given by
        the integral against

            * lambda_g for moduli='ct'
            * lambda_g * lambda_{g-1} for moduli='rt' (and moduli='sm' for n=0)

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(1, 1)
            sage: R.kappa(1).evaluate()
            1/24

        Some non-standard moduli::

            sage: from admcycles import *
            sage: R = TautologicalRing(2,1,moduli='ct')
            sage: R.kappa(2).evaluate()
            7/5760
            sage: (kappaclass(2,2,1)*lambdaclass(2,2,1)).evaluate()
            7/5760
            sage: R.kappa(2).evaluate(moduli='st') # wrong degree
            0

        TESTS::

            sage: R = TautologicalRing(2,1,moduli='ct')
            sage: Rst = TautologicalRing(2,1)
            sage: L = lambdaclass(2,2,1)
            sage: all((Rst(t)*L).evaluate() == t.evaluate() for t in R.generators(2))
            True
            sage: R = TautologicalRing(2,2,moduli='rt')
            sage: Rst = TautologicalRing(2,2)
            sage: LL = Rst.lambdaclass(2)*Rst.lambdaclass(1)
            sage: all((Rst(t)*LL).evaluate() == t.evaluate() for t in R.generators(2))
            True
        """
        P = self.parent()
        if moduli is None:
            moduli = _moduli_to_str[P._moduli]
        if moduli == 'tl':
            raise ValueError('no well-defined socle evaluation for space of treelike curves')
        if P._moduli != get_moduli(moduli):
            R = TautologicalRing(P._g, P._markings, base_ring=P.base_ring(), moduli=moduli)
            return R(self).evaluate()
        return sum((t.evaluate(moduli=moduli) for t in self._terms.values()), P.base_ring().zero())

    # TODO: change the name
    def fund_evaluate(self):
        r"""
        Computes degree zero part of the class as multiple of the fundamental class.

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(2, 1)
            sage: t = R.psi(1)
            sage: s = t.forgetful_pushforward([1])
            sage: s
            Graph :      [2] [[]] []
            Polynomial : 2
            sage: s.fund_evaluate()
            2
        """
        return self.vector(0)[0]

    def _richcmp_(self, other, op):
        r"""
        Implementation of comparisons (``==`` and ``!=``).

        TESTS::

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(2,2)
            sage: R.zero() == R.zero()
            True
            sage: R.zero() == R.psi(1)
            False
            sage: R.psi(1) == R.zero()
            False
            sage: R.psi(1) == R.psi(1)
            True
            sage: R.psi(1) == R.psi(2)
            False

            sage: R.zero() != R.zero()
            False
            sage: R.zero() != R.psi(1)
            True
            sage: R.psi(1) != R.zero()
            True
            sage: R.psi(1) != R.psi(1)
            False
            sage: R.psi(1) != R.psi(2)
            True
            sage: R = TautologicalRing(1,1)
            sage: A = R(1) + R.psi(1) - R.kappa(1)
            sage: A == R.zero()
            False
            sage: A == R.one()
            True
        """
        if op != op_EQ and op != op_NE:
            raise TypeError('incomparable')

        # TODO: is there a smarter choice of ordering?
        D = set(self.degree_list())
        D.update(other.degree_list())
        D = sorted(D)

        # NOTE: .vector(d) is much cheaper than .basis_vector(d) so we do that first
        equal = all((self.vector(d) == other.vector(d) or self.basis_vector(d) == other.basis_vector(d)) for d in D)
        return equal == (op == op_EQ)

    def __bool__(self):
        r"""
        TESTS::

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(1, 1)
            sage: bool(R.psi(1))
            True
            sage: bool(R.zero())
            False
        """
        # NOTE: .vector(d) is much cheaper than .basis_vector(d) so we do that first
        return not all(self.vector(d).is_zero() or self.basis_vector(d).is_zero() for d in self.degree_list())

    def is_zero(self, moduli=None):
        r"""
        Return whether this class is a known tautological relation (using
        Pixton's implementation of the generalized Faber-Zagier relations).

        If optional argument `moduli` is given, it checks the vanishing on
        an open subset of the current moduli of stable curves.

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(3, 0)
            sage: diff = R.kappa(1) - 12 * R.lambdaclass(1)
            sage: diff.is_zero()
            False

            sage: S = TautologicalRing(3, 0, moduli='sm')
            sage: S(diff).is_zero()
            True
            sage: diff.is_zero(moduli='sm')
            True
            sage: S(diff).is_zero(moduli='st')
            Traceback (most recent call last):
            ...
            ValueError: moduli='st' is larger than the moduli 'sm' of the parent
        """
        P = self.parent()
        moduli = get_moduli(moduli, P._moduli)
        if moduli > P._moduli:
            raise ValueError("moduli={!r} is larger than the moduli {!r} of the parent".format(
                _moduli_to_str[moduli], _moduli_to_str[P._moduli]))
        if moduli != P._moduli:
            R = TautologicalRing(P._g, P._markings, moduli, base_ring=P.base_ring())
            return not R(self)
        else:
            return not self

    def degree_list(self):
        r"""
        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(2, 3)
            sage: R.psi(1).degree_list()
            [1]
            sage: (1 + R.psi(1)**2).degree_list()
            [0, 2]
            sage: ((1 + R.psi(1))**2).degree_list()
            [0, 1, 2]
        """
        return sorted({d for t in self._terms.values() for g, n, d in t.gnr_list()})

    def forgetful_pullback(self, forget=None):
        r"""
        Return the pullback of this tautological class under a forgetful map
        `\bar M_{g, n'} --> \bar M_{g,n}`

        INPUT:

        forget : list of integers
          legs that are forgotten by the map forgetful map

        EXAMPLES::

            sage: from admcycles import TautologicalRing

            sage: R = TautologicalRing(1, 2)
            sage: b = R.psi(2).forgetful_pullback(1)
            sage: b
            Graph :      [1] [[1, 2, 3]] []
            Polynomial : psi_2
            <BLANKLINE>
            Graph :      [1, 0] [[1, 4], [2, 3, 5]] [(4, 5)]
            Polynomial : -1
            sage: b.parent()
            TautologicalRing(g=1, n=3, moduli='st') over Rational Field

            sage: R = TautologicalRing(1, [2, 3])
            sage: b = R.psi(2).forgetful_pullback([1])
            sage: b
            Graph :      [1] [[1, 2, 3]] []
            Polynomial : psi_2
            <BLANKLINE>
            Graph :      [1, 0] [[3, 4], [1, 2, 5]] [(4, 5)]
            Polynomial : -1
            sage: b.parent()
            TautologicalRing(g=1, n=3, moduli='st') over Rational Field
        """
        P = self.parent()
        if forget is None:
            # TODO: if elements were immutable we could return self (here and below)
            return self.copy()
        elif isinstance(forget, numbers.Integral):
            k = ZZ(forget)
            if k == 0:
                return self.copy()
            if k < 0:
                raise ValueError("forget can only be non-negative")
            if P._markings != tuple(range(1, P._n + 1)):
                raise ValueError("integers as forget only allowed if the markings are 1,..,n, got forget={} inside {}".format(forget, P))
            markings = tuple(range(1, P._n + k + 1))
            forget = tuple(range(P._n + 1, P._n + k + 1))
        elif isinstance(forget, (tuple, list)):
            if not forget:
                return self.copy()
            markings = sorted(set(forget).union(P._markings))
            if len(markings) != P._n + len(forget):
                raise ValueError('can only forget non-existent markings, got forget={} inside {}'.format(forget, P))

        R = TautologicalRing(P._g, markings, moduli=P._moduli, base_ring=P.base_ring())
        return sum((R.element_class(R, c.forgetful_pullback_list(forget)) for c in self._terms.values()), R.zero())

    def forgetful_pushforward(self, forget=None):
        r"""
        Return the pushforward of a given tautological class under a forgetful
        map `\bar M_{g,n} \to \bar M_{g,n'}`.

        INPUT:

        forget : list of integers
          legs that are forgotten by the map forgetful map

        EXAMPLES::

            sage: from admcycles import TautologicalRing

            sage: R = TautologicalRing(1, 3)
            sage: s1 = R.psi(3)^2
            sage: s1.forgetful_pushforward([3])
            Graph :      [1] [[1, 2]] []
            Polynomial : (kappa_1)_0
            sage: s1.forgetful_pushforward([2,3])
            Graph :      [1] [[1]] []
            Polynomial : 1

            sage: R = TautologicalRing(1, [2, 5, 6])
            sage: s1 = R.psi(5)^2
            sage: s1.forgetful_pushforward([5])
            Graph :      [1] [[2, 6]] []
            Polynomial : (kappa_1)_0
            sage: s1.forgetful_pushforward([5]).parent()
            TautologicalRing(g=1, n=(2, 6), moduli='st') over Rational Field

            sage: R = TautologicalRing(2, 2)
            sage: gens1 = R.generators(1)
            sage: t = gens1[1] + 2*gens1[3]
            sage: t.forgetful_pushforward([2])
            Graph :      [2] [[1]] []
            Polynomial : 3
            sage: t.forgetful_pushforward([2]).parent()
            TautologicalRing(g=2, n=1, moduli='st') over Rational Field

        TESTS::

            sage: from admcycles import TautologicalRing
            sage: TautologicalRing(1, [2, 4]).psi(4).forgetful_pushforward([5])
            Traceback (most recent call last):
            ...
            ValueError: invalid marking 5 in forget
            sage: TautologicalRing(1, [2, 4]).psi(4).forgetful_pushforward(2)
            Traceback (most recent call last):
            ...
            ValueError: unstable pair (g,n) = (1, 0)
            sage: TautologicalRing(1, [2, 4]).psi(4).forgetful_pushforward(3)
            Traceback (most recent call last):
            ...
            ValueError: forget must be between 0 and the number of markings
        """
        P = self.parent()
        if forget is None:
            # TODO: if elements were immutable we could return self
            return self.copy()
        elif isinstance(forget, numbers.Integral):
            k = ZZ(forget)
            if k < 0 or k > P._n:
                raise ValueError("forget must be between 0 and the number of markings")
            if k == 0:
                return self
            forget = P._markings[-k:]
        elif isinstance(forget, (tuple, list)):
            k = ZZ(len(forget))
            forget = sorted(forget)
            for i in range(len(forget) - 1):
                if forget[i] == forget[i + 1]:
                    raise ValueError('multiple marking {} in forget'.format(forget[i]))
            for i in forget:
                if i not in P._markings:
                    raise ValueError('invalid marking {} in forget'.format(i))
        else:
            raise TypeError('invalid input forget')

        if k == 0:
            return self

        new_markings = [i for i in P._markings if i not in forget]
        R = TautologicalRing(P._g, new_markings, moduli=P._moduli, base_ring=P.base_ring())
        return R.element_class(R, [term.forgetful_pushforward(forget) for term in self._terms.values()])

    # TODO: we should not do inplace operation if there is no support for mutable/immutable
    # (this needs some cleaning on the StableGraph side as well)
    # TODO: should it really be called rename_legs? it is a bit misleading are we are just
    # relabelling the markings in this function (same in decstratum and StableGraph)
    def rename_legs(self, dic, rename=None, inplace=True):
        r"""
        Rename the legs according to the dictionary ``dic``.

        EXAMPLES::

            sage: from admcycles import TautologicalRing

            sage: R = TautologicalRing(1, 2)
            sage: cl = R.psi(1) * R.psi(2)
            sage: cl.rename_legs({2:5}, inplace=False)
            Graph :      [1] [[1, 5]] []
            Polynomial : psi_1*psi_5
            sage: parent(cl.rename_legs({2:5}, inplace=False))
            TautologicalRing(g=1, n=(1, 5), moduli='st') over Rational Field

        Note that inplace operation is forbidden if the relabellings of the markings
        is not a bijection::

            sage: _ = cl.rename_legs({2:5}, inplace=True)
            Traceback (most recent call last):
            ...
            ValueError: invalid inplace operation: change of markings (1, 2) -> (1, 5)

        TESTS::

            sage: from admcycles import *
            sage: G1 = StableGraph([1,1],[[1,2,4],[3,5]],[(4,5)])
            sage: A = G1.to_tautological_class()
            sage: _ = A.rename_legs({1:3,3:1})
            sage: list(A._terms)
            [[1, 1] [[2, 3, 4], [1, 5]] [(4, 5)]]
            sage: for g, t in A._terms.items():
            ....:     assert g == t.gamma
        """
        if rename is not None:
            from .superseded import deprecation
            deprecation(109, 'the rename keyword in TautologicalClass.rename_legs is deprecated. Please set rename=None')

        P = self.parent()
        clean_dic = {i: dic.get(i, i) for i in P._markings}
        new_markings = tuple(sorted(clean_dic.values()))
        if new_markings != P._markings:
            if inplace:
                raise ValueError(
                    'invalid inplace operation: change of markings {} -> {}'.format(P._markings, new_markings))
            R = TautologicalRing(P._g, new_markings, P._moduli, base_ring=P.base_ring())
        else:
            R = P

        if inplace:
            l = list(self._terms.values())
            self._terms.clear()
            for t in l:
                t.rename_legs(dic, inplace=True)
                self._terms[t.gamma] = t
            return self
        else:
            return R([t.rename_legs(dic, inplace=False) for t in self._terms.values()])

    def permutation_action(self, g):
        r"""
        Applies the permutation ``g`` to the markings.

        INPUT:

         g: permutation in the symmetric group `S_n`

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(1, 2)
            sage: G = SymmetricGroup(2)
            sage: g = G('(1,2)')
            sage: R.psi(1).permutation_action(g) == R.psi(2)
            True
        """
        return self.rename_legs(g.dict(), inplace=False)

    def is_symmetric(self, G=None):
        r"""
        Return whether this tautological class is symmetric under the action of G.

        INPUT:

        G: (optional) subgroup of symmetric group
        if no argument is given take Sn

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(1, 2)
            sage: (R.psi(1) * R.psi(2)).is_symmetric()
            True
            sage: R.psi(1).is_symmetric()  # psi(1) = psi(2) in H^*(M_{1,2})
            True

            sage: R = TautologicalRing(2, 2)
            sage: R.psi(1).is_symmetric()
            False

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(2, 3)
            sage: G = PermutationGroup([(1,2)])
            sage: a = R.psi(1) + R.psi(2)
            sage: a.is_symmetric(G)
            True
            sage: a.is_symmetric()
            False
        """
        if not self._terms:  # if tautclass is 0, return True
            return True
        num_leg = self.parent()._n
        if G is None:
            from sage.groups.perm_gps.permgroup_named import SymmetricGroup
            G = SymmetricGroup(num_leg)
        for g in G.gens():
            if self.permutation_action(g) != self:
                return False
        return True

    def symmetrize(self, G=None):
        r"""
        Return the symmetrization of self under the action of ``G``.

        INPUT:

        G: (optional) subgroup of symmetric group
        if no argument is given take Sn

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(2, 2)
            sage: R.psi(1).symmetrize()
            Graph :      [2] [[1, 2]] []
            Polynomial : 1/2*psi_1 + 1/2*psi_2
        """
        P = self.parent()
        res = P.zero()
        if not self._terms:  # if tautclass is 0, return 0
            return res
        if G is None:
            from sage.groups.perm_gps.permgroup_named import SymmetricGroup
            G = SymmetricGroup(P._n)

        return P.sum(self.permutation_action(g) for g in G) / G.cardinality()

    def standard_markings(self):
        r"""
        Return an isomorphic tautological class where standard markings `{1, 2, ..., n}`
        are used.

        EXAMPLES::

            sage: from admcycles import StableGraph, TautologicalRing
            sage: R = TautologicalRing(4, [4,7])
            sage: g = StableGraph([3], [[4,7,1,2]], [(1,2)])
            sage: a = R(g, psi={4:1}) + R(g, psi={7:2}) + R(g, kappa=[[0,0,1]])
            sage: a.standard_markings()
            Graph :      [3] [[1, 2, 4, 7]] [(4, 7)]
            Polynomial : psi_1 + psi_2^2 + (kappa_3)_0
            sage: a.standard_markings().parent()
            TautologicalRing(g=4, n=2, moduli='st') over Rational Field
        """
        P = self.parent()
        if P._markings and P._markings[-1] == P._n:
            return self
        return self.rename_legs({j: i + 1 for i, j in enumerate(P._markings)}, inplace=False)

    def vector(self, r=None):
        r"""
        EXAMPLES:

        We consider the special case of the moduli space ``g=1`` and ``n=2``::

            sage: from admcycles import TautologicalRing, StableGraph
            sage: R = TautologicalRing(1, 2)

        Degree zero::

            sage: R(2/3).vector()
            (2/3)
            sage: R.from_vector([2/3], 0)
            Graph :      [1] [[1, 2]] []
            Polynomial : 2/3

        Degree one examples::

            sage: kappa1 = R.kappa(1)
            sage: kappa1.vector()
            (1, 0, 0, 0, 0)
            sage: R.from_vector([1,0,0,0,0], 1)
            Graph :      [1] [[1, 2]] []
            Polynomial : (kappa_1)_0

            sage: psi1 = R.psi(1)
            sage: psi1.vector()
            (0, 1, 0, 0, 0)
            sage: gamma2 = StableGraph([0], [[1,2,3,4]], [(3,4)])
            sage: R(gamma2).vector()
            (0, 0, 0, 0, 1)

        Some degree two examples::

            sage: kappa2 = R.kappa(2)
            sage: kappa2.vector()
            (1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
            sage: (kappa1*psi1).vector()
            (0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
            sage: R(gamma2, kappa=[[1],[]]).vector()
            (0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0)
            sage: gamma3 = StableGraph([0,0], [[1,2,3],[4,5,6]], [(3,4),(5,6)])
            sage: R(gamma3).vector()
            (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0)

        Empty class::

            sage: R(0).vector(1)
            (0, 0, 0, 0, 0)

        Non-standard markings::

            sage: R = TautologicalRing(1, [4, 7])
            sage: R.psi(4).vector()
            (0, 1, 0, 0, 0)
            sage: R.from_vector((0, 1, 0, 0, 0), 1)
            Graph :      [1] [[4, 7]] []
            Polynomial : psi_4

            sage: TautologicalRing(1, 1).zero().vector()
            Traceback (most recent call last):
            ...
            ValueError: specify degree to obtain vector of empty class

        TESTS:

        Non-standard moduli::

            sage: R = TautologicalRing(2,2,moduli='ct')
            sage: all(u.vector() == vector(QQ,23,{i:1}) for i,u in enumerate(R.generators(2)))
            True
        """
        self = self.standard_markings()
        P = self.parent()
        if self.is_empty():
            if r is None:
                raise ValueError('specify degree to obtain vector of empty class')
            return vector(QQ, P.num_gens(r))
        if r is None:
            # assume it is homogeneous
            r = self.degree_list()
            if len(r) != 1:
                raise ValueError('for non-homogeneous term, set r to the desired degree')
            r = r[0]
        from .admcycles import converttoTautvect
        return sum(converttoTautvect(term, P._g, P._n, r, P._moduli) for term in self._terms.values())

    def basis_vector(self, r=None, moduli=None):
        r"""
        Return a vector expressing the class in the basis of the tautological ring.

        The corresponding basis is obtained from
        :meth:~`TautologicalRing.basis`.

        EXAMPLES::

            sage: from admcycles import TautologicalRing, StableGraph
            sage: R = TautologicalRing(2, 1)
            sage: gamma = StableGraph([1],[[1,2,3]],[(2,3)])
            sage: b = R(gamma)
            sage: b.basis_vector()
            (10, -10, -14)

            sage: R.from_basis_vector((10, -10, -14), 1) == b
            True

            sage: Rct = TautologicalRing(2, 1, moduli='ct')
            sage: Rct(b).basis_vector(1)
            (0, 0)
            sage: Rct(b).basis_vector(1,moduli='tl')
            Traceback (most recent call last):
            ...
            ValueError: moduli='tl' is larger than the moduli 'ct' of the parent

            sage: R = TautologicalRing(2, 2)
            sage: c = R.psi(1)**2
            sage: for moduli in ('st', 'tl', 'ct', 'rt'):
            ....:     Rmod = TautologicalRing(2, 2, moduli=moduli)
            ....:     print(Rmod(c).basis_vector())
            (0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0)
            (0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0)
            (5/6, -1/6, 1/3, 0, 0)
            (1)
            sage: Rsm = TautologicalRing(2, 2, moduli='sm')
            sage: Rsm(c).basis_vector(2)
            ()

        Compatibility test with non-standard markings::

            sage: R1 = TautologicalRing(1, 2)
            sage: g1 = StableGraph([0], [[1,2,3,4]], [(3,4)])
            sage: a1 = R1(g1, psi={1:1}) + R1(g1, psi={2:2}) + R1(g1, kappa=[[0,0,1]])

            sage: R2 = TautologicalRing(1, [4,7])
            sage: g2 = StableGraph([0], [[4,7,1,2]], [(1,2)])
            sage: a2 = R2(g2, psi={4:1}) + R2(g2, psi={7:2}) + R2(g2, kappa=[[0,0,1]])

            sage: a1.basis_vector(0) == a2.basis_vector(0)
            True
            sage: a1.basis_vector(1) == a2.basis_vector(1)
            True
            sage: a1.basis_vector(2) == a2.basis_vector(2)
            True
            sage: a1.basis_vector(3) == a2.basis_vector(3)
            True
        """
        self = self.standard_markings()
        P = self.parent()
        moduli = get_moduli(moduli, P._moduli)
        if moduli > P._moduli:
            raise ValueError("moduli={!r} is larger than the moduli {!r} of the parent".format(
                _moduli_to_str[moduli], _moduli_to_str[P._moduli]))

        if r is None:
            r = self.degree_list()
            if len(r) != 1:
                raise ValueError('for non-homogeneous term, set r to the desired degree')
            r = r[0]

        if moduli != P._moduli:
            P = self.parent()
            R = TautologicalRing(P._g, P._markings, moduli, base_ring=P.base_ring())
            return R(self).basis_vector(r)

        P = self.parent()
        from .admcycles import Tautvecttobasis
        # TODO: Tautvecttobasis uses the 'string' version of moduli
        return Tautvecttobasis(self.vector(r), P._g, P._n, r, _moduli_to_str[P._moduli])

    ###########################################################################
    # Deprecated methods from the former tautclass                            #
    # See https://gitlab.com/modulispaces/admcycles/-/merge_requests/109      #
    ###########################################################################
    def toTautvect(self, g=None, n=None, r=None):
        from .superseded import deprecation
        deprecation(109, 'toTautvect is deprecated. Please use vector instead.')
        P = self.parent()
        if (g is not None and g != P._g) or (n is not None and n != P._n):
            raise ValueError('invalid g,n')
        return self.vector(r)

    def toTautbasis(self, g=None, n=None, r=None, moduli='st'):
        from .superseded import deprecation
        deprecation(109, 'toTautbasis is deprecated. Please use basis_vector instead.')
        P = self.parent()
        if (g is not None and g != P._g) or (n is not None and n != P._n):
            raise ValueError('invalid g,n')
        if _str_to_moduli[moduli] != P._moduli:
            P = TautologicalRing(P._g, P._n, moduli, base_ring=P.base_ring())
            self = P(self)
        return self.basis_vector(r)

    def gnr_list(self):
        from .superseded import deprecation
        deprecation(109, 'gnr_list is deprecated. Please use degree_list instead.')
        P = self.parent()
        return [(P._g, P._n, d) for d in self.degree_list()]

    def coeff_subs(self, *args, **kwds):
        from .superseded import deprecation
        deprecation(109, "coeff_subs is deprecated. Please use subs instead.")
        result = self.subs(*args, **kwds)
        self._terms = result._terms
        return self


class TautologicalRing(UniqueRepresentation, AlgebraOrParent):
    r"""
    The tautological subgring of the (even degree) cohomology of the moduli space of curves.

    EXAMPLES::

        sage: from admcycles import TautologicalRing
        sage: TautologicalRing(2)
        TautologicalRing(g=2, n=0, moduli='st') over Rational Field
        sage: TautologicalRing(1, 2)
        TautologicalRing(g=1, n=2, moduli='st') over Rational Field
        sage: TautologicalRing(1, 1, 'tl')
        TautologicalRing(g=1, n=1, moduli='tl') over Rational Field

        sage: from admcycles.moduli import MODULI_ST
        sage: TautologicalRing(0, 5, MODULI_ST, QQ)
        TautologicalRing(g=0, n=5, moduli='st') over Rational Field

    Since tautological rings are commutative algebras one can use them as basic building
    blocks of further algebraic constructors in SageMath::

        sage: R = TautologicalRing(2, 0)

        sage: Rxy.<x,y> = PolynomialRing(R, ['x', 'y'])
        sage: Rxy
        Multivariate Polynomial Ring in x, y over TautologicalRing(g=2, n=0, moduli='st') over Rational Field
        sage: R.kappa(1) * x + R.kappa(2) * y  # TODO: horrible display
        (Graph :      [2] [[]] []
        Polynomial : (kappa_1)_0)*x + (Graph :      [2] [[]] []
        Polynomial : (kappa_2)_0)*y

        sage: V = FreeModule(R, 2)
        sage: V
        Ambient free module of rank 2 over TautologicalRing(g=2, n=0, moduli='st') over Rational Field
        sage: V((R.kappa(1), R.kappa(2)))  # TODO: horrible display
        (Graph :      [2] [[]] []
        Polynomial : (kappa_1)_0, Graph :      [2] [[]] []
        Polynomial : (kappa_2)_0)

    TESTS::

        sage: from admcycles import TautologicalRing
        sage: TestSuite(TautologicalRing(1, 1)).run()
        sage: TestSuite(TautologicalRing(1, [3])).run()
        sage: TestSuite(TautologicalRing(1, 1, 'tl', QQ['x,y'])).run()

        sage: cm = get_coercion_model()
        sage: cm.get_action(QQ, TautologicalRing(2,0))
        Left scalar multiplication by Rational Field on TautologicalRing(g=2, n=0, moduli='st') over Rational Field

    Test for https://gitlab.com/modulispaces/admcycles/-/issues/70::

        sage: from admcycles import TautologicalRing
        sage: W = TautologicalRing(1,1)
        sage: V = PolynomialRing(W, 'x,y')
        sage: V.one()
        Graph :      [1] [[1]] []
        Polynomial : 1

    Test for https://gitlab.com/modulispaces/admcycles/-/issues/79::

        sage: from admcycles import TautologicalRing
        sage: TautologicalRing(2, 0).gens()
        (...)
    """

    Element = TautologicalClass

    @staticmethod
    def __classcall__(cls, *args, **kwds):
        g = kwds.pop('g', None)
        n = kwds.pop('n', None)
        moduli = kwds.pop('moduli', None)
        base_ring = kwds.pop('base_ring', None)
        if kwds:
            raise ValueError('unknown arguments {}'.format(list(kwds.keys())))
        if len(args) >= 1:
            if g is not None:
                raise ValueError('genus g specified twice')
            g = args[0]
        if len(args) >= 2:
            # g and n
            if n is not None:
                raise ValueError('number of marked points n specified twice')
            n = args[1]
        if len(args) >= 3:
            if moduli is not None:
                raise ValueError('moduli specified twice')
            moduli = args[2]
        if len(args) >= 4:
            if base_ring is not None:
                raise ValueError('base_ring specified twice')
            base_ring = args[3]
        if len(args) > 4:
            raise ValueError('too many arguments for TautologicalRing: {}'.format(args))

        moduli = get_moduli(moduli)

        if not isinstance(g, numbers.Integral) or g < 0:
            raise ValueError('g must be a non-negative integer')
        g = ZZ(g)
        if n is None:
            n = ZZ.zero()
            markings = ()
        elif isinstance(n, (tuple, list)):
            markings = [ZZ(i) for i in sorted(n)]
            n = len(markings)
            markings.sort()
            if markings and markings[0] <= 0:
                raise ValueError('markings must be positive integers')
            if any(markings[i] == markings[i + 1] for i in range(n - 1)):
                raise ValueError('repeated marking')
            markings = tuple(markings)
        elif isinstance(n, numbers.Integral):
            if n < 0:
                raise ValueError('n must be a non-negative integer')
            n = ZZ(n)
            markings = tuple(range(1, n + 1))
        else:
            raise TypeError('invalid input')

        if base_ring is None:
            base_ring = QQ
        elif base_ring not in _CommutativeRings:
            raise ValueError('base_ring (={}) must be a commutative ring'.format(base_ring))

        if (g, n) in [(0, 0), (0, 1), (0, 2), (1, 0)]:
            raise ValueError('unstable pair (g,n) = ({}, {})'.format(g, n))

        return super().__classcall__(cls, g, markings, moduli, base_ring)

    def __init__(self, g, markings, moduli, base_ring):
        r"""
        INPUT:

        g : integer
          genus
        markings : tuple of distinct positive integers
          list of markings
        moduli : integer
          code for the moduli
        base_ring : ring
          base ring
        """
        AlgebraOrParent.__init__(self, base_ring, category=Algebras(base_ring).Commutative().FiniteDimensional())
        self._g = g
        self._markings = markings
        self._n = len(markings)
        self._moduli = moduli

    # NOTE: even though the category contains the axiom Commutative(), is_commutative is reimplemented in sage.rings.ring.Ring
    # see https://gitlab.com/modulispaces/admcycles/-/issues/70
    # see https://trac.sagemath.org/ticket/32810
    def is_commutative(self):
        return True

    @cached_method
    def standard_markings(self):
        r"""
        Return an equivalent moduli space with the standard markings `{1, 2, \ldots, n}`.

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(2, [4, 7])
            sage: R
            TautologicalRing(g=2, n=(4, 7), moduli='st') over Rational Field
            sage: R.standard_markings()
            TautologicalRing(g=2, n=2, moduli='st') over Rational Field
        """
        if not self._markings or self._markings[-1] == self._n:
            return self
        return TautologicalRing(self._g, self._n, moduli=self._moduli, base_ring=self.base_ring())

    def is_integral_domain(self):
        r"""
        Return ``False`` unless the tautological ring is supported in degree 0 and the base ring
        is an integral domain.

        This uses that any element of positive order is torsion.

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: TautologicalRing(1,3,moduli='ct').socle_degree()
            2
            sage: TautologicalRing(1,3,moduli='ct').is_integral_domain()
            False
            sage: TautologicalRing(0,3).is_integral_domain()
            True
            sage: TautologicalRing(0,3,base_ring=ZZ.quotient(8)).is_integral_domain()
            False
        """
        return self.socle_degree() == 0 and self.base_ring().is_integral_domain()

    def is_field(self):
        r"""
        Return ``False`` unless the tautological ring is supported in degree 0 and the base ring
        is a field.

        This uses that any element of positive order is torsion.

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: TautologicalRing(1,3,moduli='ct').socle_degree()
            2
            sage: TautologicalRing(1,3,moduli='ct').is_field()
            False
            sage: TautologicalRing(0,3).is_field()
            True
            sage: TautologicalRing(0,3,base_ring=ZZ.quotient(5)).is_field()
            True
        """
        return self.socle_degree() == 0 and self.base_ring().is_field()

    def is_prime_field(self):
        r"""
        Return ``False`` unless the tautological ring is supported in degree 0 and the base ring
        is a prime field.

        This uses that any element of positive order is torsion.

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: TautologicalRing(1,3,moduli='ct', base_ring=GF(5)).is_prime_field()
            False
            sage: TautologicalRing(0,3,base_ring=QQ).is_prime_field()
            True
            sage: TautologicalRing(0,3,base_ring=GF(5)).is_prime_field()
            True
        """
        return self.socle_degree() == 0 and self.base_ring().is_prime_field()

    def _coerce_map_from_(self, other):
        r"""
        TESTS::

            sage: from admcycles import TautologicalRing
            sage: TautologicalRing(1, 1, base_ring=QQ['x','y']).has_coerce_map_from(TautologicalRing(1, 1, base_ring=QQ))
            True

            sage: M11st = TautologicalRing(1, 1, moduli='st')
            sage: M11ct = TautologicalRing(1, 1, moduli='ct')
            sage: M11st.has_coerce_map_from(M11ct)
            False
            sage: M11ct.has_coerce_map_from(M11st)
            True
        """
        if isinstance(other, TautologicalRing) and \
           self._g == other._g and \
           self._markings == other._markings and \
           self._moduli <= other._moduli and \
           self.base_ring().has_coerce_map_from(other.base_ring()):
            return True

    def construction(self):
        r"""
        Return a functorial construction (when applied to a base ring).

        This function is mostly intended to make the tautological ring behave nicely
        with Sage ecosystem.

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(1, 1)
            sage: QQ['x'].gen() * R.psi(1) # indirect doctest
            Graph :      [1] [[1]] []
            Polynomial : x*psi_1

            sage: A = TautologicalRing(3, 2, moduli='st', base_ring=QQ['x'])
            sage: B = TautologicalRing(3, 2, moduli='tl', base_ring=QQ)
            sage: A.psi(1) + B.psi(2) # indirect doctest
            Graph :      [3] [[1, 2]] []
            Polynomial : psi_1 + psi_2
            sage: (A.psi(1) + B.psi(2)).parent()
            TautologicalRing(g=3, n=2, moduli='tl') over Univariate Polynomial Ring in x over Rational Field
        """
        return TautologicalRingFunctor(self._g, self._markings, self._moduli), self.base_ring()

    def _repr_(self):
        if self._markings == tuple(range(1, self._n + 1)):
            return 'TautologicalRing(g={}, n={}, moduli={!r}) over {}'.format(self._g, self._n, _moduli_to_str[self._moduli], self.base_ring())
        else:
            return 'TautologicalRing(g={}, n={}, moduli={!r}) over {}'.format(self._g, self._markings, _moduli_to_str[self._moduli], self.base_ring())

    def socle_degree(self):
        r"""
        Return the socle degree of this tautological ring.

        The socle degree is the maximal degree whose corresponding graded
        component is non-empty. It is currently not implemented for the
        moduli of tree like curves.

        The formulas were computed in:

        - [GrVa01]_, [GrVa05]_ and [FaPa05]_ for compact type
        - [Lo95]_, [Fa99]_ and [FaPa00]_ for rational tail
        - [Lo95]_, [Io02]_ for smooth curves

        EXAMPLES::

            sage: from admcycles import TautologicalRing

        We display below the socle degree for various `(g, n)` for the moduli of
        smooth curves, rational tails, compact types and stable curves::

            sage: for (g,n) in [(0,3), (0,4), (0, 5), (1,1), (1,2), (2,0), (2, 1)]:
            ....:     dims = []
            ....:     for moduli in ['sm', 'rt', 'ct', 'st']:
            ....:         R = TautologicalRing(g, n, moduli=moduli)
            ....:         dims.append(R.socle_degree())
            ....:     print("g={} n={}: {}".format(g, n, " ".join(map(str, dims))))
            g=0 n=3: 0 0 0 0
            g=0 n=4: 0 1 1 1
            g=0 n=5: 0 2 2 2
            g=1 n=1: 0 0 0 1
            g=1 n=2: 0 1 1 2
            g=2 n=0: 0 0 1 3
            g=2 n=1: 1 1 2 4

        The socle degree is overestimated for tree-like::

            sage: R = TautologicalRing(2, moduli='tl')
            sage: R.socle_degree()
            3
            sage: R.kappa(3).is_zero() # generator for \bar M_2
            True
        """
        return socle_degree(self._g, self._n, self._moduli)

    @cached_method
    def trivial_graph(self):
        r"""
        Return the stable graph corresponding to the full stratum.

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: TautologicalRing(2, [1, 3, 4]).trivial_graph()
            [2] [[1, 3, 4]] []
        """
        return StableGraph([self._g], [list(self._markings)], [], mutable=False)

    def _an_element_(self):
        return self.one()

    def some_elements(self):
        r"""
        Return some elements in this tautological ring.

        This is mostly used for sage test system.

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: _  = TautologicalRing(0, [4, 5, 7]).some_elements()
            sage: _ = TautologicalRing(2, [4, 7]).some_elements()
        """
        base_elts = [self(s) for s in self.base_ring().some_elements()]
        elts = base_elts[:2] + base_elts[-2:]
        elts.append(self.irreducible_boundary_divisor())
        if self._markings:
            elts.append(self.psi(self._markings[0]))
        if self._g > 0:
            elts.append(self.kappa(1))
        return elts

    # TODO: if immutable, we could cache the method
    # @cached_method
    def zero(self):
        r"""
        Return the zero element.

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: TautologicalRing(0, 4).zero()
            0
        """
        return self.element_class(self, [])

    def sum(self, classes):
        r"""
        Return the sum of ``classes``.

        EXAMPLES::

            sage: from admcycles import TautologicalRing, psiclass
            sage: R = TautologicalRing(1, 2)
            sage: R.sum([R(1),R(1),R(0),R(1)])
            Graph :      [1] [[1, 2]] []
            Polynomial : 3
            sage: R.sum([psiclass(1,1,2),psiclass(2,1,2)]) == psiclass(1,1,2) + psiclass(2,1,2)
            True
            sage: R.sum([1,1])
            Graph :      [1] [[1, 2]] []
            Polynomial : 2

        Your elements must be coercible into the tautological ring::

            sage: R.sum(['a', 'b', 'c'])
            Traceback (most recent call last):
            ...
            TypeError: no canonical coercion from <... 'str'> to TautologicalRing(g=1, n=2, moduli='st') over Rational Field
        """
        result = self.zero()
        for t in classes:
            t = self.coerce(t)
            for g, term in t._terms.items():
                # TODO: implement a sum for list of KappaPsiPolynomial
                if g in result._terms:
                    result._terms[g].poly += term.poly
                    if not result._terms[g]:
                        del result._terms[g]
                else:
                    result._terms[g] = term.copy()
        return result

    # TODO: if immutable, we could cache the method
    # @cached_method
    def fundamental_class(self):
        r"""
        Return the fundamental class as a cohomology class.

        The fundamental class is the unit of the ring.

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(2, 1)
            sage: R.fundamental_class()
            Graph :      [2] [[1]] []
            Polynomial : 1

            sage: R.fundamental_class() ** 2 == R.fundamental_class()
            True
        """
        return self(self.trivial_graph())

    one = fundamental_class

    def psi(self, i):
        r"""
        Return the class `\psi_i` on `\bar M_{g,n}`.

        Alternatively, you could use the function :func:`~admcycles.admcycles.psiclass`.

        INPUT:

        i : integer
            the leg number associated to the psi class

        EXAMPLES::

            sage: from admcycles import TautologicalRing, StableGraph

            sage: R = TautologicalRing(2, 3)
            sage: R.psi(2)
            Graph :      [2] [[1, 2, 3]] []
            Polynomial : psi_2
            sage: R.psi(3)
            Graph :      [2] [[1, 2, 3]] []
            Polynomial : psi_3

            sage: R = TautologicalRing(3, 2)
            sage: R.psi(1)
            Graph :      [3] [[1, 2]] []
            Polynomial : psi_1

        TESTS::

            sage: from admcycles import TautologicalRing

            sage: R = TautologicalRing(3, 2)
            sage: R.psi(3)
            Traceback (most recent call last):
            ...
            ValueError: unknown marking 3 for psi
        """
        return self(self.trivial_graph(), psi={i: 1})

    def kappa(self, a):
        r"""
        Return the (Arbarello-Cornalba) kappa-class `\kappa_a` on `\bar M_{g,n}` defined by

          `\kappa_a= \pi_*(\psi_{n+1}^{a+1})`

        where `pi` is the morphism `\bar M_{g,n+1} \to \bar M_{g,n}`.

        INPUT:

        a : integer
            the degree a of the kappa class

        EXAMPLES::

            sage: from admcycles import TautologicalRing

            sage: R = TautologicalRing(3, 1)
            sage: R.kappa(2)
            Graph :      [3] [[1]] []
            Polynomial : (kappa_2)_0

            sage: R = TautologicalRing(3, 2)
            sage: R.kappa(1)
            Graph :      [3] [[1, 2]] []
            Polynomial : (kappa_1)_0
        """
        if a == 0:
            return (2 * self._g - 2 + self._n) * self.one()
        elif a < 0:
            return self.zero()
        else:
            return self(self.trivial_graph(), kappa=[[0] * (a - 1) + [1]])

    def lambdaclass(self, d, pull=True):
        r"""
        Return the tautological class `\lambda_d` on `\bar M_{g,n}`.

        The `\lambda_d` class is defined as the d-th Chern class

          `\lambda_d = c_d(E)`

        of the Hodge bundle `E`. The result is represented as a sum of stable
        graphs with kappa and psi classes.

        INPUT:

        d : integer
          the degree
        pull : boolean (optional, default to ``True``)
          whether the class is computed as pullback from `\bar M_{g}`

        EXAMPLES::

            sage: from admcycles import TautologicalRing

            sage: R = TautologicalRing(2, 0)
            sage: R.lambdaclass(1)
            Graph :      [2] [[]] []
            Polynomial : 1/12*(kappa_1)_0
            <BLANKLINE>
            Graph :      [1] [[2, 3]] [(2, 3)]
            Polynomial : 1/24
            <BLANKLINE>
            Graph :      [1, 1] [[2], [3]] [(2, 3)]
            Polynomial : 1/24

            sage: R = TautologicalRing(1, 1)
            sage: R.lambdaclass(1)
            Graph :      [1] [[1]] []
            Polynomial : 1/12*(kappa_1)_0 - 1/12*psi_1
            <BLANKLINE>
            Graph :      [0] [[3, 4, 1]] [(3, 4)]
            Polynomial : 1/24

        TESTS::

            sage: from admcycles import lambdaclass
            sage: inputs = [(0,0,4), (1,1,3), (1,2,1), (2,2,1), (3,2,1), (-1,2,1), (2,3,2)]
            sage: for d,g,n in inputs:
            ....:     R = TautologicalRing(g, n)
            ....:     assert (R.lambdaclass(d) - R.lambdaclass(d,pull=False)).is_zero()

        Check for https://gitlab.com/modulispaces/admcycles/issues/58::

            sage: R = TautologicalRing(4,0)
            sage: L = R.lambdaclass(4)
            sage: L == R.double_ramification_cycle(())
            True
            sage: L.basis_vector()
            (-229/4, 28/3, 55/24, -13/12, 1/24, 0, 0, 0, 0, 0, 0, 0, -1/2, 1/6, 1, -1/3, -1/3, 2/3, 2/3, -4/3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4/3, 1/3, -5/3, 20/3, 16/9, -4/3, 2/9, 1/6, 0, 0, 0, 0, 0, 0, 0, 0, 0)
        """
        g = self._g
        n = self._n
        if d > g or d < 0:
            return self.zero()

        if n > 0 and pull:
            if g == 0:
                return self.fundamental_class()
            elif g == 1:
                newmarks = list(range(2, n + 1))
                R = TautologicalRing(1, 1, moduli=self._moduli)
                return R.lambdaclass(d, pull=False).forgetful_pullback(newmarks)
            else:
                newmarks = list(range(1, n + 1))
                R = TautologicalRing(g, 0, moduli=self._moduli)
                return R.lambdaclass(d, pull=False).forgetful_pullback(newmarks)

        return self.chern_character_to_class(d, self.hodge_chern_character)

    def irreducible_boundary_divisor(self):
        r"""
        Return the pushforward of the fundamental class under the irreducible
        boundary gluing map `\bar M_{g-1,n+2} \to \bar M_{g,n}`.

        EXAMPLES::

            sage: from admcycles import *

            sage: R = TautologicalRing(2, 5)
            sage: R.irreducible_boundary_divisor()
            Graph :      [1] [[1, 2, 3, 4, 5, 6, 7]] [(6, 7)]
            Polynomial : 1

            sage: R = TautologicalRing(3, 0)
            sage: R.irreducible_boundary_divisor()
            Graph :      [2] [[1, 2]] [(1, 2)]
            Polynomial : 1
        """
        if self._g == 0:
            return self.zero()
        g = self._g
        last = self._markings[-1] if self._markings else 0
        G = StableGraph([g - 1], [list(self._markings) + [last + 1, last + 2]], [(last + 1, last + 2)])
        return self(G)

    # alias
    irrbdiv = irreducible_boundary_divisor

    def separable_boundary_divisor(self, h, A):
        r"""
        Return the pushforward of the fundamental class under the boundary
        gluing map `\bar M_{h,A} \times \bar M_{g-h,{1,...,n} \ A} \to  \bar M_{g,n}`.

        INPUT:

        h : integer
          genus of the first vertex
        A : list
          list of markings on the first vertex

        EXAMPLES::

            sage: from admcycles import *

            sage: R = TautologicalRing(2, 5)
            sage: R.separable_boundary_divisor(1, (1,3,4))
            Graph :      [1, 1] [[1, 3, 4, 6], [2, 5, 7]] [(6, 7)]
            Polynomial : 1

            sage: R = TautologicalRing(3, 3)
            sage: R.separable_boundary_divisor(1, (2,))
            Graph :      [1, 2] [[2, 4], [1, 3, 5]] [(4, 5)]
            Polynomial : 1

            sage: R = TautologicalRing(2, [4, 6])
            sage: R.separable_boundary_divisor(1, (6,))
            Graph :      [1, 1] [[6, 7], [4, 8]] [(7, 8)]
            Polynomial : 1
        """
        g = self._g
        last = self._markings[-1] if self._markings else 1
        G = StableGraph([h, g - h], [list(A) + [last + 1], sorted(set(self._markings) -
                        set(A)) + [last + 2]], [(last + 1, last + 2)])
        return self(G)

    # alias
    sepbdiv = separable_boundary_divisor

    # TODO: if immutable, we could cache the result
    # (this was wrongly cached before merge request !109)
    # @cached_method
    def hodge_chern_character(self, d):
        r"""
        Return the chern character `ch_d(E)` of the Hodge bundle `E` on `\bar
        M_{g,n}`.

        This function implements the formula from [Mu83]_.

        INPUT:

        d : integer
            The degree of the Chern character.

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(1, 2)
            sage: R.hodge_chern_character(1)
            Graph :      [1] [[1, 2]] []
            Polynomial : 1/12*(kappa_1)_0 - 1/12*psi_1 - 1/12*psi_2
            <BLANKLINE>
            Graph :      [0] [[1, 2, 3, 4]] [(3, 4)]
            Polynomial : 1/24
            <BLANKLINE>
            Graph :      [0, 1] [[1, 2, 3], [4]] [(3, 4)]
            Polynomial : 1/12
        """
        if self._markings and self._markings[-1] != len(self._markings):
            raise NotImplementedError('hodge_chern_character unsupported with non-standard markings')

        g = self._g
        n = self._n
        if g == 0:
            return self.zero()
        from .admcycles import list_strata
        bdries = list_strata(g, n, 1)
        irrbdry = bdries.pop(0)

        d = ZZ(d)

        if d == 0:
            return g * self.fundamental_class()
        elif d % 2 == 0 or d < 0:
            return self.zero()

        from .admcycles import psicl
        psipsisum_onevert = sum(((-1)**i) * (psicl(n + 1, 1)**i) * (psicl(n + 2, 1)**(d - 1 - i)) for i in range(d))
        psipsisum_twovert = sum(((-1)**i) * (psicl(n + 1, 2)**i) * (psicl(n + 2, 2)**(d - 1 - i)) for i in range(d))

        contrib = self.kappa(d) - sum(self.psi(i)**d for i in range(1, n + 1))

        # old: contrib=kappaclass(d,g,n)-sum([psiclass(i,g,n) for i in range(1,n+1)])
        contrib += (QQ(1) / 2) * self(irrbdry, poly=psipsisum_onevert)
        contrib += sum(QQ((1, ind.automorphism_number())) * self(ind, poly=psipsisum_twovert) for ind in bdries)

        contrib.dimension_filter()

        return bernoulli(d + 1) / factorial(d + 1) * contrib

    # TODO
    # The function below is useful in some computations and does not need to know about the parent TautologicalRing
    # I think it makes more sense as a standalone function e.g. in admcycles.py
    def chern_character_to_class(self, t, char):
        r"""
        Return the Chern class associated to the Chern character.

        INPUT:

        t : integer
          degree of the output Chern class
        char : tautological class or a function
          Chern character, either represented as a (mixed-degree) tautological class or as
          a function m -> ch_m

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(1, 1)
            sage: R.chern_character_to_class(1, R.hodge_chern_character)
            Graph :      [1] [[1]] []
            Polynomial : 1/12*(kappa_1)_0 - 1/12*psi_1
            <BLANKLINE>
            Graph :      [0] [[3, 4, 1]] [(3, 4)]
            Polynomial : 1/24

        Note that the output of generalized_hodge_chern takes the form of a chern character::

            sage: from admcycles import *
            sage: from admcycles.GRRcomp import *
            sage: g=2;n=2;l=0;d=[1,-1];a=[[1,[1],-1]]
            sage: chern_char_to_class(1,generalized_hodge_chern(l,d,a,1,g,n)) # known bug
            Graph :      [2] [[1, 2]] []
            Polynomial : 1/12*(kappa_1^1 )_0
            <BLANKLINE>
            Graph :      [2] [[1, 2]] []
            Polynomial : (-13/12)*psi_1^1
            <BLANKLINE>
            Graph :      [2] [[1, 2]] []
            Polynomial : (-1/12)*psi_2^1
            <BLANKLINE>
            Graph :      [0, 2] [[1, 2, 4], [5]] [(4, 5)]
            Polynomial : 1/12*
            <BLANKLINE>
            Graph :      [1, 1] [[4], [1, 2, 5]] [(4, 5)]
            Polynomial : 1/12*
            <BLANKLINE>
            Graph :      [1, 1] [[2, 4], [1, 5]] [(4, 5)]
            Polynomial : 13/12*
            <BLANKLINE>
            Graph :      [1] [[4, 5, 1, 2]] [(4, 5)]
            Polynomial : 1/24*
        """
        if isinstance(char, TautologicalClass):
            arg = [(-1)**(s - 1) * factorial(s - 1) * char.simplified(r=s) for s in range(1, t + 1)]
        else:
            arg = [(-1)**(s - 1) * factorial(s - 1) * char(s) for s in range(1, t + 1)]

        exp = sum(multinomial(s.to_exp()) / factorial(len(s)) * prod(arg[k - 1] for k in s) for s in Partitions(t))
        if t == 0:
            return exp * self.fundamental_class()
        return exp.simplified(r=t)

    def _check_stable_graph(self, stg):
        if stg.g() != self._g or stg.n() != self._n:
            raise ValueError('invalid stable graph (has g={}, n={} instead of g={}, n={})'.format(
                stg.g(), stg.n(), self._g, self._n))
        markings = tuple(sorted(stg.list_markings()))
        if markings != self._markings:
            raise ValueError('invalid stable graph (has markings={} instead of {})'.format(markings, self._markings))

    def _element_constructor_(self, arg, kappa=None, psi=None, poly=None):
        r"""
        TESTS::

            sage: from admcycles import TautologicalRing, StableGraph
            sage: R = TautologicalRing(2,1)
            sage: R(2/3)
            Graph :      [2] [[1]] []
            Polynomial : 2/3

        From a stable graph with decorations::

            sage: g = StableGraph([1], [[1,2,3]], [(2,3)])
            sage: R(g)
            Graph :      [1] [[1, 2, 3]] [(2, 3)]
            Polynomial : 1

        A stable graph outside of the open set defines by the moduli gives zero::

            sage: Rct = TautologicalRing(2, 1, moduli='ct')
            sage: Rct(g)
            0

        From a sequence of decorated strata::

            sage: from admcycles.admcycles import decstratum
            sage: gg = StableGraph([2], [[1]], [])
            sage: arg = [decstratum(g), decstratum(gg, kappa=[[1]])]
            sage: R(arg)
            Graph :      [2] [[1]] []
            Polynomial : (kappa_1)_0
            <BLANKLINE>
            Graph :      [1] [[1, 2, 3]] [(2, 3)]
            Polynomial : 1

        Empty argument::

            sage: from admcycles import TautologicalRing
            sage: TautologicalRing(1, 1)([])
            0
        """
        if isinstance(arg, TautologicalClass):
            P = arg.parent()
            if P._g != self._g or P._n != self._n:
                raise ValueError('incompatible moduli spaces')
            return self.element_class(self, {g: term.copy() for g, term in arg._terms.items()})
        elif not arg:
            return self.zero()
        elif isinstance(arg, StableGraph):
            self._check_stable_graph(arg)
            if arg.vanishes(self._moduli):
                return self.zero()
            if psi is not None:
                if not isinstance(psi, dict):
                    raise ValueError('psi must be a dictionary')
                for i in psi:
                    if not any(i in arg._legs[v] for v in range(arg.num_verts())):
                        raise ValueError('unknown marking {} for psi'.format(i))
            dec = decstratum(arg, kappa=kappa, psi=psi, poly=poly)
            return self.element_class(self, [dec])
        elif isinstance(arg, (tuple, list)):
            # a sequence of decstratum
            for term in arg:
                if not isinstance(term, decstratum):
                    raise TypeError('must be a sequence of decstrata')
                self._check_stable_graph(term.gamma)
            return self.element_class(self, arg)
        else:
            raise NotImplementedError('unknown argument of type arg={}'.format(arg))

    # NOTE: replaces admcycles.Tautv_to_tautclass
    def from_vector(self, v, r):
        r"""
        Return the tautological class associated to the vector ``v`` and degree ``r`` on this tautological ring.

        See also :meth:`~TautlogicalRing.generators` and :meth:`~TautologicalRing.from_basis_vector`.

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(1, 2)
            sage: R.from_vector((0, -1, 0, 1, 0), 1)
            Graph :      [1] [[1, 2]] []
            Polynomial : -psi_1
            <BLANKLINE>
            Graph :      [0, 1] [[1, 2, 4], [5]] [(4, 5)]
            Polynomial : 1

            sage: R = TautologicalRing(1, [4, 7])
            sage: R.from_vector((0, -1, 0, 1, 0), 1)
            Graph :      [1] [[4, 7]] []
            Polynomial : -psi_4
            <BLANKLINE>
            Graph :      [0, 1] [[1, 4, 7], [5]] [(1, 5)]
            Polynomial : 1

        This also works with non-standard moduli::

            sage: R = TautologicalRing(2,0,moduli='ct')
            sage: R.generators(1)
            [Graph :      [2] [[]] []
             Polynomial : (kappa_1)_0,
             Graph :      [1, 1] [[2], [3]] [(2, 3)]
             Polynomial : 1]
            sage: R.from_vector((1,2),1)
            Graph :      [2] [[]] []
            Polynomial : (kappa_1)_0
            <BLANKLINE>
            Graph :      [1, 1] [[2], [3]] [(2, 3)]
            Polynomial : 2

        TESTS::

            sage: R = TautologicalRing(2,0)
            sage: x = polygen(ZZ)
            sage: v = vector((x,0,0,0,0,0,0,0))
            sage: R.from_vector(v, 2).parent().base_ring()
            Univariate Polynomial Ring in x over Rational Field
        """
        from .admcycles import Graphtodecstratum
        from . import DR
        strata = DR.all_strata(self._g, r, tuple(range(1, self._n + 1)),
                               moduli_type=get_moduli(self._moduli, DRpy=True))
        stratmod = []
        if len(v) != len(strata):
            raise ValueError('input v has wrong length')
        v = vector(v)
        BR = v.parent().base_ring()
        try:
            TR = coercion_model.common_parent(self, BR)
        except TypeError:
            TR = TautologicalRing(self._g, self._n, moduli=self._moduli, base_ring=BR)
        for i in range(len(v)):
            if not v[i]:
                continue
            currstrat = Graphtodecstratum(strata[i])
            currstrat.poly *= v[i]
            stratmod.append(currstrat)
        if self._markings and self._markings[-1] != self._n:
            dic = {i + 1: j for i, j in enumerate(self._markings)}
            R = TR.standard_markings()
            return R.element_class(R, stratmod).rename_legs(dic, inplace=False)
        else:
            return TR.element_class(TR, stratmod)

    def dimension(self, r):
        r"""
        INPUT:

        r : integer
          the degree

        EXAMPLES::

            sage: from admcycles import *
            sage: R = TautologicalRing(2, 1)
            sage: [R.dimension(r) for r in range(5)]
            [1, 3, 5, 3, 1]
            sage: R = TautologicalRing(2, 1, moduli='ct')
            sage: [R.dimension(r) for r in range(5)]
            [1, 2, 1, 0, 0]
        """
        if r < 0 or r > self.socle_degree():
            return 0

        if self._moduli == MODULI_TL:
            raise NotImplementedError('dimension not implemented for the moduli of treelike curves')

        # TODO: is there something smarter?
        from .admcycles import generating_indices
        return len(generating_indices(self._g, self._n, r, moduli=_moduli_to_str[self._moduli]))

    # NOTE: replaces admcycles.Tautbv_to_tautclass
    # TODO: full support for all moduli
    def from_basis_vector(self, v, r):
        r"""
        Return the tautological class of degree ``r`` corresponding to the
        vector ``v`` expressing the coefficients in the basis.

        See also :meth:`~TautologicalRing.basis` and :meth:`~TautologicalRing.from_vector`.

        INPUT:

        v : vector
        r : degree

        EXAMPLES::

            sage: from admcycles import TautologicalRing

            sage: R = TautologicalRing(2, 1)
            sage: R.from_basis_vector((1,0,-2), 1)
            Graph :      [2] [[1]] []
            Polynomial : (kappa_1)_0
            <BLANKLINE>
            Graph :      [1, 1] [[3], [1, 4]] [(3, 4)]
            Polynomial : -2

            sage: R = TautologicalRing(2, [3])
            sage: R.from_basis_vector((1,0,-2), 1)
            Graph :      [2] [[3]] []
            Polynomial : (kappa_1)_0
            <BLANKLINE>
            Graph :      [1, 1] [[1], [3, 4]] [(1, 4)]
            Polynomial : -2

        TESTS::

            sage: for mo in ['st', 'ct', 'rt', 'sm']:
            ....:     R = TautologicalRing(2,2,moduli=mo)
            ....:     for a in R.generators(2):
            ....:         assert a == R.from_basis_vector(a.basis_vector(),2)
        """
        if self._moduli == MODULI_TL:
            raise NotImplementedError('from_basis not implemented for the moduli of treelike curves')
        from .admcycles import Graphtodecstratum, generating_indices
        from . import DR
        genind = generating_indices(self._g, self._n, r, moduli=_moduli_to_str[self._moduli])
        # TODO: maybe use the method TautologicalRing.generators?
        strata = DR.all_strata(self._g, r, tuple(range(1, self._n + 1)),
                               moduli_type=get_moduli(self._moduli, DRpy=True))
        stratmod = []
        if len(v) != len(genind):
            from warnings import warn
            warn('vector v has wrong length {}; should have been {}'.format(len(v), len(strata)), DeprecationWarning)
        for i in range(len(v)):
            if not v[i]:
                continue
            currstrat = Graphtodecstratum(strata[genind[i]])
            currstrat.poly *= v[i]
            stratmod.append(currstrat)

        if self._markings and self._markings[-1] != self._n:
            dic = {i + 1: j for i, j in enumerate(self._markings)}
            R = self.standard_markings()
            return R.element_class(R, stratmod).rename_legs(dic, inplace=False)
        else:
            return self.element_class(self, stratmod)

    # TODO: if elements were immutable, this could be cached
    def generators(self, r=None):
        r"""
        INPUT:

        r : integer (optional)
            the degree. If provided, only returns the generators of a given degree.

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(2,0)
            sage: R.generators(1)
            [Graph :      [2] [[]] []
             Polynomial : (kappa_1)_0,
             Graph :      [1, 1] [[2], [3]] [(2, 3)]
             Polynomial : 1,
             Graph :      [1] [[2, 3]] [(2, 3)]
             Polynomial : 1]
            sage: R = TautologicalRing(2,0,moduli='ct')
            sage: R.generators(1)
            [Graph :      [2] [[]] []
             Polynomial : (kappa_1)_0,
             Graph :      [1, 1] [[2], [3]] [(2, 3)]
             Polynomial : 1]
            sage: R = TautologicalRing(2,0,moduli='sm')
            sage: R.generators(1)
            []

        TESTS::

            sage: R = TautologicalRing(1, 2)
            sage: for v in R.generators(0): print(v.vector())
            (1)
            sage: for v in R.generators(1): print(v.vector())
            (1, 0, 0, 0, 0)
            (0, 1, 0, 0, 0)
            (0, 0, 1, 0, 0)
            (0, 0, 0, 1, 0)
            (0, 0, 0, 0, 1)
            sage: for v in R.generators(2): print(v.vector())
            (1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
            (0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
            (0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
            (0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
            (0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
            (0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0)
            (0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0)
            (0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0)
            (0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0)
            (0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0)
            (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0)
            (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0)
            (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0)
            (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0)
            (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1)

        Test compatibility with nonstandard markings::

            sage: R = TautologicalRing(1,[2,4])
            sage: R.generators(1)
            [Graph :      [1] [[2, 4]] []
             Polynomial : (kappa_1)_0, Graph :      [1] [[2, 4]] []
             Polynomial : psi_2, Graph :      [1] [[2, 4]] []
             Polynomial : psi_4, Graph :      [0, 1] [[1, 2, 4], [5]] [(1, 5)]
             Polynomial : 1, Graph :      [0] [[1, 2, 4, 5]] [(1, 5)]
             Polynomial : 1]
        """
        if r is None:
            result = []
            for r in range(self.socle_degree() + 1):
                result.extend(self.generators(r))
            return result

        r = ZZ(r)
        if r < 0 or r > self.socle_degree():
            return []

        from .DR import all_strata
        from .admcycles import Graphtodecstratum
        moduli = get_moduli(self._moduli, DRpy=True)
        if self._markings and self._markings[-1] == self._n:
            return [self.element_class(self, [Graphtodecstratum(stratum)])
                    for stratum in all_strata(self._g, r,
                                              tuple(range(1, self._n + 1)),
                                              moduli_type=moduli)]
        return [self.element_class(self, [Graphtodecstratum(stratum).rename_legs({i + 1: j for i, j in enumerate(self._markings)})])
                for stratum in all_strata(self._g, r,
                                          tuple(range(1, self._n + 1)),
                                          moduli_type=moduli)]

    # NOTE: by convention we make gens return a tuple. We do not use the generic gens
    # which performs some caching and does not allow extra arguments.
    def gens(self, r=None):
        r"""
        Return a tuple whose entries are module generators for this tautological ring.

        INPUT:

        r: integer (optional)
        If provided, return generators in the given degree only.

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(2,0)
            sage: R.gens(1)
            (Graph :      [2] [[]] []
             Polynomial : (kappa_1)_0,
             Graph :      [1, 1] [[2], [3]] [(2, 3)]
             Polynomial : 1,
             Graph :      [1] [[2, 3]] [(2, 3)]
             Polynomial : 1)
        """
        return tuple(self.generators(r))

    def ngens(self, r=None):
        r"""
        Return the number of generators.

        INPUT:

        r: integer (optional)
        If provided, return the number of generators of the given degree.

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(2, 0)
            sage: R.ngens()
            29
            sage: R.ngens(2)
            8

        TESTS::

            sage: R = TautologicalRing(2,0,moduli='ct')
            sage: R.socle_degree()
            1
            sage: R.ngens()
            3
            sage: len(R.generators(1))
            2
        """
        if r is None:
            return sum(self.ngens(r) for r in range(self.socle_degree() + 1))

        r = ZZ(r)
        if r < 0 or r > self.socle_degree():
            return ZZ.zero()

        try:
            ngens = self._ngens
        except AttributeError:
            ngens = self._ngens = [None] * (self.socle_degree() + 1)

        from .DR import num_strata
        if ngens[r] is None:
            ngens[r] = ZZ(num_strata(self._g, r, tuple(range(1, self._n + 1)), moduli_type=get_moduli(self._moduli, DRpy=True)))

        return ngens[r]

    def gen(self, i=0, r=None):
        r"""
        Return the ``i``-th generator.

        INPUT:

        i : integer (default ``0``)
        The number of the generator.

        r : integer (optional)
        If provided, return the ``i``-th generator in degree ``r``.

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(2, 0)
            sage: R.gen(23)
            Graph :      [0, 1] [[3, 4, 5], [6]] [(3, 4), (5, 6)]
            Polynomial : (kappa_1)_1
            sage: [R.ngens(i) for i in range(4)]
            [1, 3, 8, 17]
            sage: R.gen(11,3)
            Graph :      [0, 1] [[3, 4, 5], [6]] [(3, 4), (5, 6)]
            Polynomial : (kappa_1)_1
            sage: R.gen(2, 3)
            Graph :      [2] [[]] []
            Polynomial : (kappa_1^3)_0

        TESTS::

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(2, 0)
            sage: R.generators() == [R.gen(i) for i in range(R.ngens())]
            True
            sage: R.generators(3) == [R.gen(i, 3) for i in range(R.ngens(3))]
            True
        """
        if i < 0 or i > self.ngens(r):
            raise ValueError('undefined generator')

        if r is None:
            r = 0
            while i >= self.ngens(r):
                i -= self.ngens(r)
                r += 1
        return self.generators(r)[i]

    def list_generators(self, r):
        r"""
        Lists all tautological classes of degree r in the tautological ring.

        INPUT:

        r : integer
        The degree r of of the classes.

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(2,0)
            sage: R.list_generators(2)
            [0] : Graph :      [2] [[]] []
            Polynomial : (kappa_2)_0
            [1] : Graph :      [2] [[]] []
            Polynomial : (kappa_1^2)_0
            [2] : Graph :      [1, 1] [[2], [3]] [(2, 3)]
            Polynomial : (kappa_1)_0
            [3] : Graph :      [1, 1] [[2], [3]] [(2, 3)]
            Polynomial : psi_2
            [4] : Graph :      [1] [[2, 3]] [(2, 3)]
            Polynomial : (kappa_1)_0
            [5] : Graph :      [1] [[2, 3]] [(2, 3)]
            Polynomial : psi_2
            [6] : Graph :      [0, 1] [[3, 4, 5], [6]] [(3, 4), (5, 6)]
            Polynomial : 1
            [7] : Graph :      [0] [[3, 4, 5, 6]] [(3, 4), (5, 6)]
            Polynomial : 1
        """
        L = self.generators(r)
        for i in range(len(L)):
            print('[' + repr(i) + '] : ' + repr(L[i]))

    # TODO: if elements were immutable, this could be cached
    # TODO: full support for all moduli
    def basis(self, d=None):
        r"""
        Return a basis.

        INPUT:

        d : ``None`` (default) or integer
          if ``None`` return a full basis if ``d`` is provided, return a basis
          of the homogeneous component of degree ``d``

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(2, 0)
            sage: R.basis(2)
            [Graph :      [2] [[]] []
             Polynomial : (kappa_2)_0,
             Graph :      [2] [[]] []
             Polynomial : (kappa_1^2)_0]
            sage: R2 = TautologicalRing(2, 1, moduli='ct')
            sage: R2.basis(1)
            [Graph :      [2] [[1]] []
             Polynomial : (kappa_1)_0,
             Graph :      [2] [[1]] []
             Polynomial : psi_1]
        """
        if d is None:
            result = []
            for d in range(self.socle_degree() + 1):
                result.extend(self.basis(d))
            return result

        if self._moduli == MODULI_TL:
            raise NotImplementedError('basis not implemented for treelike curves')

        from .admcycles import generating_indices
        gens = self.generators(d)
        return [gens[i] for i in generating_indices(self._g, self._n, d, moduli=_moduli_to_str[self._moduli])]

    def kappa_psi_polynomials(self, d, combout=False):
        r"""
        Iterator over the polynomials in kappa and psi classes of degree ``d``.

        For combout=True it returns a generator of triples
        (kappalist, psidict, kppoly) of

          * a list kappalist of exponents of kappa_i,
          * a dictionary psidict sending i to the exponent of psi_i,
          * the associated TautologicalClass for this monomial.

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: for a in TautologicalRing(0, 4).kappa_psi_polynomials(1): print(a)
            Graph :      [0] [[1, 2, 3, 4]] []
            Polynomial : (kappa_1)_0
            Graph :      [0] [[1, 2, 3, 4]] []
            Polynomial : psi_1
            Graph :      [0] [[1, 2, 3, 4]] []
            Polynomial : psi_2
            Graph :      [0] [[1, 2, 3, 4]] []
            Polynomial : psi_3
            Graph :      [0] [[1, 2, 3, 4]] []
            Polynomial : psi_4

            sage: for a in TautologicalRing(1, [2,7]).kappa_psi_polynomials(1): print(a)
            Graph :      [1] [[2, 7]] []
            Polynomial : (kappa_1)_0
            Graph :      [1] [[2, 7]] []
            Polynomial : psi_2
            Graph :      [1] [[2, 7]] []
            Polynomial : psi_7

        Here is the option where the combinatorial data is output separately::

            sage: for a in TautologicalRing(1, [2,7]).kappa_psi_polynomials(1, True): print(a)
            ([1], {}, Graph :      [1] [[2, 7]] []
            Polynomial : (kappa_1)_0)
            ([], {2: 1}, Graph :      [1] [[2, 7]] []
            Polynomial : psi_2)
            ([], {7: 1}, Graph :      [1] [[2, 7]] []
            Polynomial : psi_7)
        """
        triv = self.trivial_graph()
        for V in IntegerVectors(d, 1 + self._n):
            psi = {i: a for i, a in zip(self._markings, V[1:]) if a}
            for kV in Partitions(V[0]):
                kappa = []
                for i, a in enumerate(kV.to_exp()):
                    if not a:
                        continue
                    kappa.extend([0] * (i + 1 - len(kappa)))
                    kappa[i] = a
                cl = self(triv, psi=psi, kappa=[kappa])
                yield (kappa, psi, cl) if combout else cl

    def num_gens(self, r):
        r"""
        INPUT:

        r : integer
          degree

        TESTS::

            sage: from admcycles import *
            sage: R = TautologicalRing(1,2)
            sage: R.num_gens(1)
            5
            sage: len(R.generators(1))
            5
            sage: R = TautologicalRing(1,2,moduli='ct')
            sage: R.num_gens(1)
            4
        """
        from .DR import num_strata
        return num_strata(self._g, r, tuple(range(1, self._n + 1)), self._moduli)

    @cached_method
    def pairing_matrix(self, d, basis=False, ind_d=None, ind_dcomp=None):
        r"""
        Computes the matrix of the intersection pairing of generators in
        degree d (rows) against generators of opposite degree (columns).

        INPUT:

        d : integer
        degree of the classes associated to rows

        basis : bool (default: False)
        compute pairing of basis elements in the two degrees

        ind_d, ind_dcomp: tuple (optional)
        lists of indices of generators in degrees d and its complementary degree

        NOTE:

        The matrix is returned as an immutable object, to allow caching.

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(1,2)
            sage: R.pairing_matrix(1)
            [  1/8  1/12  1/12  1/24     1]
            [ 1/12  1/24  1/24     0     1]
            [ 1/12  1/24  1/24     0     1]
            [ 1/24     0     0 -1/24     1]
            [    1     1     1     1     0]
            sage: R.pairing_matrix(1, basis=True)
            [ 1/8 1/12]
            [1/12 1/24]
            sage: R.pairing_matrix(1, ind_d=(0,1), ind_dcomp=(1,2,3))
            [1/12 1/12 1/24]
            [1/24 1/24    0]
        """
        dcomp = self.socle_degree() - d

        if ind_d is not None:
            allgens = self.generators(d)
            gens = [allgens[i] for i in ind_d]
        elif basis:
            gens = self.basis(d)
        else:
            gens = self.generators(d)

        if ind_dcomp is not None:
            allcogens = self.generators(dcomp)
            cogens = [allcogens[i] for i in ind_dcomp]
        elif basis:
            cogens = self.basis(dcomp)
        else:
            cogens = self.generators(dcomp)

        # TODO: for d = dcomp we only need to compute half of these numbers
        M = matrix(QQ, [[(a * b).evaluate() for b in cogens] for a in gens])
        M.set_immutable()
        return M

    def double_ramification_cycle(self, Avector, d=None, k=None, rpoly=False, tautout=True, basis=False, chiodo_coeff=False, r_coeff=None):
        r"""
        Return the k-twisted double ramification cycle in genus g and codimension d
        for the partition Avector of k*(2g-2+n). For more information see the documentation
        of :func:`~admcycles.double_ramification_cycle.DR_cycle`.

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(2,2)
            sage: DR = R.double_ramification_cycle([1,3], k=1, d=1)
            sage: (DR * R.psi(1)^3).evaluate()
            -11/1920
        """
        from .double_ramification_cycle import DR_cycle
        if len(Avector) != self._n:
            raise ValueError('length of argument Avector must be n')
        return DR_cycle(self._g, Avector, d=None, k=None, rpoly=False, tautout=True, basis=False, chiodo_coeff=False, r_coeff=None, moduli=self._moduli, base_ring=self.base_ring())

    def theta_class(self):
        r"""
        Return the class Theta_{g,n} from [Norbury - A new cohomology class on the moduli space of curves].
        For more information see the documentation of :func:`~admcycles.double_ramification_cycle.ThetaClass`.

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(1, 1)
            sage: R.theta_class()
            Graph :      [1] [[1]] []
            Polynomial : 11/6*(kappa_1)_0 + 1/6*psi_1
            <BLANKLINE>
            Graph :      [0] [[3, 4, 1]] [(3, 4)]
            Polynomial : 1/24
            sage: R = TautologicalRing(2, 1, moduli='ct')
            sage: R.theta_class()
            0
        """
        from .double_ramification_cycle import ThetaClass
        return self(ThetaClass(self._g, self._n, moduli=self._moduli))

    def hyperelliptic_cycle(self, n=0, m=0):
        r"""
        Return the cycle class of the hyperelliptic locus of genus g curves with n marked
        fixed points and m pairs of conjugate points in `\bar M_{g,n+2m}`.

        For more information see the documentation of :func:`~admcycles.admcycles.Hyperell`.

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(2,1)
            sage: H = R.hyperelliptic_cycle(1,0)
            sage: H.forgetful_pushforward([1]).fund_evaluate()
            6
        """
        if n + 2 * m != self._n:
            raise ValueError('the number n+2m must equal the total number of marked points')
        from .admcycles import Hyperell
        return self(Hyperell(self._g, n, m))

    def bielliptic_cycle(self, n=0, m=0):
        r"""
        Return the cycle class of the bielliptic locus of genus g curves with n marked
        fixed points and m pairs of conjugate points in `\bar M_{g,n+2m}`.

        For more information see the documentation of :func:`~admcycles.admcycles.Biell`.

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(1,2)
            sage: B = R.bielliptic_cycle(0,1)
            sage: B.degree_list()
            [1]
            sage: B.forgetful_pushforward([2]).fund_evaluate()
            3
        """
        if n + 2 * m != self._n:
            raise ValueError('the number n+2m must equal the total number of marked points')
        from .admcycles import Biell
        return self(Biell(self._g, n, m))

    def generalized_lambda(self, deg, l, d, a):
        r"""
        Computes the Chern class c_deg of the derived pushforward of a line bundle
        \O(D) on the universal curve C_{g,n} over the space Mbar_{g,n} of stable curves, for

          D = l \tilde{K} + sum_{i=1}^n d_i \sigma_i  +  \sum_{h,S} a_{h,S} C_{h,S}

        where the numbers l, d_i and a_{h,S} are integers, \tilde{K} is the relative canonical
        class of the morphism C_{g,n} -> Mbar_{g,n}, \sigma_i is the image of the ith section
        and C_{h,S} is the boundary divisor of C_{g,n} where the moving point lies on a genus h
        component with markings given by the set S.

        For more information see the documentation of :func:`~admcycles.GRRcomp.generalized_lambda`.

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(2,1)
            sage: l = 1; d = [0]; a = []
            sage: t = R.generalized_lambda(1,l,d,a)
            sage: t.basis_vector()
            (1/2, -1/2, -1/2)
        """
        if len(d) != self._n:
            raise ValueError('the number of entries of d equal the total number of marked points')
        from .GRRcomp import generalized_lambda
        return self(generalized_lambda(deg, l, d, a, self._g, self._n))

    def cotangent_chern_class(self, d):
        r"""
        Return the d-th Chern class of the cotangent bundle of the moduli space.

        This represents the Chern class of the ordinary cotangent bundle on the moduli
        space of curves.

        INPUT:

        - ``d`` -- non-negative integer; degree of the Chern class

        OUTPUT:

        A tautological class representing the d-th Chern class of the cotangent bundle.

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(2, 0)
            sage: R.cotangent_chern_class(1)
            Graph :      [2] [[]] []
            Polynomial : 13/12*(kappa_1)_0
            <BLANKLINE>
            Graph :      [1] [[2, 3]] [(2, 3)]
            Polynomial : -11/24
            <BLANKLINE>
            Graph :      [1, 1] [[2], [3]] [(2, 3)]
            Polynomial : -11/24

            sage: R = TautologicalRing(1, 1)
            sage: (-1)^1 * R.cotangent_chern_class(1).evaluate()  # = chiorb(Mbar_1,1)
            5/12

            sage: R = TautologicalRing(0, 4)
            sage: (-1)^1 * R.cotangent_chern_class(1).evaluate()  # = chiorb(Mbar_0,4)
            2
        """
        from admcycles.chernclasses import chernclass
        return self(chernclass(self._g, self._n, d))

    def log_cotangent_chern_class(self, d):
        r"""
        Return the d-th Chern class of the logarithmic cotangent bundle of the moduli space.

        The logarithmic cotangent bundle is the cotangent bundle with logarithmic poles along
        the boundary divisors.

        These classes are also related to double ramification cycles with specific parameters.

        INPUT:

        - ``d`` -- non-negative integer; degree of the Chern class

        OUTPUT:

        A tautological class representing the d-th Chern class of the logarithmic cotangent bundle.

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(2, 0)
            sage: R.log_cotangent_chern_class(1)
            Graph :      [2] [[]] []
            Polynomial : 13/12*(kappa_1)_0
            <BLANKLINE>
            Graph :      [1] [[2, 3]] [(2, 3)]
            Polynomial : 1/24
            <BLANKLINE>
            Graph :      [1, 1] [[2], [3]] [(2, 3)]
            Polynomial : 1/24

            sage: R = TautologicalRing(1, 1)
            sage: (-1)^1 * R.log_cotangent_chern_class(1).evaluate()  # = chiorb(Mcal_1,1)
            -1/12

            sage: from admcycles.double_ramification_cycle import DR_cycle
            sage: R = TautologicalRing(1, 2)
            sage: d = 2
            sage: A = R.log_cotangent_chern_class(d)
            sage: B = (-1)**d * DR_cycle(1, [0, 0], chiodo_coeff=True, k=-1, r_coeff=1, d=d)
            sage: A == B
            True

            sage: for g, n in [(0,4), (1,1), (2,0)]:
            ....:     dim = 3*g-3+n
            ....:     R = TautologicalRing(g, n)
            ....:     print(g, n, R.log_cotangent_chern_class(dim).evaluate())
            0 4 1
            1 1 1/12
            2 0 1/240
        """
        from admcycles.chernclasses import chernlogclass
        return self(chernlogclass(self._g, self._n, d))

    def differential_stratum(self, k, mu, virt=False, res_cond=(), xi_power=0, method='pull'):
        r"""
        Return the fundamental class of the closure of the stratum of ``k``-differentials
        with vanishing and pole orders ``mu``.

        For more information see the documentation of :func:`~admcycles.stratarecursion.Strataclass`.

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: R = TautologicalRing(1,2)
            sage: H1 = R.differential_stratum(1,(1, -1))
            sage: H1.is_zero()
            True
            sage: H5 = R.differential_stratum(1,(5, -5))
            sage: H5.forgetful_pushforward([2]).fund_evaluate()
            24
        """
        if len(mu) != self._n:
            raise ValueError('the length of partition mu must equal the total number of marked points')
        from .stratarecursion import Strataclass
        return self(Strataclass(self._g, k, mu, virt=virt, res_cond=res_cond, xi_power=xi_power, method=method))

    identify_class = identify_class

    def presentation(self, generators=None, assume_FZ=True, eliminate_generators=None, output='pres'):
        r"""
        Computes a presentation of the tautological ring as a quotient of
        a polynomial ring by an ideal, where the generators of the polynomial
        ring are sent to the given generators.

        The function returns the above ideal in a polynomial ring together with
        a ring homomorphism. Assumes FZ relations are sufficient unless otherwise
        instructed.

        INPUT:

        - generators (list) --- optional, if provided we will use the given
          elements as ring generators (it is the user's responsibility to check
          they generate as an algebra)
        - elimimate_generators (bool) --- optional, decides whether to keep around unnecessary ring generators.
        - output (str) --- optional. Can be::
            'pres', in which case returns a surjecion from a polynomial ring to self, and an ideal of that ring (the kernel)
            'lists', in which case it returns generators for the ideal, then lists of generators for R and a correspondng list of generators for TR.
            'fun', in which case it returns an ideal, a rung hom from free polynomial ring to self, and a function from self to free polynomial ring (a lift). This does not allow the user to choose their own basis.

        EXAMPLES::

            sage: from admcycles import TautologicalRing
            sage: TR = TautologicalRing(2,0)
            sage: I, f = TR.presentation()
            sage: R = I.ring()
            sage: I == R.ideal([2*R.0*R.1 + R.1^2, 40*R.0^3 - 43*R.1^3, R.1^4])
            True
            sage: R.ngens()
            2
            sage: I, f = TR.presentation(eliminate_generators = False)
            sage: R = I.ring()
            sage: R.ngens()
            5

        By specifying generators lambda_1 and delta_1, we can check a result by
        Faber.::

            sage: gens = (TR.lambdaclass(1), 1/2*TR.sepbdiv(1,()))
            sage: I, f = TR.presentation(gens)
            sage: R = I.ring()
            sage: x0, x1 = R.gens()
            sage: I == R.ideal([x1^2 + x0*x1, 5*x0^3 - x0^2 * x1])
            True
            sage: r = f(x1^2 + x0*x1)
            sage: r.is_zero()
            True

        Going to the locus of smooth curves, we check Theorem 1.1 in [CanLars]_ by Canning-Larson (we correct the exponent of kap1 in the last term).::

            sage: TR = TautologicalRing(7, 0, moduli = 'sm')
            sage: gens = (TR.kappa(1), TR.kappa(2))
            sage: I, f = TR.presentation(gens)
            sage: R = I.ring(); R
            Multivariate Polynomial Ring in x0, x1 over Rational Field
            sage: kap1, kap2 = R.gens()
            sage: idgens = [2423*kap1^2*kap2 - 52632*kap2^2, 1152000*kap2^2 - 2423*kap1^4, 16000*kap1^3*kap2 - 731*kap1^5]
            sage: I == R.ideal(idgens)
            True

        Theorem 1.2 in [CanLars]_ (we correct the signs in the first term).::

            sage: TR = TautologicalRing(8, 0, moduli = 'sm')
            sage: gens = (TR.kappa(1), TR.kappa(2))
            sage: I, f = TR.presentation(gens)
            sage: R = I.ring(); R
            Multivariate Polynomial Ring in x0, x1 over Rational Field
            sage: kap1, kap2 = R.gens()
            sage: idgens = [714894336*kap2^2 - 55211328*kap1^2*kap2 + 1058587*kap1^4, 62208000*kap1*kap2^2 - 95287*kap1^5, 144000*kap1^3*kap2 - 5617*kap1^5]
            sage: I == R.ideal(idgens)
            True

        Theorem 1.3 in [CanLars]_ (corrected the last coefficient of the third generator).::

            sage: TR = TautologicalRing(9, 0, moduli = 'sm')
            sage: gens = (TR.kappa(1), TR.kappa(2), TR.kappa(3))
            sage: I, f = TR.presentation(gens)
            sage: R = I.ring(); R
            Multivariate Polynomial Ring in x0, x1, x2 over Rational Field
            sage: kap1, kap2, kap3 = R.gens()
            sage: idgens = [5195*kap1^4 + 3644694*kap1*kap3 + 749412*kap2^2 - 265788*kap1^2*kap2, 33859814400*kap2*kap3 - 95311440*kap1^3*kap2 + 2288539*kap1^5, 19151377*kap1^5 + 16929907200*kap1*kap2^2 - 1142345520*kap1^3*kap2,  1422489600*kap3^2 - 983*kap1^6, 1185408000*kap2^3 - 47543*kap1^6]
            sage: I == R.ideal(idgens)
            True

        """
        if not assume_FZ:
            return NotImplementedError("Need to insert a step checking FZ conjecture here. ")
        if output == 'fun' and generators is not None:
            return NotImplementedError('if you want an inverse, please let me choose my own generators for now. Otherwise I would have to do a bit of linear algebra... ')
        if generators is None:
            generators = self.basis()
            if eliminate_generators is None:
                eliminate_generators = True
        if eliminate_generators is None:
            eliminate_generators = False
        if output in ['lists', 'fun']:
            eliminate_generators = False
        gens = []
        gen_degree_list = []
        for gen in generators:
            if not len(gen.degree_list()) == 1:
                return NotImplementedError("So far needs to assume the generators are homogeneous. ")
            m = max(gen.degree_list())
            if not m == 0:
                gens.append(gen)
                gen_degree_list.append(m)
        T = TermOrder("wdeglex", gen_degree_list)
        ngens = len(gens)
        R = PolynomialRing(QQ, 'x', ngens, order=T)
        x = R.gens()
        maxdeg = self.socle_degree()
        LL = [WeightedIntegerVectors(maxdeg + i + 1, gen_degree_list) for i in range(max(gen_degree_list))]
        LL2 = [a for b in LL for a in b]
        # NOTE: this is not maximally efficient, I guess
        deg_ideal = R.ideal([R({tuple(a): 1}) for a in LL2])
        ideal_gens = []
        for deg in range(1, maxdeg + 1):
            exponent_tuples_to_try = WeightedIntegerVectors(deg, gen_degree_list)
            taut_monomials_to_try = [prod([gens[i]**w[i] for i in range(len(gens))]) for w in exponent_tuples_to_try]
            poly_monomials_to_try = [R({tuple(w): 1}) for w in exponent_tuples_to_try]
            # NOTE: need to specify the degree, as some elements may be zero!
            rels = matrix([m.basis_vector(deg) for m in taut_monomials_to_try]).kernel().gens()
            for r in rels:
                P = sum([r[i] * poly_monomials_to_try[i] for i in range(len(r))])
                ideal_gens.append(P)
        genlist = (R.ideal(ideal_gens) + deg_ideal).groebner_basis()
        elimlist = []
        for i in range(ngens):
            i = ngens - i - 1
            elim = False
            for f in genlist:
                if not f.coefficient(x[i]) == 0 and f.coefficient(x[i]).is_constant():
                    elim = True
                    elimlist.append(i)
                    break
            if elim:
                I = R.ideal(genlist).elimination_ideal(x[i])
                genlist = I.gens()
        if eliminate_generators:
            for i in elimlist:
                R = R.remove_var(x[i], order='degrevlex')
                gens.pop(i)
        II = R.ideal(list(genlist))
        if output == 'pres':
            Rhom = R.hom(gens, self)
            return II, Rhom
        if output == 'lists':
            return II, gens, R.gens()
#            return II, gens[i]:R.gens()[i] for i in range(ngens)}, {R.gens()[i]:gens[i] for i in range(ngens)}
        if output == 'fun':
            Rhom = R.hom(gens, self)

            def f(tautelt):
                polyelt = 0
                gennum = 0
                for d in range(1, self.socle_degree()):
                    vd = tautelt.basis_vector(d)
                    polyelt += sum([vd[i] * R.gens()[i + gennum] for i in range(len(vd))])
                    gennum += len(vd)
                return polyelt + tautelt.basis_vector(0)[0]
            return II, Rhom, f


class TautologicalRingFunctor(ConstructionFunctor):
    r"""
    Construction functor for tautological ring.

    This class is the way to implement the "promotion of base ring" (see below in the examples).

    EXAMPLES::

        sage: from admcycles.tautological_ring import TautologicalRing, TautologicalRingFunctor
        sage: F = TautologicalRingFunctor(1, (1,), 'st')
        sage: F(QQ)
        TautologicalRing(g=1, n=1, moduli='st') over Rational Field

        sage: x = polygen(QQ, 'x')
        sage: (x**2 + 2) * TautologicalRing(1, 1).generators(1)[0]
        Graph :      [1] [[1]] []
        Polynomial : (x^2 + 2)*(kappa_1)_0
    """
    rank = 10

    def __init__(self, g, markings, moduli):
        Functor.__init__(self, _CommutativeRings, _CommutativeRings)
        self.g = g
        self.markings = markings
        self.moduli = moduli

    def _repr_(self):
        return 'TautologicalRingFunctor(g={}, n={}, moduli={!r})'.format(
            self.g, self.markings, _moduli_to_str[self.moduli])

    def _apply_functor(self, R):
        return TautologicalRing(self.g, self.markings, self.moduli, base_ring=R)

    def merge(self, other):
        r"""
        Return the merge of two tautological ring functors.
        """
        if isinstance(other, TautologicalRingFunctor) and \
                self.g == other.g and \
                self.markings == other.markings:
            return TautologicalRingFunctor(self.g, self.markings, min(self.moduli, other.moduli))

    def __eq__(self, other):
        return isinstance(other, TautologicalRingFunctor) and \
            self.g == other.g and \
            self.markings == other.markings and \
            self.moduli == other.moduli

    def __ne__(self, other):
        return not (self == other)

    __hash__ = ConstructionFunctor.__hash__
