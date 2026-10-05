r"""
Mixcellaneous functions
"""
from sage.rings.integer_ring import ZZ
from sage.rings.rational_field import QQ
from sage.combinat.subset import Subsets
from sage.combinat.combination import Combinations


ENABLE_DPRINT = True
ENABLE_DSAVE = False

A_list = [ZZ(6 * n).factorial() / (ZZ(3 * n).factorial() * ZZ(2 * n).factorial())
          for n in range(100)]
B_list = [ZZ(6 * n + 1).factorial() / ((6 * n - 1) * ZZ(3 * n).factorial() * ZZ(2 * n).factorial())
          for n in range(100)]


def get_memory_usage():
    """
    Return the memory usage of the current process in megabytes.

    This function was part of sage.misc.getusage but the module was
    removed in sage 9.5

    OUTPUT: a float representing the number of megabytes used.

    EXAMPLES::

        sage: from admcycles.DR.utils import get_memory_usage
        sage: t = get_memory_usage(); t  # random
        873.98046875
        sage: type(t)
        <... 'float'>
    """
    import psutil
    return psutil.Process().memory_info().vms / float(1048576)


def dprint(string, *args):
    if ENABLE_DPRINT:
        print(string % args)


def dsave(string, *args):
    if ENABLE_DSAVE:
        from sage.misc.persist import save
        save(0, string % args)


def aut(L):
    """
    Return the cardinality of the automorphism group of the list ``L``.

    EXAMPLES::

       sage: from admcycles.DR.utils import aut
       sage: aut([])
       1
       sage: aut([4,1,3,2])
       1
       sage: aut([4,5,6,5,4,4,6])
       24
    """
    if not L:
        return ZZ.one()
    L.sort()
    total = ZZ.one()
    n = 1
    last = L[0]
    for l in L[1:]:
        if l == last:
            n += 1
            total *= n
        else:
            n = 1
            last = l
    return total


def remove_duplicates(L):
    """
    Remove duplicate elements in a list ``L``.

    One cannot use ``set(L)`` because the elements of ``L`` are not hashable.

    INPUT:

    - ``L`` -- a list

    OUTPUT:

    a list

    EXAMPLES::

       sage: from admcycles.DR.utils import remove_duplicates
       sage: remove_duplicates([4,7,6,4,3,3,4,2,2,1])
       [1, 2, 3, 4, 6, 7]
    """
    if not L:
        return L
    L.sort()
    LL = [L[0]]
    for i, Li in enumerate(L[1:]):
        if Li != L[i]:
            LL.append(Li)
    return LL


def subsequences(n, l, symm):
    """
    Return all subsequences of length ``l`` of ``n`` points with symmetry in the first ``symm`` points.

    EXAMPLES::

        sage: from admcycles.DR.utils import subsequences
        sage: subsequences(5,2,2)
        [[2, 3], [2, 4], [3, 4], [1, 2], [1, 3], [1, 4], [1, 1]]
    """
    sym = max(symm, 1)
    answer = []
    for ones in range(min(l, sym) + 1):
        for others in Subsets(tuple(range(2, n - sym + 2)), l - ones):
            answer.append([1 for _ in range(ones)] + sorted(list(others)))
    return answer


def interpolate(A, B, var='x'):
    r"""
    Univariate Lagrange interpolation over the rationals.

    EXAMPLES::

        sage: from admcycles.DR.utils import interpolate
        sage: p = interpolate([1/2, -2, 3], [4/5, 2/3, -7/6])
        sage: p(1/2)
        4/5
        sage: p(-2)
        2/3
        sage: p(3)
        -7/6

    TESTS::

        sage: from admcycles.DR.utils import interpolate
        sage: parent(interpolate([], []))
        Univariate Polynomial Ring in x over Rational Field
        sage: parent(interpolate([], [], 'r'))
        Univariate Polynomial Ring in r over Rational Field
    """
    if len(A) != len(B):
        raise ValueError
    return QQ[var].lagrange_polynomial(zip(A, B))


def simplify_sparse(vec):
    """
    Collect coefficients in a list of pairs (index, coefficient).

    This also sorts the indices and removes indices with zero coefficient.

    EXAMPLES::

        sage: from admcycles.DR.utils import simplify_sparse
        sage: simplify_sparse([('b',6),('a',1),('c',2),('a',-1),('b',5)])
        [['b', 11], ['c', 2]]
    """
    vec.sort()
    vec2 = []
    last_index = None
    for index, coeff in vec:
        if index == last_index:
            if vec2[-1][1] == -coeff:
                vec2.pop()
                last_index = None
            else:
                vec2[-1][1] += coeff
        else:
            vec2.append([index, coeff])
            last_index = index
    return vec2


def setparts_recur(symlist, progress):
    if not symlist:
        yield progress
        return
    for i in Combinations(symlist[1:]):
        j = [symlist[0]] + i
        if progress and j < progress[-1]:
            continue
        cur = 0
        new_symlist = []
        for sym_k in symlist:
            if cur < len(j) and sym_k == j[cur]:
                cur += 1
            else:
                new_symlist.append(sym_k)
        yield from setparts_recur(new_symlist, progress + [j])


def setparts_with_auts(symlist):
    r"""
    Iterate through the pairs ``(part, aut)`` where ``part`` is a set
    partition of ``symlist`` and ``aut`` is its number of
    automorphisms.

    EXAMPLES::

        sage: from admcycles.DR.utils import setparts_with_auts

        sage: list(setparts_with_auts(symlist=[1]))
        [([[1]], 1)]
        sage: list(setparts_with_auts(symlist=[2]))
        [([[2]], 1)]
        sage: list(setparts_with_auts(symlist=[1, 1]))
        [([[1], [1]], 1), ([[1, 1]], 1)]
        sage: list(setparts_with_auts(symlist=[3]))
        [([[3]], 1)]
        sage: list(setparts_with_auts(symlist=[1, 2]))
        [([[1], [2]], 1), ([[1, 2]], 1)]
        sage: list(setparts_with_auts(symlist=[1, 1, 1]))
        [([[1], [1], [1]], 1), ([[1], [1, 1]], 3), ([[1, 1, 1]], 1)]
    """
    a = aut(symlist)
    for i in setparts_recur(symlist, []):
        b = aut(i)
        for j in i:
            b *= aut(j)
        yield (i, a // b)
