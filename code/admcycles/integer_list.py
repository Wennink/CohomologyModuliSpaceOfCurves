r"""
Various iterators on integer lists.

The most notable functions in this module are

- :func:`ordered_set_partitions`: iterator through the ordered set
  partitions of `range(n)` of fixed part sizes
- :func:`multiset_permutations`: iterator through the permutations
  of the elements of a list with possibly repeated elements
- :func:`integer_lists_lex`: iterator through the integer lists
  of fixed length with lower and upper bound constraints on sum
  and individual entries
- :func:`orbit_representatives`: naive implementation of the
  computation of a set of representatives for a group action
- :func:`integer_lists_mod_perm_group`: an efficient implementation
  of `orbit_representatives` for group actions on integer lists
  by permutation
"""

import collections
import itertools

from sage.libs.gap.libgap import libgap


def is_trivial_group(group):
    r"""
    Return whether ``group`` is a trivial group.
    """
    return group is None or all(g.is_one() for g in group.gens())


def multiset_permutation_to_ordered_set_partition(l, m):
    p = [[] for _ in range(m)]
    for i, j in enumerate(l):
        p[j].append(i)
    return p


def ordered_set_partitions(part_sizes):
    r"""
    A faster version of sage ``OrderedSetPartitions``.

    See https://gitlab.com/modulispaces/admcycles/-/issues/100.

    EXAMPLES::

        sage: from admcycles.integer_list import ordered_set_partitions
        sage: [list(map(list, x)) for x in OrderedSetPartitions(range(5), [2,1,2]).list()] == list(ordered_set_partitions([2, 1, 2]))
        True
    """
    l = []
    for i, j in enumerate(part_sizes):
        l.extend([i] * j)
    yield multiset_permutation_to_ordered_set_partition(l, len(part_sizes))
    while multiset_permutation_next_lex(l):
        yield multiset_permutation_to_ordered_set_partition(l, len(part_sizes))


def multiset_permutation_next_lex(l):
    r"""
    EXAMPLES::

        sage: from admcycles.integer_list import multiset_permutation_next_lex
        sage: l = [0, 0, 1, 1, 2]
        sage: while multiset_permutation_next_lex(l):
        ....:     print(l)
        [0, 0, 1, 2, 1]
        [0, 0, 2, 1, 1]
        [0, 1, 0, 1, 2]
        [0, 1, 0, 2, 1]
        [0, 1, 1, 0, 2]
        [0, 1, 1, 2, 0]
        ...
        [1, 1, 2, 0, 0]
        [1, 2, 0, 0, 1]
        [1, 2, 0, 1, 0]
        [1, 2, 1, 0, 0]
        [2, 0, 0, 1, 1]
        [2, 0, 1, 0, 1]
        [2, 0, 1, 1, 0]
        [2, 1, 0, 0, 1]
        [2, 1, 0, 1, 0]
        [2, 1, 1, 0, 0]
    """
    i = len(l) - 2
    while i >= 0 and l[i] >= l[i + 1]:
        i -= 1
    if i == -1:
        return 0
    j = len(l) - 1
    while l[j] <= l[i]:
        j -= 1
    l[i], l[j] = l[j], l[i]
    l[i + 1:] = l[:i:-1]
    return 1


def multiset_permutations(l):
    r"""
    Iterator through the multiset permutations of ``l``.

    EXAMPLES::

        sage: from admcycles.integer_list import multiset_permutations
        sage: list(multiset_permutations([0, 0, 1]))
        [[0, 0, 1], [0, 1, 0], [1, 0, 0]]
        sage: list(multiset_permutations([0, 1, 1]))
        [[0, 1, 1], [1, 0, 1], [1, 1, 0]]
        sage: list(multiset_permutations([0, 1, 0, 1]))
        [[0, 0, 1, 1], [0, 1, 0, 1], [0, 1, 1, 0], [1, 0, 0, 1], [1, 0, 1, 0], [1, 1, 0, 0]]
    """
    l = sorted(l)
    yield l[:]
    while multiset_permutation_next_lex(l):
        yield l[:]


def integer_lists_lex(min_sum, max_sum, floor, ceiling):
    r"""
    Return the list of integers with sum between ``min_sum`` and ``max_sum``,
    lower bound ``floor`` and upper bound ``ceiling`` on their parts.

    Iteration is done lexicographically.

    This is similar to a special case of sage ``IntegerListLex`` though much faster.
    See https://gitlab.com/modulispaces/admcycles/-/issues/99.

    EXAMPLES::

        sage: from admcycles.integer_list import integer_lists_lex
        sage: L1 = list(integer_lists_lex(4, 4, [0]*5, [2, 1, 2, 1, 1]))
        sage: L2 = IntegerListsLex(4, length=5, ceiling=[2, 1, 2, 1, 1], element_constructor=list).list()
        sage: assert L1 == L2[::-1]

        sage: L1 = list(integer_lists_lex(4, 4, [1, 1, 0, 0, 0], [2, 1, 2, 1, 1]))
        sage: L2 = IntegerListsLex(4, length=5, floor=[1, 1, 0, 0, 0], ceiling=[2, 1, 2, 1, 1], element_constructor=list).list()
        sage: assert L1 == L2[::-1]

        sage: L1 = list(integer_lists_lex(2, 5, [1, 1, 0, 0, 0], [2, 1, 2, 1, 1]))
        sage: L2 = IntegerListsLex(min_sum=2, max_sum=5, length=5, floor=[1, 1, 0, 0, 0], ceiling=[2, 1, 2, 1, 1], element_constructor=list).list()
        sage: assert L1 == L2[::-1]

        sage: list(integer_lists_lex(1, 1, [0, 0], [1, 0]))
        [[1, 0]]
        sage: list(integer_lists_lex(0, 2, [0, 0], [1, 0]))
        [[0, 0], [1, 0]]
        sage: list(integer_lists_lex(0, 5, [0, 1, 2], [3, 2, 2]))
        [[0, 1, 2], [0, 2, 2], [1, 1, 2], [1, 2, 2], [2, 1, 2]]

        sage: list(integer_lists_lex(1, 1, [1, 1], [2, 1]))
        Traceback (most recent call last):
        ...
        ValueError: integer_lists_lex_first: empty set
    """
    if len(floor) != len(ceiling):
        raise ValueError('integer_lists_lex: invalid arguments')
    min_sum = max(min_sum, sum(floor))
    max_sum = min(max_sum, sum(ceiling))
    ceiling = [j - i for i, j in zip(floor, ceiling)]
    min_sum -= sum(floor)
    max_sum -= sum(floor)
    l = []
    integer_lists_lex_first(l, min_sum, max_sum, ceiling)
    yield [i + j for i, j in zip(floor, l)]
    while integer_lists_lex_next(l, min_sum, max_sum, ceiling):
        yield [i + j for i, j in zip(floor, l)]


def integer_lists_lex_first(l, min_sum, max_sum, ceiling):
    r"""
    Set ``l`` to the smallest integer list with given constraints.

    EXAMPLES::

        sage: from admcycles.integer_list import integer_lists_lex_first
        sage: l = []
        sage: integer_lists_lex_first(l, 7, 7, [1, 2, 1, 3, 1])
        sage: l
        [0, 2, 1, 3, 1]

        sage: integer_lists_lex_first(l, 1, 0, [1, 1, 1])
        Traceback (most recent call last):
        ...
        ValueError: integer_lists_lex_first: empty set
    """
    if any(i < 0 for i in ceiling) or sum(ceiling) < min_sum or max_sum < min_sum:
        raise ValueError('integer_lists_lex_first: empty set')
    l[:] = [0] * len(ceiling)
    i = len(ceiling) - 1
    n = min_sum
    while n:
        l[i] += min(n, ceiling[i])
        n -= l[i]
        i -= 1


def integer_lists_lex_last(l, min_sum, max_sum, ceiling):
    r"""
    Set ``l`` to the largest integer list with the given constraints.

    EXAMPLES::

        sage: from admcycles.integer_list import integer_lists_lex_last
        sage: l = []
        sage: integer_lists_lex_last(l, 7, 7, [1, 2, 1, 3, 1])
        sage: l
        [1, 2, 1, 3, 0]

        sage: integer_lists_lex_last(l, 1, 0, [1, 1, 1])
        Traceback (most recent call last):
        ...
        ValueError: integer_lists_lex_last: empty set
    """
    if any(i < 0 for i in ceiling) or sum(ceiling) < min_sum or max_sum < min_sum:
        raise ValueError('integer_lists_lex_last: empty set')
    l[:] = [0] * len(ceiling)
    i = 0
    n = max_sum
    while n:
        l[i] += min(n, ceiling[i])
        n -= l[i]
        i += 1


def integer_lists_lex_next(l, min_sum, max_sum, ceiling):
    r"""
    EXAMPLES::

        sage: from admcycles.integer_list import integer_lists_lex_next

        sage: ceiling = [1, 2, 1]
        sage: l = [0, 1, 1]
        sage: print(integer_lists_lex_next(l, 2, 2, ceiling), l)
        True [0, 2, 0]
        sage: print(integer_lists_lex_next(l, 2, 2, ceiling), l)
        True [1, 0, 1]
        sage: print(integer_lists_lex_next(l, 2, 2, ceiling), l)
        True [1, 1, 0]

        sage: ceiling = [1, 2, 1]
        sage: l = [0, 0, 1]
        sage: print(integer_lists_lex_next(l, 1, 3, ceiling), l)
        True [0, 1, 0]
        sage: print(integer_lists_lex_next(l, 1, 3, ceiling), l)
        True [0, 1, 1]
        sage: print(integer_lists_lex_next(l, 1, 3, ceiling), l)
        True [0, 2, 0]
        sage: print(integer_lists_lex_next(l, 1, 3, ceiling), l)
        True [0, 2, 1]
        sage: print(integer_lists_lex_next(l, 1, 3, ceiling), l)
        True [1, 0, 0]
        sage: print(integer_lists_lex_next(l, 1, 3, ceiling), l)
        True [1, 0, 1]
        sage: print(integer_lists_lex_next(l, 1, 3, ceiling), l)
        True [1, 1, 0]
        sage: print(integer_lists_lex_next(l, 1, 3, ceiling), l)
        True [1, 1, 1]
        sage: print(integer_lists_lex_next(l, 1, 3, ceiling), l)
        True [1, 2, 0]
        sage: print(integer_lists_lex_next(l, 1, 3, ceiling), l)
        False [0, 0, 0]
    """
    # NOTE: here we could avoid making this summation and making this
    # function faster. Though this is not the most important part to
    # optimize for now
    s = sum(l)

    i = len(l) - 1
    if s == max_sum:
        # we need to compensate an increase with a decrease:
        # find largest index that we can decrease
        while i >= 0 and not l[i]:
            i -= 1
        if i == -1:
            return False
        s -= l[i]
        l[i] = 0
        i -= 1

    # from i find the largest index that we can increase
    while i >= 0 and l[i] == ceiling[i]:
        s -= l[i]
        l[i] = 0
        i -= 1
    if i == -1:
        return False
    l[i] += 1
    s += 1

    # reset the end so that the vector is at least min_sum
    i = len(l) - 1
    while s < min_sum:
        l[i] = min(min_sum - s, ceiling[i])
        s += l[i]
        i -= 1

    return True


def integer_lists_lex_prev(l, min_sum, max_sum, ceiling):
    r"""
    Set ``l`` to the previous integer vector in lexicographic order.

    EXAMPLES::

        sage: from admcycles.integer_list import integer_lists_lex_next, integer_lists_lex_prev

        sage: l = [1, 1]
        sage: assert integer_lists_lex_next(l, 2, 2, [2, 2])
        sage: assert integer_lists_lex_prev(l, 2, 2, [2, 2])
        sage: assert l == [1, 1]

        sage: l = [0, 0, 1]
        sage: assert integer_lists_lex_prev(l, 0, 2, [1, 1, 1])
        sage: l
        [0, 0, 0]
    """
    s = sum(l)
    i = len(l) - 1
    if s == min_sum:
        # we need to compensate a decrease with an increase:
        # find largest index that we can increase
        while i >= 0 and l[i] == ceiling[i]:
            s -= l[i]
            l[i] = 0
            i -= 1
        if i == -1:
            return False
        s -= l[i]
        l[i] = 0
        i -= 1

    # from i find the largest index that we can decrease
    while i >= 0 and not l[i]:
        i -= 1
    if i == -1:
        return False
    l[i] -= 1
    s -= 1

    # reset the end of the vector
    i += 1
    while i < len(l) and s < max_sum:
        l[i] = min(max_sum - s, ceiling[i])
        s += l[i]
        i += 1

    assert min_sum <= sum(l) <= max_sum and all(x <= y for x, y in zip(l, ceiling))
    return True


def integer_matrices_lex(row_min_sums, row_max_sums, col_min_sums, col_max_sums):
    r"""
    Iterate through the matrices of non-negative integers with entries, row
    sums and column sums restrictions.

    INPUT:

    row_min_sums: a list of ``nrows`` non-negative integers
      lower bounds for row sums

    row_max_sums: a list of ``nrows`` non-negative integers
      upper bounds for row sums

    col_min_sums: a list of ``ncols`` non-negative integers
      lower bounds for column sums

    col_max_sums: a list of ``ncols`` non-negative integers
      upper bounds for column sums

    REFERENCES:

    - Barvinok "Matrices with prescribed rows and column sums" (2012)
    - Brualdi "Combinatorial matrix classes" (2006)
    - Brualdi, Ryser "Combinatorial matrix theory" (1991)

    EXAMPLES::

        sage: from admcycles.integer_list import integer_matrices_lex

    Permutation matrices::

        sage: for mat in integer_matrices_lex([1] * 3, [1] * 3, [1] * 3, [1] * 3):
        ....:     print(mat)
        [[0, 0, 1], [0, 1, 0], [1, 0, 0]]
        [[0, 0, 1], [1, 0, 0], [0, 1, 0]]
        [[0, 1, 0], [0, 0, 1], [1, 0, 0]]
        [[0, 1, 0], [1, 0, 0], [0, 0, 1]]
        [[1, 0, 0], [0, 0, 1], [0, 1, 0]]
        [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
        sage: [sum(1 for _ in integer_matrices_lex([1] * n, [1] * n, [1] * n, [1] * n)) for n in range(1, 6)]
        [1, 2, 6, 24, 120]

    Consistency with filtering and transposition::

        sage: from collections import defaultdict
        sage: for (nrows, ncols) in [(1, 2), (2, 2), (1, 3), (2, 3), (1, 4), (2, 4), (3, 4)]:
        ....:     counter = defaultdict(int)
        ....:     for mat in integer_matrices_lex([0] * nrows, [2] * nrows, [0] * ncols, [2] * ncols):
        ....:         row_sums = tuple(sum(mat[i][j] for j in range(ncols)) for i in range(nrows))
        ....:         col_sums = tuple(sum(mat[i][j] for i in range(nrows)) for j in range(ncols))
        ....:         counter[row_sums, col_sums] += 1
        ....:     for (row_sums, col_sums), num in counter.items():
        ....:         assert sum(1 for _ in integer_matrices_lex(row_sums, row_sums, col_sums, col_sums)) == num
        ....:     transposed_counter = defaultdict(int)
        ....:     for mat in integer_matrices_lex([0] * ncols, [2] * ncols, [0] * nrows, [2] * nrows):
        ....:         row_sums = tuple(sum(mat[i][j] for j in range(nrows)) for i in range(ncols))
        ....:         col_sums = tuple(sum(mat[i][j] for i in range(ncols)) for j in range(nrows))
        ....:         transposed_counter[row_sums, col_sums] += 1
        ....:     for row_sums, col_sums in counter:
        ....:         assert counter[row_sums, col_sums] == transposed_counter[col_sums, row_sums]

    TESTS::

        sage: list(integer_matrices_lex([0,0], [2,1], [1,1,1], [3,3,3]))
        [[[0, 1, 1], [1, 0, 0]], [[1, 0, 1], [0, 1, 0]], [[1, 1, 0], [0, 0, 1]]]
    """
    nrows = len(row_min_sums)
    if len(row_max_sums) != nrows:
        raise ValueError('row_min_sums and row_max_sums must be list of identical lengths')
    ncols = len(col_min_sums)
    if len(col_max_sums) != ncols:
        raise ValueError('col_min_sums and col_max_sums must be list of identical lengths')
    if nrows == 0 or ncols == 0:
        raise ValueError('integer_matrices_lex: empty matrices {} x {}'.format(nrows, ncols))

    # NOTE: there exist a matrix with prescribed row and column sums if and
    # only if the sums coincide!
    smin = max(sum(row_min_sums), sum(col_min_sums))
    smax = min(sum(row_max_sums), sum(col_max_sums))
    if (any(row_max_sums[i] < 0 or row_min_sums[i] > row_max_sums[i] for i in range(nrows)) or
            any(col_max_sums[j] < 0 or col_min_sums[j] > col_max_sums[j] for j in range(ncols)) or
            smin > smax):
        raise ValueError('integer_matrices_lex: empty iteration')

    # handle first trivial cases
    if nrows == 1:
        for row in integer_lists_lex(row_min_sums[0], row_max_sums[0], col_min_sums, col_max_sums):
            yield [row]
        return
    if ncols == 1:
        for col in integer_lists_lex(col_min_sums[0], col_max_sums[0], row_min_sums, row_max_sums):
            yield [[x] for x in col]
        return

    # run through possible row and column sums
    for s in range(smin, smax + 1):
        for row_sums, col_sums in itertools.product(integer_lists_lex(s, s, row_min_sums, row_max_sums),
                                                    integer_lists_lex(s, s, col_min_sums, col_max_sums)):
            yield from integer_matrices_lex_s(row_sums, col_sums)


def integer_matrices_lex_s(row_sums, col_sums):
    if sum(row_sums) != sum(col_sums):
        raise ValueError('integer_matrices_lex_s: empty iterator')

    nrows = len(row_sums)
    ncols = len(col_sums)

    i = 0  # current row index
    matrix = [[0] * ncols for _ in range(nrows)]  # current solution
    dyn_col_sums = list(col_sums)
    while True:
        while i < nrows:
            # update bound and add row
            integer_lists_lex_first(matrix[i], row_sums[i], row_sums[i], dyn_col_sums)
            for j in range(ncols):
                dyn_col_sums[j] -= matrix[i][j]
            i += 1

        assert all(row_sums[ii] == sum(matrix[ii]) for ii in range(nrows))
        assert all(sum(matrix[ii][j] for ii in range(nrows)) == col_sums[j] for j in range(ncols))

        yield [row[:] for row in matrix]

        i -= 1
        for j in range(ncols):
            dyn_col_sums[j] += matrix[i][j]
        while not integer_lists_lex_next(matrix[i], row_sums[i], row_sums[i], dyn_col_sums):
            i -= 1
            if i < 0:
                return
            for j in range(ncols):
                dyn_col_sums[j] += matrix[i][j]

        assert all(row_sums[ii] == sum(matrix[ii]) for ii in range(i))

        for j in range(ncols):
            dyn_col_sums[j] -= matrix[i][j]
        i += 1


def orbit_representatives(group, domain, action, selector=None, return_sizes=False):
    r"""
    Return a set of representatives for the action of ``group`` on ``domain``.

    INPUT:

    group : a sage group

    domain : a collection of hashable elements
      the ground set on which ``group`` acts.

    action : a function with to arguments
      to a pair ``(x, g)`` return the action of the group
      element ``g`` on the element ``x`` of the domain

    selector : optional function of one argument
      if set the function should return a representative
      given the orbit as argument

    return_sizes : boolean (default ``False``)
      if set to ``True`` also return the size of each orbit

    EXAMPLES::

        sage: import itertools
        sage: from admcycles.integer_list import orbit_representatives
        sage: P = PermutationGroup(['(0,1)(2,3)', '(0,2)(1,3)'])
        sage: L = list(itertools.product([0, 1], repeat=4))
        sage: def action(x, g):
        ....:    return tuple(x[g(i)] for i in range(4))
        sage: rep1 = orbit_representatives(P, L, action, selector=min)
        sage: sorted(rep1)
        [(0, 0, 0, 0),
         (0, 0, 0, 1),
         (0, 0, 1, 1),
         (0, 1, 0, 1),
         (0, 1, 1, 0),
         (0, 1, 1, 1),
         (1, 1, 1, 1)]
        sage: rep2 = orbit_representatives(P, L, action, selector=max)
        sage: sorted(rep2)
        [(0, 0, 0, 0),
         (1, 0, 0, 0),
         (1, 0, 0, 1),
         (1, 0, 1, 0),
         (1, 1, 0, 0),
         (1, 1, 1, 0),
         (1, 1, 1, 1)]
        sage: rep3 = orbit_representatives(P, L, action)
        sage: len(rep1) == len(rep2) == len(rep3)
        True

        sage: sorted(orbit_representatives(P, L, action, selector=min, return_sizes=True))
        [((0, 0, 0, 0), 1),
         ((0, 0, 0, 1), 4),
         ((0, 0, 1, 1), 2),
         ((0, 1, 0, 1), 2),
         ((0, 1, 1, 0), 2),
         ((0, 1, 1, 1), 4),
         ((1, 1, 1, 1), 1)]
    """
    if is_trivial_group(group):
        return domain

    if selector is None:
        def selector(arg):
            return next(iter(arg))

    representatives = []
    domain = set(domain)
    while domain:
        x = domain.pop()
        todo = [x]
        orbit = {x}
        while todo:
            x = todo.pop()
            assert x in orbit and x not in domain
            for g in group.gens():
                y = action(x, g)
                if y not in orbit:
                    domain.remove(y)
                    orbit.add(y)
                    todo.append(y)
        representatives.append((selector(orbit), len(orbit)) if return_sizes else selector(orbit))

    return representatives


def stabilizer_chain(group, domain_to_int=None):
    r"""
    Return an increasing stabilizer chain for the permutation ``group``
    together with an inverse list for quick lookup.

    This function is a central tool for :func:`integer_lists_mod_perm_group`.

    The output is a pair ``(transversals, pre)`` where

    - ``transversals`` is a list of lists. Each list ``transversals[i]``
      is non-empty and made of pairs ``(element, permutation)``. The
      first element ``e`` of the first pair is the visited element (and its
      associated permutation is the identity). The rest of the pairs correspond
      to the orbit of ``e`` under the stablizer of `\{0, 1, ..., e-1\}`.
    - ``pre`` is a list of lists of indices of length the degree of ``group``.
      The list ``pre[i]`` consists of the indices ``j`` smaller than ``i``
      that can be permuted with ``i`` under the stabilizer of `\{0, 1, ..., j-1\}`.

    EXAMPLES::

        sage: from admcycles.integer_list import stabilizer_chain

        sage: P = PermutationGroup(['(1,3)(2,4,6)', '(2,4)'])
        sage: t, p = stabilizer_chain(P)
        sage: t
        [[(0, ()), (2, (1,3)(2,6,4))],
         [(1, ()), (3, (2,4)), (5, (2,6,4))],
         [(3, ()), (5, (4,6))]]
        sage: p
        [[], [], [0], [1], [], [1, 3]]

        sage: P = PermutationGroup(['(1,3,5)', '(2,4,6)', '(1,3)', '(2,4)'])
        sage: t, p = stabilizer_chain(P)
        sage: t
        [[(0, ()), (2, (1,3)), (4, (1,5,3))],
         [(1, ()), (3, (2,4)), (5, (2,6,4))],
         [(2, ()), (4, (3,5))],
         [(3, ()), (5, (4,6))]]
        sage: p
        [[], [], [0], [1], [0, 2], [1, 3]]

        sage: t, p = stabilizer_chain(SymmetricGroup(5))
        sage: t
        [[(0, ()), (4, (1,5)), (1, (1,2,5)), (2, (1,3,5)), (3, (1,4,5))],
         [(1, ()), (4, (2,5)), (2, (2,3,5)), (3, (2,4,5))],
         [(2, ()), (4, (3,5)), (3, (3,4,5))],
         [(3, ()), (4, (4,5))]]
        sage: p
        [[], [0], [0, 1], [0, 1, 2], [0, 1, 2, 3]]
    """
    domain = group.domain()
    if domain_to_int is None:
        domain_to_int = {j: i for i, j in enumerate(domain)}
    S = libgap(group)  # stablizer of points already visited
    D = [group._domain_to_gap[p] for p in domain]
    transversals = []  # output
    pre = [[] for _ in D]  # output
    for i, P in enumerate(D):
        if libgap.IsTrivial(S):
            break
        elif all(P == libgap.OnPoints(P, g) for g in libgap.GeneratorsOfGroup(S)):
            continue
        else:
            SS = libgap.Stabilizer(S, P)
            T = libgap.RightTransversal(S, SS)
            transversals.append([(domain_to_int[group._domain_from_gap[int(libgap.OnPoints(P, perm))]], group(perm)) for perm in T])
            for j, _ in transversals[-1][1:]:
                pre[j].append(i)
            S = SS

    # check
    for transversal in transversals:
        i = transversal[0][0]
        assert transversal[0][1].is_one()
        for j, perm in transversal:
            assert perm(domain[i]) == domain[j]
    for i, antecedants in enumerate(pre):
        assert all(k < i for k in antecedants)
    assert all(len(l) == len(set(l)) for l in pre)

    return transversals, pre


# NOTE: this code could end up with the computation of a whole orbit
# sage: P = PermutationGroup(['(1,2)(6,7)', '(1,2,3,4,5)(6,7,8,9,10)'])
# sage: vector_canonical_representative((1, 1, 1, 1, 1, 1, 2, 3, 4, 5), P)
# Is there a better way to deal with non-transitive actions?
def vector_canonical_representative(v, group, sgs, flag=0):
    r"""
    Return a max lex element in the orbit of ``v`` under ``group``.

    With the default ``flag=0`` option, it returns the max lex element.  If
    ``flag=1`` then return whether ``v`` is max lex (output is a boolean).
    This mode is usually faster. If ``flag=2`` then return a pair ``(vmax, p)``
    such that the action of ``p`` on ``v`` gives ``vmax``.

    EXAMPLES::

        sage: from admcycles.integer_list import vector_canonical_representative, stabilizer_chain

        sage: S4 = SymmetricGroup(4)
        sage: sc = stabilizer_chain(S4)
        sage: vector_canonical_representative((1, 2, 3, 1), S4, sc)
        (3, 2, 1, 1)

        sage: t = [1, 4, 3, 2]
        sage: r, p = vector_canonical_representative(t, S4, sc, flag=2)
        sage: p._act_on_list_on_position(t)
        [4, 3, 2, 1]

        sage: vector_canonical_representative((1, 2, 3, 1), S4, sc, flag=1)
        False
        sage: vector_canonical_representative((3, 2, 1, 1), S4, sc, flag=1)
        True
        sage: vector_canonical_representative((2, 2, 2, 1), S4, sc, flag=1)
        True

    TESTS::

        sage: G1 = SymmetricGroup(8)
        sage: G2 = TransitiveGroup(8, 5)
        sage: G3 = PermutationGroup(['(1,3,5,7)(2,4,6,8)', '(1,3)(2,4)'])
        sage: for G in [G1, G2, G3]:
        ....:     sc = stabilizer_chain(G)
        ....:     l = [randint(0, 8) for _ in range(8)]
        ....:     r = vector_canonical_representative(l, G, sc)
        ....:     assert vector_canonical_representative(r, G, sc, flag=1), (G, sc, l, r)
        ....:     for _ in range(10):
        ....:         # TODO: G.random_element() is broken
        ....:         g = G(libgap(G).Random())
        ....:         ll = g._act_on_list_on_position(l)
        ....:         ans, p = vector_canonical_representative(ll, G, sc, flag=2)
        ....:         assert ans == r, (G, l, g, ans)
        ....:         pll = p._act_on_list_on_position(ll)
        ....:         assert pll == list(r), (G, ll, p, pll, r)
    """
    v0 = tuple(v)
    if sgs is None:
        if flag == 0:
            return v0
        elif flag == 1:
            return True
        elif flag == 2:
            return v0, group.one()
        else:
            raise ValueError('invalid flag argument')
    if flag == 0 or flag == 1:
        todo = {v0}
        new_todo = set()
    elif flag == 2:
        todo = {v0: group.one()}
        new_todo = {}
    else:
        raise ValueError('invalid flag argument')

    for transversal in sgs[0]:
        i = transversal[0][0]
        # test whether we can bring a smaller element at position i
        # using the stabilizer of {0, 1, ..., i-1}
        m = max(v[j] for j, _ in transversal for v in todo)
        if flag == 1 and m > v0[i]:
            # better representative
            return False
        for j, p in transversal:
            for v in todo:
                if m == v[j]:
                    child = tuple(p._act_on_list_on_position(list(v)))
                    if flag == 2:
                        new_todo[child] = p * todo[v]
                        assert tuple(new_todo[child]._act_on_list_on_position(list(v0))) == child
                    else:
                        new_todo.add(child)

        todo, new_todo = new_todo, todo
        new_todo.clear()

    representative = max(todo)
    if flag == 0:
        return representative
    if flag == 1:
        return representative == v0
    elif flag == 2:
        return representative, todo[representative]


def integer_lists_mod_perm_group(min_sum, max_sum, floor, ceiling, group=None, sgs=None):
    r"""
    Return an iterator through vectors with sum between ``min_sum`` and ``max_sum``,
    lower bounds ``floor`` and upper bounds ``ceiling`` on their entries modulo the
    action of ``group``.

    The iterator actually yields the vector that are maximal with respect to the
    lexicographic order in their orbit. This is checked via the function
    :func:`vector_canonical_representative`.

    A similar feature is available in sage with
    ``IntegerVectorsModPermutationGroup``.  However this Python implementation
    is more general and faster (even though the sage code is in Cython).
    See https://gitlab.com/modulispaces/admcycles/-/issues/101.

    EXAMPLES::

        sage: from admcycles.integer_list import integer_lists_mod_perm_group
        sage: P = PermutationGroup(['(1,3,4)', '(1,3)', '(2,5,6,7,8,9)'])
        sage: sum(1 for _ in integer_lists_mod_perm_group(0, 27, [0]*9, [3]*9, P))
        14000
        sage: IntegerVectorsModPermutationGroup(P, max_part=3).cardinality()
        14000

        sage: sum(1 for _ in integer_lists_mod_perm_group(0, 24, [0]*8, [3]*8, TransitiveGroup(8, 4)))
        8356
        sage: IntegerVectorsModPermutationGroup(TransitiveGroup(8,4), max_part=3).cardinality()
        8356

    This is something ``IntegerVectorsModPermutationGroup`` can not do yet::

        sage: P = PermutationGroup(['(1,3,5)(2,4,6)', '(1,3)(2,4)'])
        sage: floor = [0, 1, 0, 1, 0, 1]
        sage: ceiling = [1, 3, 1, 3, 1, 3]
        sage: min_sum = 4
        sage: max_sum = 7
        sage: L1 = list(integer_lists_mod_perm_group(min_sum, max_sum, floor, ceiling, P))
        sage: L1
        [[1, 1, 0, 1, 0, 1],
         [0, 2, 0, 1, 0, 1],
         [1, 2, 0, 1, 0, 1],
         [1, 1, 1, 1, 0, 1],
        ...
         [1, 1, 1, 1, 0, 3],
         [1, 1, 0, 3, 0, 2],
         [0, 3, 0, 3, 0, 1],
         [0, 3, 0, 2, 0, 2]]

        sage: L2 = [list(l) for l in IntegerVectorsModPermutationGroup(P, max_part=3) if all(i <= j <= k for i, j, k in zip(floor, l, ceiling)) and min_sum <= sum(l) <= max_sum]
        sage: sorted(L1) == sorted(L2)
        True

    With no group provided, no symmetry is considered::

        sage: list(integer_lists_mod_perm_group(0, 5, [0, 1, 2], [3, 2, 2]))
        [[0, 1, 2], [0, 2, 2], [1, 1, 2], [1, 2, 2], [2, 1, 2]]

    TESTS::

        sage: list(integer_lists_mod_perm_group(0, 0, [], [], None, None))
        [[]]
    """
    if len(floor) != len(ceiling) or (group is not None and len(floor) != len(group.domain())):
        raise ValueError('invalid input')
    if sgs is None:
        if not is_trivial_group(group):
            sgs = stabilizer_chain(group)
        else:
            # NOTE: much faster this way
            yield from integer_lists_lex(min_sum, max_sum, floor, ceiling)
            return

    ceiling = [j - i for i, j in zip(floor, ceiling)]
    min_sum -= sum(floor)
    max_sum -= sum(floor)
    if any(i < 0 for i in ceiling) or sum(ceiling) < min_sum or max_sum < 0:
        raise ValueError('integer_lists_mod_perm_group: empty iteration')

    def canonical_children(v):
        j = len(v) - 1
        while j >= 1 and not v[j]:
            j -= 1
        for i in range(j, len(v)):
            if v[i] < ceiling[i] and all(v[i] < v[k] for k in sgs[1][i]):
                child = v[:]
                child[i] += 1
                if vector_canonical_representative(child, group, sgs, flag=1):
                    yield child

    # NOTE: we could be a bit smarter with the memory footprint. But it
    # probably does not matter.
    todo = collections.deque()
    todo.append([0] * len(floor))
    while todo:
        v = todo.popleft()
        s = sum(v)
        if s >= min_sum:
            yield [i + j for i, j in zip(floor, v)]
        if s < max_sum:
            todo.extend(canonical_children(v))
