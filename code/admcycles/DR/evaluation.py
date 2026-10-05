r"""
Evaluation of integrals of cohomology classes against the fundamental class
"""

from sage.misc.cachefunc import cached_function
from sage.rings.integer_ring import ZZ
from sage.combinat.subset import Subsets
from sage.arith.misc import bernoulli, multinomial


from .moduli import MODULI_ST, MODULI_CT, MODULI_RT, MODULI_SM, dim_form
from .utils import setparts_with_auts
from .graph import single_stratum


def socle_evaluation(num, g, markings=(), moduli_type=MODULI_ST):
    r"""
    EXAMPLES::

        sage: from admcycles.DR.graph import num_strata
        sage: from admcycles.DR.moduli import MODULI_ST
        sage: from admcycles.DR.evaluation import socle_evaluation
        sage: g = 2
        sage: markings = (1,)
        sage: for i in range(num_strata(g, 3*g-3+len(markings), (1,))):
        ....:     print(i, socle_evaluation(i, g, markings, MODULI_ST))
        0 1/1152
        1 13/1920
        2 53/5760
        3 259/5760
        4 29/128
        5 1/384
        6 101/5760
        7 169/1920
        8 29/5760
        9 139/5760
        10 29/5760
        11 1/1152
        12 1/576
        ...
        76 2
        77 2
        78 1
        79 1
        80 1
        81 1
        82 1
        83 1
        84 1
        85 1
        86 1
        87 1
        88 1
        89 1
        90 1
        91 1
    """
    answer = 1
    G = single_stratum(num, g, dim_form(
        g, len(markings), moduli_type), markings, moduli_type)
    for i in range(1, G.M.nrows()):
        g0 = G.M[i, 0][0]
        psilist = []
        for j in range(1, G.M.ncols()):
            if G.M[i, j][0] > 0:
                psilist.append(G.M[i, j][1])
                if G.M[i, j][0] == 2:
                    psilist.append(G.M[i, j][2])
        n0 = len(psilist)
        dim0 = dim_form(g0, n0, moduli_type)
        kappalist = []
        for j in range(1, dim0 + 1):
            for k in range(G.M[i, 0][j]):
                kappalist.append(j)
        if sum(psilist) + sum(kappalist) != dim0:
            raise ValueError("wrong dimension")
        answer *= socle_formula(g0, psilist, kappalist, moduli_type)
    return answer


def socle_formula(g, psilist, kappalist, moduli_type=MODULI_ST):
    r"""
    Return the integral of a product of kappa and psi classes.

    EXAMPLES::

        sage: from admcycles.DR.evaluation import socle_formula
        sage: from admcycles.DR.moduli import MODULI_SM, MODULI_RT, MODULI_CT, MODULI_ST

        sage: socle_formula(4, [], [2], MODULI_SM)
        1/3225600
        sage: socle_formula(4, [], [1, 1], MODULI_SM)
        1/302400
        sage: socle_formula(3, [0], [2], MODULI_SM)
        1/120960
        sage: socle_formula(3, [0], [1, 1], MODULI_SM)
        1/13440
        sage: socle_formula(3, [1], [1], MODULI_SM)
        1/24192
        sage: socle_formula(3, [2], [], MODULI_SM)
        1/120960

        sage: socle_formula(3, [0], [2], MODULI_RT)
        1/120960
        sage: socle_formula(3, [0], [1, 1], MODULI_RT)
        1/13440
        sage: socle_formula(3, [1], [1], MODULI_RT)
        1/24192
        sage: socle_formula(3, [2], [], MODULI_RT)
        1/120960

        sage: socle_formula(4, [], [5], MODULI_CT)
        127/154828800
        sage: socle_formula(4, [], [1, 4], MODULI_CT)
        127/7741440
        sage: socle_formula(4, [], [2, 3], MODULI_CT)
        2159/77414400
        sage: socle_formula(4, [], [1, 1, 1, 1, 1], MODULI_CT)
        3171571/77414400

        sage: socle_formula(3, [], [6], MODULI_ST)
        1/82944
        sage: socle_formula(3, [], [1, 5], MODULI_ST)
        1/5760
        sage: socle_formula(3, [], [2, 4], MODULI_ST)
        971/2903040
        sage: socle_formula(3, [], [1, 1, 4], MODULI_ST)
        2173/967680
        sage: socle_formula(3, [], [1, 1, 1, 1, 1, 1], MODULI_ST)
        176557/107520
    """
    degree = sum(psilist) + sum(kappalist)
    n = len(psilist)
    if moduli_type == MODULI_SM:
        if degree != g - 1 + (g == 0) - (n == 0):
            raise ValueError("invalid degree")
    elif moduli_type == MODULI_RT:
        if degree != g - 2 + n - (g == 0):
            raise ValueError("invalid degree")
    elif moduli_type == MODULI_CT:
        if degree != 2 * g - 3 + n:
            raise ValueError("invalid degree")
    elif moduli_type == MODULI_ST:
        if degree != 3 * g - 3 + n:
            raise ValueError("invalid degree")

    if moduli_type == MODULI_CT or g == 0:
        return CTconst(g) * CTsum(psilist, kappalist)
    if moduli_type <= MODULI_SM or moduli_type == MODULI_RT:
        return RTconst(g) * RTsum(g, psilist, kappalist)
    if moduli_type == MODULI_ST:
        return STsum(psilist, kappalist)


def multi2(g, sigma):
    r"""
    EXAMPLES::

        sage: from admcycles.DR.evaluation import multi2
        sage: multi2(3, [3, 0])
        1
        sage: multi2(3, [2])
        1
        sage: multi2(3, [2, 2, 0])
        10
    """
    sigma.sort()
    if sigma[0] == 0:
        total = ZZ.zero()
        for i in range(len(sigma) - 1):
            sigmacopy = sigma[1:]
            if sigmacopy[i] > 0:
                sigmacopy[i] -= 1
                total += multi2(g, sigmacopy)
        return total
    term = ZZ(2 * g - 3 + len(sigma)).factorial()
    term *= ZZ(2 * g - 1).multifactorial(2)
    term /= ZZ(2 * g - 1).factorial()
    for i in sigma:
        term /= ZZ(2 * i - 1).multifactorial(2)
    return term


def STsum(psilist, kappalist):
    kappalist.sort()
    total = 0
    for i0, i1 in setparts_with_auts(kappalist):
        total += (-1)**(len(i0)) * i1 * \
            STrecur([1 + sum(j) for j in i0] + psilist)
    return total * (-1)**(len(kappalist))


def RTsum(g, psilist, kappalist):
    kappalist.sort()
    total = ZZ.zero()
    for i0, i1 in setparts_with_auts(kappalist):
        total += (-1) ** len(i0) * i1 * \
            multi2(g, [1 + sum(j) for j in i0] + psilist)
    return total * (-1)**(len(kappalist))


def CTsum(psilist, kappalist):
    kappalist.sort()
    total = ZZ.zero()
    for i0, i1 in setparts_with_auts(kappalist):
        total += (-1)**len(i0) * i1 * \
            multinomial([1 + sum(j) for j in i0] + psilist)
    return total * (-1)**len(kappalist)


def CTconst(g):
    """
    Sequence of rational numbers related to Bernoulli numbers.

    INPUT: an integer g

    OUTPUT: a rational

    EXAMPLES::

        sage: from admcycles.DR.evaluation import CTconst
        sage: [CTconst(g) for g in range(12)]
        [1,
         1/24,
         7/5760,
         31/967680,
         127/154828800,
         73/3503554560,
         1414477/2678117105664000,
         8191/612141052723200,
         16931177/49950709902213120000,
         5749691557/669659197233029971968000,
         91546277357/420928638260761696665600000,
         3324754717/603513268363481705349120000]
    """
    gg = 2 * ZZ(g)
    power = ZZ(2)**(gg - 1)
    return ((power - 1) * bernoulli(gg)).abs() / (power * ZZ(gg).factorial())


@cached_function
def RTconst(g):
    r"""
    Universal constant computing the intersection number

    \int_{Mbar_{g,n}} \psi_1^{g-1} \lambda_g \lambda_{g-1}.

    EXAMPLES::

        sage: from admcycles.DR.evaluation import RTconst
        sage: [RTconst(g) for g in range(12)]
        [1,
         1/24,
         1/2880,
         1/120960,
         1/3225600,
         1/63866880,
         691/697426329600,
         1/13284311040,
         3617/541999890432000,
         43867/64877386884710400,
         174611/2265559542005760000,
         77683/7958292791191142400]

    TESTS::

        sage: from admcycles import TautologicalRing
        sage: R = TautologicalRing(1,1)
        sage: (R.psi(1)^0*R.lambdaclass(1)*R.lambdaclass(0)).evaluate()
        1/24
        sage: R = TautologicalRing(2,1)
        sage: (R.psi(1)^1*R.lambdaclass(2)*R.lambdaclass(1)).evaluate()
        1/2880
        sage: R = TautologicalRing(3,1)
        sage: (R.psi(1)^2*R.lambdaclass(3)*R.lambdaclass(2)).evaluate()
        1/120960
    """
    if g == 0:
        return ZZ(1)
    return (bernoulli(2 * ZZ(g))).abs() / (2**(2 * g - 1) * ZZ(2 * g - 1).multifactorial(2) * 2 * g)


def STrecur(psi):
    """
    Integral of psi classes.

    INPUT: a sorted tuple of nonegative integers

    OUTPUT: a rational

    EXAMPLES::

        sage: from admcycles.DR.evaluation import STrecur
        sage: STrecur((0, 0, 0))
        1
        sage: STrecur((1,))
        1/24
        sage: STrecur((4,))
        1/1152
        sage: STrecur((7,))
        1/82944
        sage: STrecur((2,) * 3)
        7/240
        sage: STrecur((2,) * 6)
        1225/144
        sage: STrecur((1,) * 3)
        1/12
    """
    return STrecur_calc(tuple(sorted(psi)))


@cached_function
def STrecur_calc(psi):
    if not psi:
        return ZZ.one()
    s = sum(psi)
    n = len(psi)
    if (s - n) % 3:
        return ZZ.zero()
    if psi[0] == 0:
        if s == 0 and n == 3:
            return ZZ.one()
        total = ZZ.zero()
        psi_end = list(psi[1:])
        for i in range(n - 1):
            psicopy = list(psi_end)
            if psicopy[i] > 0:
                psicopy[i] -= 1
                total += STrecur(psicopy)
        return total

    g = ZZ(s - n) // 3 + 1  # in ZZ
    d = ZZ(psi[-1])
    total = ZZ.zero()

    psicopy = [0, 0, 0, 0] + list(psi)
    psicopy[-1] += 1
    total += (2 * d + 3) / 12 * STrecur(psicopy)

    psicopy = [0, 0, 0] + list(psi)
    total -= (2 * g + n - 1) / 6 * STrecur(psicopy)

    for I in Subsets(list(range(n - 1))):
        # 3g - 3 + n
        nI = len(I) + 2
        degI = sum(psi[i] for i in I)
        if (degI - nI) % 3 != 0:
            continue
        gI = (degI - nI) // 3 + 1
        if 2 * gI - 2 + nI <= 0:
            continue
        psi3 = [0, 0] + [psi[i] for i in I]
        x = STrecur(psi3)
        if not x:
            raise ValueError
        psi1 = [0, 0] + [psi[i] for i in range(n - 1) if i not in I] + [d + 1]
        psi2 = list(psi1[1:])
        psi2[-1] = d
        total += ((2 * d + 3) * STrecur(psi1) -
                  (2 * g + n - 1) * STrecur(psi2)) * x
    total /= (2 * g + n - 1) * (2 * g + n - 2)
    return total
