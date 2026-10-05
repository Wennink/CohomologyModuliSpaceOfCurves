# -*- coding: utf-8 -*-
r"""
Double ramification cycle

The main function to use to compute DR cycles are the following:

- :func:`DR_compute`
- :func:`DR_sparse`: same as ``DR_compute`` except that it returns the answer as a
  sparse vector
- :func:`DR_reduced`: same as ``DR_compute`` except that it only requires two
  arguments (g and dvector) and simplifies the answer using the 3-spin
  tautological relations.

EXAMPLES::

    sage: from admcycles.DR import DR_compute, DR_sparse, DR_reduced

To compute the genus 1 DR cycle with weight vector (2,-2)::

    sage: DR_compute(1,1,2,(2,-2))
    (0, 2, 2, 0, -1/24)

In the example above, the five classes described on R^1(Mbar_{1,2}) are:
kappa_1, psi_1, psi_2, delta_{12}, delta_{irr}.  (Here by delta_{irr} we mean
the pushforward of 1 under the gluing map Mbar_{0,4} -> Mbar_{1,2}, so twice
the class of the physical locus.)

Sparse version::

    sage: DR_sparse(1,1,2,(2,-2))
    [[1, 2], [2, 2], [4, -1/24]]

Reduced version::

    sage: DR_reduced(1,(2,-2))
    (0, 0, 0, 4, 1/8)
"""

from copy import copy
import itertools

from sage.rings.integer_ring import ZZ
from sage.rings.rational_field import QQ
from sage.functions.other import ceil
from sage.modules.free_module_element import vector

from .moduli import MODULI_ST
from .graph import R, num_strata, single_stratum, autom_count
from .utils import interpolate
from .relations import FZ_rels


def find_nonsep_pairs(num, g, r, markings=(), moduli_type=MODULI_ST):
    G = single_stratum(num, g, r, markings, moduli_type)
    nr = G.M.nrows()
    nc = G.M.ncols()
    answer = []
    for i1 in range(1, nr):
        for i2 in range(1, i1):
            found_edge = False
            for j in range(1, nc):
                if G.M[i1, j] != 0 and G.M[i2, j] != 0:
                    found_edge = True
                    break
            if not found_edge:
                continue
            S = {i1}
            did_something = True
            while did_something:
                did_something = False
                for i3 in tuple(S):
                    for j in range(1, nc):
                        if G.M[i3, j] != 0:
                            for i4 in range(1, nr):
                                if G.M[i4, j] != 0 and i4 not in S and (i3 != i1 or i4 != i2):
                                    S.add(i4)
                                    did_something = True
            if i2 in S:
                answer.append([i2, i1])
    return answer

# assumes r <= 4 for now


def DR_coeff_is_known(num, g, r, markings=(), moduli_type=MODULI_ST):
    return r <= 4

# old stuff
    G = single_stratum(num, g, r, markings, moduli_type)
    nr = G.M.nrows()
    nc = G.M.ncols()
    nonsep_pairs = find_nonsep_pairs(num, g, r, markings, moduli_type)
    if len(nonsep_pairs) > 3:
        return False
    if len(nonsep_pairs) == 3:
        i1 = nonsep_pairs[0][0]
        i2 = nonsep_pairs[0][1]
        i3 = nonsep_pairs[2][1]
        jlist = []
        for j in range(1, nc):
            if len([1 for i in [i1, i2, i3] if G.M[i, j] != 0]) == 2:
                jlist.append(j)
        if len(jlist) > 3:
            return False
        for j in jlist:
            for i in [i1, i2, i3]:
                if G.M[i, j][1] != 0:
                    return False

    return True

# this stuff is old, keeping it around for now just in case
    for j in range(1, nc):
        ilist = []
        for i in range(1, nr):
            if G.M[i, j] != 0:
                ilist.append(i)
        if len(ilist) == 1:
            continue
        ii1 = ilist[0]
        ii2 = ilist[1]
        jlist = []
        for jj in range(1, nc):
            if G.M[ii1, jj] != 0 and G.M[ii2, jj] != 0:
                jlist.append(jj)
        if len(jlist) == 1 or jlist[0] != j:
            continue
        count = len(jlist)
        for ii in [ii1, ii2]:
            for jj in jlist:
                count += G.M[ii, jj][1]
        if count > 3:
            return False
    return True

# next function doesn't work on arbitrary graphs yet, see above function


def DR_coeff(num, g, r, n=0, dvector=(), moduli_type=MODULI_ST):
    markings = tuple(range(1, n + 1))
    G = single_stratum(num, g, r, markings, moduli_type)
    nr = G.M.nrows()
    nc = G.M.ncols()
    answer = QQ((1, autom_count(num, g, r, markings, moduli_type)))

    def balance(ilist):
        bal = [0 for i1 in ilist]
        for j1 in range(1, nc):
            if G.M[0, j1] != 0:
                for i3 in range(1, nr):
                    if G.M[i3, j1] != 0:
                        S = {i3}
                        did_something = True
                        while did_something:
                            did_something = False
                            for i4 in tuple(S):
                                for j2 in range(1, nc):
                                    if G.M[i4, j2] != 0:
                                        for i5 in range(1, nr):
                                            if G.M[i5, j2] != 0 and i5 not in S and (i4 not in ilist or i5 not in ilist):
                                                S.add(i5)
                                                did_something = True
                        for kk, ikk in enumerate(ilist):
                            if ikk in S:
                                bal[kk] += dvector[G.M[0, j1][0] - 1]
        return bal

    def poly4(a, b, c):
        return (ZZ.one() / 420) * (-15 * (a**8 + b**8 + c**8) + 40 * (a**7 * b + a**7 * c + b**7 * a + b**7 * c + c**7 * a + c**7 * b) - 28 * (a**6 * b**2 + a**6 * c**2 + b**6 * a**2 + b**6 * c**2 + c**6 * a**2 + c**6 * b**2) - 112 * (a**6 * b * c + b**6 * a * c + c**6 * a * b) + 84 * (a**5 * b**2 * c + a**5 * c**2 * b + b**5 * a**2 * c + b**5 * c**2 * a + c**5 * a**2 * b + c**5 * b**2 * a) - 70 * (a**4 * b**2 * c**2 + b**4 * a**2 * c**2 + c**4 * a**2 * b**2))

    nonsep_pairs = find_nonsep_pairs(num, g, r, markings, moduli_type)
    if len(nonsep_pairs) == 4:
        cycle = [nonsep_pairs[0][0], nonsep_pairs[0]
                 [1], 0, 0]
        for i in range(1, 4):
            for j in range(2):
                if nonsep_pairs[i][j] == cycle[0]:
                    cycle[3] = nonsep_pairs[i][1 - j]
                if nonsep_pairs[i][j] == cycle[1]:
                    cycle[2] = nonsep_pairs[i][1 - j]
        dbal = balance(cycle)
        a = dbal[0]
        b = dbal[0] + dbal[1]
        c = dbal[0] + dbal[1] + dbal[2]
        answer *= poly4(a, b, c)
    elif len(nonsep_pairs) == 3:
        i1 = nonsep_pairs[0][0]
        i2 = nonsep_pairs[0][1]
        i3 = nonsep_pairs[2][1]
        cycle = [i1, i2, i3]
        cycle4 = cycle + [cycle[0]]
        dbal = balance(cycle)
        dbal4 = dbal + [dbal[0]]
        done = False
        for k in range(3):
            jlist = [j for j in range(1, nc) if (
                G.M[cycle4[k], j] != 0 and G.M[cycle4[k + 1], j] != 0)]
            if len(jlist) == 2:
                answer *= -ZZ.one() / 6 * \
                    poly4(0, dbal4[k], -dbal4[k + 1])
                done = True
            elif len(jlist) == 1:
                if G.M[cycle4[k], jlist[0]][1] + G.M[cycle4[k + 1], jlist[0]][1] > 0:
                    answer *= -ZZ.one() / 2 * \
                        poly4(0, dbal4[k], -dbal4[k + 1])
                    done = True
        if not done:
            answer *= (dbal[0]**6 + dbal[1]**6 + dbal[2]**6 -
                       10 * dbal[0]**2 * dbal[1]**2 * dbal[2]**2) / ZZ(30)

    for j in range(1, nc):
        ilist = []
        for i in range(1, nr):
            if G.M[i, j] != 0:
                ilist.append(i)
        if len(ilist) == 1:
            x = G.M[ilist[0], j][1]
            answer /= ZZ(x).factorial()
            answer *= dvector[G.M[0, j][0] -
                              1]**(ZZ(2) * x)
            continue
        if ilist in nonsep_pairs:
            continue
        ii1 = ilist[0]
        ii2 = ilist[1]
        jlist = []
        for jj in range(1, nc):
            if G.M[ii1, jj] != 0 and G.M[ii2, jj] != 0:
                jlist.append(jj)
        if len(jlist) == 1:
            x1 = G.M[ii1, j][1]
            x2 = G.M[ii2, j][1]
            answer *= -1
            answer /= ZZ(x1).factoial()
            answer /= ZZ(x2).factorial()
            answer /= x1 + x2 + 1
            answer *= balance([ii1, ii2])[0]**(ZZ(2) *
                                               (x1 + x2 + 1))
            continue
        elif len(jlist) == 2:
            if jlist[0] != j:
                continue
            xvec = [G.M[ii1, jlist[0]][1], G.M[ii1, jlist[1]][1],
                    G.M[ii2, jlist[0]][1], G.M[ii2, jlist[1]][1]]
            x = sum(xvec)
            if x == 0:
                answer *= -ZZ.one() / 6
                answer *= balance([ii1, ii2])[0]**4
            elif x == 1:
                answer *= -ZZ.one() / 30
                answer *= balance([ii1, ii2])[0]**6
            elif x == 2:
                if xvec in [[2, 0, 0, 0], [0, 2, 0, 0], [0, 0, 2, 0], [0, 0, 0, 2]]:
                    answer *= -ZZ.one() / 168
                elif xvec in [[1, 1, 0, 0], [0, 0, 1, 1], [1, 0, 0, 1], [0, 1, 1, 0]]:
                    answer *= -ZZ.one() / 280
                elif xvec in [[1, 0, 1, 0], [0, 1, 0, 1]]:
                    answer *= -ZZ.one() / 84
                answer *= balance([ii1, ii2])[0]**8
            continue
        elif len(jlist) == 3:
            if jlist[0] != j:
                continue
            xvec = [G.M[ii1, jlist[0]][1], G.M[ii1, jlist[1]][1], G.M[ii1, jlist[2]]
                    [1], G.M[ii2, jlist[0]][1], G.M[ii2, jlist[1]][1], G.M[ii2, jlist[2]][1]]
            x = sum(xvec)
            if x == 0:
                answer *= -ZZ.one() / 90
                answer *= balance([ii1, ii2])[0]**6
            elif x == 1:
                answer *= -ZZ.one() / 840
                answer *= balance([ii1, ii2])[0]**8
            continue
        elif len(jlist) == 4:
            if jlist[0] != j:
                continue
            answer *= -ZZ.one() / 2520
            answer *= balance([ii1, ii2])[0]**8
    return answer


def veto_for_DR(num, g, r, markings=(), moduli_type=MODULI_ST):
    G = single_stratum(num, g, r, markings, moduli_type)
    nr = G.M.nrows()
    nc = G.M.ncols()
    marked_vertices = []
    for i in range(1, nr):
        if G.M[i, 0] != R(G.M[i, 0][0]):
            return True
        for j in range(1, nc):
            if G.M[i, j][0] == 2:
                return True
            if G.M[0, j] != 0 and G.M[i, j] != 0:
                marked_vertices.append(i)
    for ii in range(1, nr):
        S = set(marked_vertices)
        S.add(ii)
        did_something = True
        while did_something:
            did_something = False
            for i in tuple(S):
                if i == ii:
                    continue
                for j in range(1, nc):
                    if G.M[i, j] != 0:
                        for i2 in range(1, nr):
                            if G.M[i2, j] != 0 and i2 not in S:
                                S.add(i2)
                                did_something = True
        if len(S) < nr - 1:
            return True
    return False


def DR_uncomputed(g, r, markings, moduli_type=MODULI_ST):
    # markings = tuple(range(1,n+1))
    for i in range(num_strata(g, r, markings, moduli_type)):
        if not veto_for_DR(i, g, r, markings, moduli_type) and not DR_coeff_is_known(i, g, r, markings, moduli_type):
            print(i)
            print(single_stratum(i, g, r, markings, moduli_type).M)
            print("---------------------")


def reduce_with_rels(B, vec):
    vec2 = copy(vec)
    for row in B:
        for i in range(len(row)):
            if row[i] != 0:
                if vec2[i] != 0:
                    vec2 -= QQ((vec2[i], row[i])) * row
                break
    return vec2


def DR_coeff_setup(num, g, r, n=0, dvector=(), kval=0, moduli_type=MODULI_ST):
    markings = tuple(range(1, n + 1))
    G = single_stratum(num, g, r, markings, moduli_type)
    nr = G.M.nrows()
    nc = G.M.ncols()
    edge_list = []
    exp_list = []
    scalar_factor = ZZ.one() / \
        autom_count(num, g, r, markings, moduli_type)
    for i in range(1, nr):
        for j in range(1, G.M[i, 0].degree() + 1):
            scalar_factor /= ZZ(G.M[i, 0][j]).factorial()
            scalar_factor /= ZZ(j).factorial()**G.M[i, 0][j]
            scalar_factor *= (-1)**G.M[i, 0][j]
            scalar_factor *= (kval**2)**(j * G.M[i, 0][j])
    given_weights = [-kval * (2 * G.M[i + 1, 0][0] - 2 + sum([G.M[i + 1][j][0]
                                                              for j in range(1, nc)])) for i in range(nr - 1)]
    for j in range(1, nc):
        ilist = [i for i in range(1, nr)
                 if G.M[i, j] != 0]
        if G.M[0, j] == 0:
            if len(ilist) == 1:
                i1 = ilist[0]
                i2 = ilist[0]
                exp1 = G.M[i1, j][1]
                exp2 = G.M[i1, j][2]
            else:
                i1 = ilist[0]
                i2 = ilist[1]
                exp1 = G.M[i1, j][1]
                exp2 = G.M[i2, j][1]
            edge_list.append([i1 - 1, i2 - 1])
            exp_list.append(exp1 + exp2 + 1)
            scalar_factor /= - \
                ZZ(exp1).factorial() * ZZ(exp2).factorial() * (exp1 + exp2 + 1)
        else:
            exp1 = G.M[ilist[0], j][1]
            scalar_factor *= dvector[G.M[0, j][0] -
                                     1]**(ZZ(2) * exp1) / ZZ(exp1).factorial()
            given_weights[ilist[0] -
                          1] += dvector[G.M[0, j][0] - 1]
    return edge_list, exp_list, given_weights, scalar_factor


def DR_coeff_new(num, g, r, n=0, dvector=(), kval=0, moduli_type=MODULI_ST):
    markings = tuple(range(1, n + 1))
    G = single_stratum(num, g, r, markings, moduli_type)
    nr = G.M.nrows()
    nc = G.M.ncols()
    edge_list, exp_list, given_weights, scalar_factor = DR_coeff_setup(
        num, g, r, n, dvector, kval, moduli_type)
    m0 = ceil(sum([abs(i) for i in dvector]) / ZZ(2)) + g * abs(kval)
    h0 = nc - nr - n + 1
    deg = 2 * sum(exp_list)
    mrange = range(m0 + 1, m0 + deg + 2)
    mvalues = []
    for m in mrange:
        total = 0
        for weight_data in itertools.product(*[list(range(m)) for i in range(len(edge_list))]):
            vertex_weights = copy(given_weights)
            for i in range(len(edge_list)):
                vertex_weights[edge_list[i][0]] += weight_data[i]
                vertex_weights[edge_list[i][1]] -= weight_data[i]
            if any(i % m for i in vertex_weights):
                continue
            term = 1
            for i in range(len(edge_list)):
                term *= weight_data[i]**(ZZ(2) * exp_list[i])
            total += term
        mvalues.append(QQ((total, m**h0)))
    mpoly = interpolate(mrange, mvalues)
    return mpoly.subs(x=0) * scalar_factor


def DR_coeff_setup_m(m, num, g, r, n=0, dvector=(), kval=0, moduli_type=MODULI_ST):
    markings = tuple(range(1, n + 1))
    G = single_stratum(num, g, r, markings, moduli_type)
    nr = G.M.nrows()
    nc = G.M.ncols()
    edge_list = []
    exp_list = []
    scalar_factor = ZZ.one() / \
        autom_count(num, g, r, markings, moduli_type)
    for i in range(1, nr):
        for j in range(1, G.M[i, 0].degree() + 1):
            scalar_factor /= ZZ(G.M[i, 0][j]).factorial()
            scalar_factor /= ZZ(j).factorial()**G.M[i, 0][j]
            scalar_factor *= (-1)**G.M[i, 0][j]
            scalar_factor *= (kval**2 - kval * m + m**2 /
                              ZZ(6))**(j * G.M[i, 0][j])
    given_weights = [-kval * (ZZ(2) * G.M[i + 1, 0][0] - ZZ(2) + sum(
        [G.M[i + 1][j][0] for j in range(1, nc)])) for i in range(nr - 1)]
    for j in range(1, nc):
        ilist = [i for i in range(1, nr)
                 if G.M[i, j] != 0]
        if G.M[0, j] == 0:
            if len(ilist) == 1:
                i1 = ilist[0]
                i2 = ilist[0]
                exp1 = G.M[i1, j][1]
                exp2 = G.M[i1, j][2]
            else:
                i1 = ilist[0]
                i2 = ilist[1]
                exp1 = G.M[i1, j][1]
                exp2 = G.M[i2, j][1]
            edge_list.append([i1 - 1, i2 - 1])
            exp_list.append(exp1 + exp2 + 1)
            scalar_factor /= - \
                ZZ(exp1).factorial() * ZZ(exp2).factorial() * (exp1 + exp2 + 1)
        else:
            exp1 = G.M[ilist[0], j][1]
            dval = dvector[G.M[0, j][0] - 1]
            if dval < 0:
                dval = dval + m
            scalar_factor *= (dval**2 - dval * m + m**2 /
                              ZZ(6))**(exp1) / ZZ(exp1).factorial()
            given_weights[ilist[0] -
                          1] += dvector[G.M[0, j][0] - 1]
    return edge_list, exp_list, given_weights, scalar_factor


def DR_coeff_m(m, num, g, r, n=0, dvector=(), kval=0, moduli_type=MODULI_ST):
    markings = tuple(range(1, n + 1))
    G = single_stratum(num, g, r, markings, moduli_type)
    nr = G.M.nrows()
    nc = G.M.ncols()
    edge_list, exp_list, given_weights, scalar_factor = DR_coeff_setup_m(
        m, num, g, r, n, dvector, kval, moduli_type)
    h0 = nc - nr - n + 1
    total = ZZ.zero()
    for weight_data in itertools.product(*[list(range(m)) for i in range(len(edge_list))]):
        vertex_weights = copy(given_weights)
        for i in range(len(edge_list)):
            vertex_weights[edge_list[i][0]] += weight_data[i]
            vertex_weights[edge_list[i][1]] -= weight_data[i]
        if any(i % m for i in vertex_weights):
            continue
        term = 1
        for i in range(len(edge_list)):
            dval = weight_data[i]
            term *= (dval**2 - dval * m + m**2 / ZZ(6))**exp_list[i]
        total += term
    total /= m**h0
    total *= scalar_factor
    return total


def DR_compute(g, r, n=0, dvector=(), kval=0, moduli_type=MODULI_ST):
    r"""
    INPUT:

    g : integer
      the genus
    r : integer
      cohomological degree (set to g for the actual DR cycle, should give
      tautological relations for r > g)
    n : integer
      number of marked points
    dvector : integer vector
      weights to place on the marked points, should have sum zero in the case
      of the DR cycle
    kval : integer (0 by default)
      if set to something else than 0 then the result is the twisted DR
      cycle by copies of the log canonical bundle (e.g. 1 for differentials)
    moduli_type : a moduli type
      MODULI_ST by default (moduli of stable curves), can be set to moduli
      spaces containing less of the boundary (e.g.  MODULI_CT for compact type)
      to compute there instead
    """
    answer = []
    markings = tuple(range(1, n + 1))
    for i in range(num_strata(g, r, markings, moduli_type)):
        answer.append(DR_coeff_new(i, g, r, n, dvector, kval, moduli_type))
    return vector(answer) / ZZ(2) ** r


def DR_compute_m(m, g, r, n=0, dvector=(), kval=0, moduli_type=MODULI_ST):
    answer = []
    markings = tuple(range(1, n + 1))
    for i in range(num_strata(g, r, markings, moduli_type)):
        answer.append(DR_coeff_m(m, i, g, r, n, dvector, kval, moduli_type))
    return vector(answer)


def DR_sparse(g, r, n=0, dvector=(), kval=0, moduli_type=MODULI_ST):
    """
    Same as :func:`DR_compute` except that it returns the answer as a
    sparse vector.

    EXAMPLES::

        sage: from admcycles.DR import DR_sparse
        sage: DR_sparse(1,1,2,(2,-2))
        [[1, 2], [2, 2], [4, -1/24]]
    """
    vec = DR_compute(g, r, n, dvector, kval, moduli_type)
    return [[i, veci] for i, veci in enumerate(vec) if veci != 0]


def DR_psi_check(g, n, dvector, which_psi):
    from .algebra import psi_multiple
    from .evaluation import socle_evaluation
    vec = DR_sparse(g, g, n, dvector, 0)
    r = g
    while r < 3 * g - 3 + n:
        vec = psi_multiple(vec, which_psi, g, r, n)
        r += 1
    total = ZZ.zero()
    for a, b in vec:
        total += b * socle_evaluation(a, g, tuple(range(1, n + 1)))
    return total / 2**g


def DR_reduced(g, dvector=()):
    """
    Same as :func:`DR_compute` except that it only requires two arguments
    (g and dvector) and simplifies the answer using the 3-spin
    tautological relations.

    EXAMPLES::

        sage: from admcycles.DR import DR_reduced
        sage: DR_reduced(1,(2,-2))
        (0, 0, 0, 4, 1/8)
    """
    g = ZZ(g)
    n = len(dvector)
    r = g
    kval = ZZ(sum(dvector) / (2 * g - 2 + n))
    vec = DR_compute(g, r, n, dvector, kval)
    vec = vector(QQ, (QQ(a) for a in vec))
    rels = FZ_rels(g, r, tuple(range(1, n + 1)))
    return reduce_with_rels(rels, vec)
