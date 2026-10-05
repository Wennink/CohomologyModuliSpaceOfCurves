from sage.modules.free_module_element import vector
from sage.rings.all import QQ
from multiprocessing import Pool
from .relations import big_boundary_FZparam, FZ_coeff, FZ_param_iter
from .algebra import convert_to_monomial_basis, convert_to_monomial_basis_contributions
from .moduli import MODULI_ST
from ..symmetry import get_marks_part
from ..antisymmetry import antisym_gens, dec_to_as

from itertools import islice, zip_longest

from .. import file_cache
import os
from sage.env import DOT_SAGE


def generate_interior_FZ_as(g, r, markings, as_gens_parameters, moduli_type=MODULI_ST, num_cpu=1, start=1, maxtasks=100):
    FZpl = FZ_param_iter(3 * r - g - 1, markings)
    for i in range(start - 1):
        next(FZpl)

    with Pool(processes=num_cpu, maxtasksperchild=int(maxtasks)) as pool:
        arglist = zip_longest((), FZpl, fillvalue=(g, r, markings, moduli_type, as_gens_parameters))

        imapresult = pool.imap(_interior_FZ_worker_as, arglist)

        for result in imapresult:
            yield result
        pool.close()
        pool.join()


def _interior_FZ_worker_as(argtuple):
    (g, r, markings, moduli_type, as_gens_parameters), FZ_param = argtuple
    result = []
    as_gens_kappa_convert_contr = antisym_gens_kappa_convert_contribution(*as_gens_parameters)
    for as_gen_kcc in as_gens_kappa_convert_contr:
        coeff = 0
        for i, c in as_gen_kcc:
            coeff += c * FZ_coeff(i, FZ_param, g, r, markings, moduli_type)
        result.append(coeff)
    return vector(QQ, result)


def generate_boundary_FZ_as(g, r, markings, as_gens_parameters, moduli_type=MODULI_ST, num_cpu=1, chunksize=100, start=1, quiet=True, record=True, maxtasks=500):
    num_asgen = len(antisym_gens(*as_gens_parameters))
    big_FZ_param = big_boundary_FZparam(g, r, markings, moduli_type, record=record, start=start)
    for i in range(start - 1):
        next(big_FZ_param)
    count = start
    with Pool(processes=num_cpu, maxtasksperchild=int(maxtasks)) as pool:
        arggen = zip_longest((), big_FZ_param, fillvalue=(num_asgen, as_gens_parameters, r, moduli_type))

        while True:
            arglist = tuple(islice(arggen, chunksize))
            if not arglist:
                return None

            imapresult = pool.imap(_boundary_FZ_worker_as, arglist)

            for result in imapresult:
                if not quiet:
                    print(count)
                yield result
                count += 1
        pool.close()
        pool.join()
    return


def _boundary_FZ_worker_as(arglist):
    (num_asgen, dec_to_as_parameters, r, moduli_type), (len_strata2, which_gen_list, FZ_param, g2, r0, d) = arglist
    kcdtas = kappa_convert_dec_to_as(*dec_to_as_parameters)
    relation = [0] * num_asgen
    for num in range(len_strata2):
        if which_gen_list[num] != -1:
            for as_num, coeff in kcdtas[which_gen_list[num]]:
                relation[as_num] += coeff * FZ_coeff(num, FZ_param, g2, r - r0, tuple(
                    range(1, d + 1)), moduli_type)
    return vector(QQ, relation, sparse=True)


##################################################
# combine antisym basis with kappa convertion
##################################################

@file_cache.file_cached_function(
    directory=os.path.join(DOT_SAGE, "admcycles/cohomology/as_gens"),
    key=file_cache.ignore_args_key([]),
    filename=file_cache.ignore_args_filename())
def kappa_convert_dec_to_as(g, n, r, n_part, self_edges):
    dtas = dec_to_as(g, n, r, n_part, self_edges)
    kcdtas = []
    markings = get_marks_part(n, n_part)
    for i in range(len(dtas)):
        L = []
        for j, c in convert_to_monomial_basis(i, g, r, markings):
            if dtas[j] is None:
                continue
            k, c2 = dtas[j]
            L.append((k, c * c2))
        kcdtas.append(tuple(L))
    return tuple(kcdtas)


@file_cache.file_cached_function(
    directory=os.path.join(DOT_SAGE, "admcycles/cohomology/as_gens"),
    key=file_cache.ignore_args_key([]),
    filename=file_cache.ignore_args_filename())
def antisym_gens_kappa_convert_contribution(g, n, r, n_part, self_edges):
    as_gens = antisym_gens(g, n, r, n_part, self_edges)
    result = []
    dic = convert_to_monomial_basis_contributions(g, r, get_marks_part(n, n_part))
    for gen in as_gens:
        L = []
        for i, c in gen:
            for j, c2 in dic[i]:
                L.append((j, (-1) ** (c < 0) * c2))
        result.append(tuple(L))
    return tuple(result)


def precompute_kappa_convert_as(g, n, r, n_part, self_edges, force_recompute=False):
    if force_recompute or not antisym_gens_kappa_convert_contribution.file_exists(g, n, r, n_part, self_edges):
        antisym_gens_kappa_convert_contribution(g, n, r, n_part, self_edges)
    if force_recompute or not kappa_convert_dec_to_as(g, n, r, n_part, self_edges):
        kappa_convert_dec_to_as(g, n, r, n_part, self_edges)
    return
