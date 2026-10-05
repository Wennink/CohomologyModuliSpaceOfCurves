import os
import pickle
import bz2
from multiprocessing import Pool, shared_memory
import numpy as np

from .betti_nrs import get_betti
from .moduli import get_moduli
from .DR.symmetry import symmetrize_map
from .DR.relations import generate_interior_FZ, generate_boundary_FZ
from .DR.antisym_relations import generate_interior_FZ_as, generate_boundary_FZ_as
from .admcycles import generating_indices, genstobasis, decstratum
from .mp_manager import set_context
from .symmetry import genstobasis_Sn, generating_indices_Sn, general_genstobasis, general_generating_indices, tautgens_sym, less_symmetric_partitions, get_marks_part, get_orbits
from .antisymmetry import antisym_gens, genstobasis_as, generating_indices_as, generating_indices_in_cache, use_as_gens

from .log_setup import log_setup, log_memory
import logging

from . import DR

from sage.matrix.constructor import matrix
from sage.matrix.special import block_matrix, identity_matrix
from sage.modules.free_module_element import vector
from sage.rings.all import QQ, ZZ
from itertools import zip_longest
from collections import defaultdict
from sage.combinat.all import Partitions
from sage.rings.finite_rings.finite_field_constructor import GF


########################################
# matrix computations
########################################


def process_rels_matrix(g, n, r, n_part, moduli, M, betti_nr=None, already_echelon=False, echelon_algorithm='flint', self_edges=0):
    r"""
    Takes the matrix of tautological relations and computes a basis of the tautological group
    together with the map from generators to that basis.
    """
    if not already_echelon:
        logging.info('echelonizing matrix')
        if echelon_algorithm is None:
            M.echelonize()
        else:
            M.echelonize(algorithm=echelon_algorithm)

    logging.info('starting processing matrix')
    log_memory()
    # in some cases calling M.pivots() will compute the row echelon form again with the default algorithm
    reordnongens = get_pivots_from_echelon_form(M)
    log_memory()
    num_cols = M.ncols()
    nongens = [num_cols - i - 1 for i in reordnongens]
    log_memory()
    gens = [i for i in range(num_cols) if i not in nongens]
    log_memory()

    # compute result of genstobasis here, for efficiency reasons
    lengens = len(gens)
    if betti_nr is not None:
        assert (lengens == betti_nr)
    gtob = {gens[j]: vector(QQ, lengens, {j: 1}) for j in range(lengens)}
    log_memory()
    for i in range(len(reordnongens)):
        gtob[nongens[i]] = vector([-M[i, num_cols - j - 1] for j in gens])
    log_memory()
    if self_edges >= 2:
        genstobasis_as.set_cache([gtob[i] for i in range(num_cols)], g, n, r, n_part, self_edges, moduli)
        generating_indices_as.set_cache(gens, g, n, r, n_part, self_edges, moduli)
    elif len(n_part) == n:
        genstobasis.set_cache([gtob[i] for i in range(num_cols)], g, n, r, moduli)
        generating_indices.set_cache(gens, g, n, r, moduli)
    else:
        genstobasis_Sn.set_cache([gtob[i] for i in range(num_cols)], g, n, r, n_part, moduli)
        generating_indices_Sn.set_cache(gens, g, n, r, n_part, moduli)

    logging.info('saved genstobasis and generating_indices to disk')
    return


def get_pivots_from_echelon_form(M):
    r"""
    Unlike the built in sagemath pivots function, this does not first call the echelonizing
    function with the default algorithm
    """
    try:
        # this is what M.pivots() does after computing the echelon form
        return M._cache['pivots']
    except (TypeError, KeyError):
        # if the matrix was loaded from file then it doesn't have 'pivots' in the cache
        pivots = []
        for row in M.rows():
            zero_row = True
            for i, c in enumerate(row):
                if c != 0:
                    pivots.append(i)
                    zero_row = False
                    break
            if zero_row:
                break
        return pivots


def process_rels_from_precomputed_matrix(g, n, r, n_part=None, self_edges=0, moduli='st'):
    r"""
    Continue computing a basis from a matrix of tautological relations that was previously
    saved to disk in ``compute_full_rels_matrix`` or ``compute_full_rels_matrix_as``.
    """
    if n_part is None:
        n_part = [1] * n
    if self_edges < 2:
        betti_nr = get_betti(g, n, r, n_part)
        if g < 5 and betti_nr is None:
            raise ValueError('betti unknown')
    else:
        betti_nr = None
    if self_edges < 2:
        with bz2.open(f'FZmatrix_{g}_{n}_{r}_{n_part}.pkl.bz2', 'rb') as file:
            M = pickle.load(file)
    else:
        with bz2.open(f'FZmatrix_as_{g}_{n}_{r}_{n_part}_{self_edges}.pkl.bz2', 'rb') as file:
            M = pickle.load(file)
    process_rels_matrix(g, n, r, n_part, moduli, M, betti_nr=betti_nr, self_edges=self_edges)
    return


def compute_from_less_symmetry(g, n, r, n_part, moduli='st', betti_nr=None):
    r"""
    Computes a basis of the tautological group and the map from generators to relations.
    This is done by symmetrizing a known basis and map.
    """
    if sorted(n_part, reverse=True) != list(n_part):
        raise ValueError
    if type(n_part) is not tuple:
        raise TypeError
    if 3 * g - 3 + n < 2 * r:
        raise ValueError('compute this using pairing')
    gens = False
    for pt, symmarks in less_symmetric_partitions(n_part).items():
        if generating_indices_in_cache(g, n, r, tuple(pt)):
            gens = general_generating_indices(g, n, r, pt, moduli=moduli, method='cached_only')
            print(f"computing generating indices for g = {g}, n = {n} , r = {r}, n_part = {n_part} from the known case where n_part = {pt}")

            gtb = general_genstobasis(g, n, r, pt)
            rels = -identity_matrix(QQ, len(gtb))
            for i, row in enumerate(gtb):
                for i2, j in enumerate(gens):
                    rels[i, j] += row[i2]
            del (gens)
            del (gtb)
            genstobasis.cache.clear()
            genstobasis_Sn.cache.clear()
            generating_indices.cache.clear()
            gens = True

            symmap = symmetrize_map(g, r, get_marks_part(n, pt), symmarks, moduli_type=get_moduli('st', DRpy=True))
            relconv = matrix(QQ, rels.nrows(), len(DR.all_strata(g, r, symmarks)))
            for i in range(rels.nrows()):
                for j in range(rels.ncols()):
                    relconv[i, symmap[j]] += rels[i, j]
            del (rels)
            del (symmap)
            symmetrize_map.cache.clear()
            break
    if not gens:
        raise ValueError('compute relations using one of the other functions')
    reverseindices = list(range(relconv.ncols()))
    reverseindices.reverse()
    M = relconv.matrix_from_columns(reverseindices)
    del relconv
    process_rels_matrix(g, n, r, n_part, moduli, M, betti_nr=betti_nr)
    return


########################################
# computation using 3-spin relations
########################################


def generating_indices_known_betti_nr(g, n, r, betti_nr=None, chunksize=-1, method=None, moduli='st', n_part=None, num_cpu=1, interior_cpu=None, maxtasks=500, echelon_algorithm='flint'):
    r"""
    computes `generating_indices` and `genstobasis`.

    INPUTS:

    betti_nr : expects the correct Betti number or None.
      If set to None it searches the Betti number from a saved list.
      The Betti number serves as a check that the computation gives the correct result.
      And if we are computing in chunks, then it enables us to stop when the expected rank
      has been reached.

    maxtasks : the number of relations a thread will compute before it is treminated
      if a task is terminated it frees up the corresponding memory

    chunksize : how many relations are added at a time before computing the row echelon form and
      checking if we are done
      when set to None it dynamically adjusts the chunksize
      when set to -1 it will not use chunks and compute everything in one go
      setting it to -1 is generally recommended
      Note that when we compute in chunks and stop early, the basis found can be different from the
      one that we would obtain if we compute everything in one go
    """
    boundary_cpu = num_cpu
    if interior_cpu is None:
        interior_cpu = num_cpu
    if chunksize == -1:
        chunksize = 999999999999999
    if n_part is None:
        n_part = [1] * n
    if method == 'newrels' and len(n_part) != n:
        raise NotImplementedError
    if method is None:
        if r >= 3 and len(n_part) == n:
            method = 'newrels'
        else:
            method = '3spin'
    if 3 * g - 3 + n < 2 * r:
        raise ValueError('compute this using pairing matrix')
    if betti_nr is None:
        betti_nr = get_betti(g, n, r, n_part)

    marked_pts = get_marks_part(n, n_part)
    nr_tautgens = len(DR.all_strata(g, r, marked_pts))
    if betti_nr is not None:
        rank_goal = nr_tautgens - betti_nr
    else:
        rank_goal = None
    reverseindices = list(range(nr_tautgens))
    reverseindices.reverse()
    finished = False
    variable_chunksize = chunksize is None
    if betti_nr is None and variable_chunksize:
        raise ValueError
    log_setup(f"FZ_{method}_{g}_{n}_{r}_{n_part}")
    set_context()
    if method == '3spin':
        try:
            with bz2.open(f'FZ_{g}_{n}_{r}_{n_part}_{method}.pkl.bz2', 'rb') as file:
                count, finished_interior, M = pickle.load(file)
                M_rank = M.nrows()
                logging.info(f"continuing from file with count {count} and rank {M_rank}")
        except FileNotFoundError:
            logging.info('did not find file')
            count = 0
            finished_interior = False
            M = matrix(QQ, 0, nr_tautgens)
            M_rank = 0

        if finished_interior:
            logging.info("interior is already done so starting from boundary")
            func = generate_boundary_FZ
            num_cpu = boundary_cpu
        else:
            func = generate_interior_FZ
            num_cpu = interior_cpu
        rels = func(g, r, marked_pts, moduli_type=get_moduli(moduli, DRpy=True), num_cpu=num_cpu, start=1 + count, maxtasks=maxtasks)
        hits = 1
        while betti_nr is None or M_rank < rank_goal:
            logging.info(f"relation count: {count}")
            chunklist = []
            if variable_chunksize:
                chunksize = guess_chunksize(M_rank, rank_goal, hits)
                logging.info(f'new chunksize: {chunksize}')
            for i in range(chunksize):
                try:
                    new_rel = list(DR.convert_vector_to_monomial_basis(next(rels), g, r, marked_pts, moduli_type=get_moduli(moduli, DRpy=True)))
                    new_rel.reverse()
                    chunklist.append(new_rel)
                except StopIteration:
                    logging.info(f"finished chunk after {i} items")
                    if not finished_interior:
                        logging.info("finished interior")
                        count = 0
                        finished_interior = True
                        rels = generate_boundary_FZ(g, r, marked_pts, moduli_type=get_moduli(moduli, DRpy=True), num_cpu=boundary_cpu, maxtasks=maxtasks)
                    else:
                        finished = True
                    break
            if chunklist:
                M = M.stack(matrix(chunklist))
            logging.info(f"echelonizing using algorithm {echelon_algorithm}")
            if echelon_algorithm is None:
                M.echelonize()
            else:
                M.echelonize(algorithm=echelon_algorithm)
            logging.info("done echelonizing")
            new_rank = M.rank()
            M = M.matrix_from_rows(range(new_rank))
            count += chunksize
            hits = QQ((new_rank - M_rank, chunksize))
            if new_rank > M_rank:
                logging.info(f"rank increased: {M_rank} > {new_rank} out of goal {rank_goal}")
                with bz2.open(f'FZ_{g}_{n}_{r}_{n_part}_{method}.pkl.bz2', 'wb') as file:
                    pickle.dump((count, finished_interior, M), file, protocol=5)
                M_rank = new_rank
            if finished and betti_nr is None:
                break
            if finished and not M_rank == rank_goal:
                raise ValueError
    if method == 'newrels':
        try:
            with bz2.open(f'FZ_{g}_{n}_{r}_{n_part}_{method}.pkl.bz2', 'rb') as file:
                count, M = pickle.load(file)
                M_rank = M.nrows()
                logging.info(f"continuing from file with count {count} and rank {M_rank}")
        except FileNotFoundError:
            logging.info('did not find file')
            count = 0
            M = matrix(QQ, 0, nr_tautgens)
            M_rank = 0
        log_memory()
        logging.info("obtaining full relations matrix")
        fullM = DR.rels_matrix(g, r, n, symm=0, moduli_type=get_moduli(moduli, DRpy=True), usespin=False, quiet=False, num_cpu=1)
        logging.info("have full matrix")

        total_rels = fullM.nrows()
        if count != 0:
            fullM = fullM.matrix_from_rows(range(count, fullM.nrows()))
        hits = 1
        while betti_nr is None or M_rank < rank_goal:
            log_memory()
            if variable_chunksize:
                chunksize = guess_chunksize(M_rank, rank_goal, hits, rels_left=total_rels - count)
                logging.info(f'new chunksize: {chunksize}')
            logging.info(f"relation count: {count}")
            if fullM.nrows() > chunksize:
                chunkmatrix = fullM.matrix_from_rows(range(chunksize))
                fullM = fullM.matrix_from_rows(range(chunksize, fullM.nrows()))
            else:
                chunkmatrix = fullM
                finished = True
            chunkmatrix = matrix([DR.convert_vector_to_monomial_basis(chunkmatrix.row(i), g, r, tuple(range(1, n + 1)),
                                                                      moduli_type=get_moduli(moduli, DRpy=True)) for i in range(chunkmatrix.nrows())])
            chunkmatrix = chunkmatrix.matrix_from_columns(reverseindices)
            M = M.stack(chunkmatrix)
            logging.info(f"echelonizing using algorithm {echelon_algorithm}")
            log_memory()
            if echelon_algorithm is None:
                M.echelonize()
            else:
                M.echelonize(algorithm=echelon_algorithm)
            logging.info("done echelonizing")
            log_memory()
            new_rank = M.rank()
            M = M.matrix_from_rows(range(new_rank))
            count += chunksize
            hits = QQ((new_rank - M_rank, chunksize))
            if new_rank > M_rank:
                log_memory()
                logging.info(f'rank increased: {M_rank} > {new_rank} out of goal {rank_goal}')
                with bz2.open(f'FZ_{g}_{n}_{r}_{n_part}_{method}.pkl.bz2', 'wb') as file:
                    pickle.dump((count, M), file, protocol=5)
                M_rank = new_rank
            if finished and betti_nr is None:
                break
            if finished and not M_rank == rank_goal:
                raise ValueError
    process_rels_matrix(g, n, r, n_part, moduli, M, betti_nr=betti_nr, already_echelon=True, echelon_algorithm=echelon_algorithm)

    try:
        os.remove(f'FZ_{g}_{n}_{r}_{n_part}_{method}.pkl.bz2')
    except FileNotFoundError:
        pass
    return


def compute_full_rels_matrix(g, n, r, n_part=None, method=None, moduli='st', num_cpu=63, maxtasks=500):
    r"""
    Saves to disk the matrix of tautological relations without putting it into row echelon form.
    """
    if n_part is None:
        n_part = tuple([1] * n)
    if method == 'newrels' and len(n_part) != n:
        raise NotImplementedError
    if method is None:
        if r >= 3 and len(n_part) == n:
            method = 'newrels'
        else:
            method = '3spin'
    if 3 * g - 3 + n < 2 * r:
        raise ValueError('should be done with pairing matrix')

    marked_pts = get_marks_part(n, n_part)
    moduli_type = get_moduli(moduli, DRpy=True)
    log_setup(f"FZmatrix_{method}_{g}_{n}_{r}_{n_part}")
    set_context()
    if method == '3spin':
        rels = generate_interior_FZ(g, r, marked_pts, moduli_type=moduli_type, num_cpu=num_cpu, maxtasks=maxtasks)
        rowlist = []
        count = 0
        for rel in rels:
            new_rel = list(DR.convert_vector_to_monomial_basis(rel, g, r, marked_pts, moduli_type=moduli_type))
            new_rel.reverse()
            rowlist.append(new_rel)
            count += 1
            print(count)
        rels = generate_boundary_FZ(g, r, marked_pts, moduli_type=moduli_type, num_cpu=num_cpu, maxtasks=maxtasks)
        for rel in rels:
            new_rel = list(DR.convert_vector_to_monomial_basis(rel, g, r, marked_pts, moduli_type=moduli_type))
            new_rel.reverse()
            rowlist.append(new_rel)
            count += 1
            print(count)
    if method == 'newrels':
        M = DR.rels_matrix(g, r, n, symm=0, moduli_type=get_moduli(moduli, DRpy=True), usespin=False, quiet=False, num_cpu=1)
        rowlist = []
        for i in range(M.nrows()):
            new_rel = list(DR.convert_vector_to_monomial_basis(M.row(i), g, r, marked_pts, moduli_type=moduli_type))
            new_rel.reverse()
            rowlist.append(new_rel)
    print('am saving rel list not matrix')
    with bz2.open(f'FZmatrix_{g}_{n}_{r}_{n_part}.pkl.bz2', 'wb') as file:
        pickle.dump(rowlist, file, protocol=5)
    return
    M = matrix(rowlist)
    del (rowlist)
    with bz2.open(f'FZmatrix_{g}_{n}_{r}_{n_part}.pkl.bz2', 'wb') as file:
        pickle.dump(M, file, protocol=5)
    return


def guess_chunksize(current_rank, target_rank, hits, rels_left=None):
    r"""
    dynamically adjusts the chunksize for ``generating_indices_known_betti_nr``
    """
    guess = QQ(max(QQ((9, 5)) * (target_rank - current_rank) / QQ(hits), target_rank - current_rank + 1500)).ceil()
    if rels_left is None:
        return guess
    return min(guess, rels_left)


##################################
# pairing computation
##################################


def _pairvect2(argtuple):
    alist, b = argtuple
    return [(a * b).evaluate() for a in alist]


def _pairvect3(argtuple):
    alist, b = argtuple
    return [sum([(a * b).evaluate() for a in aa]) for aa in alist]


def process_pairing_chunk(argtuple):
    r"""
    Computes part of the intersection matrix for the perfect pairing.
    If a basis has not yet been found it also computes
    which generators are canditates for a basis.
    """
    gens_orbit, cogens_list = argtuple
    if type(gens_orbit[0]) is decstratum:
        pair_func = _pairvect2
    else:
        pair_func = _pairvect3
    row_list = []
    M_rank = 0
    potential_generators = []
    existing_shm = shared_memory.SharedMemory(name='shared_bool')
    c = np.ndarray((1,), dtype=np.int64, buffer=existing_shm.buf)
    for i, cogen in enumerate(cogens_list):
        row = pair_func((gens_orbit, cogen))
        row_list.append(row)
        if c[0]:
            continue
        if i == 0:
            rank_goal = len(row)
            M = matrix(QQ, 0, rank_goal)
        M_new = block_matrix([[M], [matrix([row])]], subdivide=False)
        new_rank = M_new.rank()
        if new_rank > M_rank:
            potential_generators.append(i)
            M = M_new
            M_rank = new_rank
    return row_list, potential_generators


def compute_basis_with_pairing(g, n, r, n_part, num_cpu=1, max_tasks=1, chunksize=500):
    r"""
    Computes a basis of the tautological group together with the map from generators to that basis.
    This computation is done using the perfect pairing and assumes that the tautological ring is Gorenstein.
    """
    log_setup(f"FZ_pairing_{g}_{n}_{r}_{n_part}")
    set_context()
    co_r = 3 * g - 3 + n - r
    if co_r > r or co_r < 0:
        return ValueError("r should not be lower than the middle degree or higher than the socle degree")
    if n_part is None:
        n_part = [1] * n
    if not generating_indices_in_cache(g, n, co_r, n_part):
        raise ValueError(f'first compute relations for g={g}, n={n}, r={co_r}, n_part={n_part}')

    cogens = tautgens_sym(g, n, r, n_part)

    try:
        with bz2.open(f'pairing_{g}_{n}_{r}_{n_part}.pkl.bz2', 'rb') as file:
            row_list, gen_ind = pickle.load(file)
            M = matrix([row_list[i] for i in gen_ind])
            M_rank = M.nrows()
            rank_goal = M.ncols()
            square_yet = M_rank == rank_goal
            start_point = len(row_list)
            cogens = cogens[start_point:]
            logging.info(f"continuing from file with count {start_point} and rank {M_rank}")
    except FileNotFoundError:
        logging.info('did not find file')
        row_list = []
        gen_ind = []
        M_rank = 0
        start_point = 0
        M = None
        square_yet = False

    totaltasks = len(cogens)
    logging.info(f'totaltasks: {totaltasks}')
    chunksize = min(QQ((totaltasks, num_cpu)).ceil(), chunksize)
    logging.info(f'set chunksize to {chunksize}')
    cogens_chunks = []
    index = 0
    while index < totaltasks:
        cogens_chunks.append(cogens[index: index + chunksize])
        index += chunksize
    totalchunks = len(cogens_chunks)
    del (cogens)
    if len(n_part) == n:
        gens = tautgens_sym(g, n, co_r, n_part)
        gens = [gens[i] for i in general_generating_indices(g, n, co_r, n_part)]
    else:
        gens = get_orbits(g, n, co_r, n_part)

    argiter = zip_longest((), cogens_chunks, fillvalue=gens)

    if square_yet:
        a = np.array([1])
    else:
        a = np.array([0])
    try:
        shm = shared_memory.SharedMemory(create=True, size=a.nbytes, name="shared_bool")
    except FileExistsError:
        shm = shared_memory.SharedMemory(create=False, name="shared_bool")
        shm.unlink()
        shm = shared_memory.SharedMemory(create=True, size=a.nbytes, name="shared_bool")
    b = np.ndarray(a.shape, dtype=a.dtype, buffer=shm.buf)
    b[:] = a[:]

    logging.info(f"starting the multiprocessing now for g={g}, n={n}, r={r}, n_part={n_part}")
    log_memory()
    with Pool(processes=num_cpu, maxtasksperchild=int(max_tasks)) as pool:
        L = pool.imap(process_pairing_chunk, argiter)
        for chunk_i, (chunk_list, potential_gens) in enumerate(L):
            logging.info(f"finished computing chunk {chunk_i} out of {totalchunks}")
            logging.info(f"len chunk_list: {len(chunk_list)}, len pot_gens: {len(potential_gens)}")
            if ZZ(QQ((totalchunks, 20)).floor()).divides(chunk_i):
                with bz2.open(f'pairing_{g}_{n}_{r}_{n_part}.pkl.bz2', 'wb') as file:
                    pickle.dump((row_list, gen_ind), file, protocol=5)
                logging.info('finished writing to file')
            log_memory()
            row_list += chunk_list
            if square_yet:
                continue
            if chunk_i == 0:
                rank_goal = len(chunk_list[0])
                if M is None:
                    M = matrix(QQ, 0, rank_goal)
            for pot_i in potential_gens:
                M_new = block_matrix([[M], [matrix([chunk_list[pot_i]])]], subdivide=False)
                new_rank = M_new.rank()
                if new_rank > M_rank:
                    gen_ind.append(start_point + chunk_i * chunksize + pot_i)
                    M = M_new
                    M_rank = new_rank
                square_yet = M_rank == rank_goal
                if square_yet:
                    logging.info("found a full list of generating_indices")
                    b[:] = np.array([1])[:]
                    break
            logging.info('finished processing chunksize')
            log_memory()
        pool.close()
        pool.join()
    shm.close()
    shm.unlink()
    if len(gen_ind) != rank_goal:
        raise ValueError
    M = M.inverse()
    gensmap = (matrix(row_list) * M).rows()
    if len(n_part) == n:
        generating_indices.set_cache(gen_ind, g, n, r, 'st')
        genstobasis.set_cache(gensmap, g, n, r, 'st')
    else:
        generating_indices_Sn.set_cache(gen_ind, g, n, r, n_part, 'st')
        genstobasis_Sn.set_cache(gensmap, g, n, r, n_part, 'st')
    os.remove(f'pairing_{g}_{n}_{r}_{n_part}.pkl.bz2')
    return


#################################
# single vertex case where we can compute pixton relations on generators up to asymmetry
#################################


def compute_generating_indices_3spin_as(g, n, r, n_part, self_edges, chunksize=-1, moduli='st', num_cpu=1, interior_cpu=None, maxtasks=500, echelon_algorithm='flint', force_non_pairing=False):
    r"""
    Computes basis indices and the map from generators to that basis for
    (S_{g,n}^r/P_{g,n}^r)^((S_2 \wraith S_{``self_edges``}) \otimes (S_{``n_part``}/S_2^{``self_edges``}))
    """
    if self_edges < 2:
        raise ValueError('no interesting antisymmetry, use normal generating_indices')
    boundary_cpu = num_cpu
    if interior_cpu is None:
        interior_cpu = num_cpu
    if chunksize == -1:
        chunksize = 999999999999999
    if n_part is None:
        n_part = [1] * n

    as_gens_params = (g, n, r, n_part, self_edges)
    num_asgens = len(antisym_gens(*as_gens_params))

    marked_pts = get_marks_part(n, n_part)
    reverseindices = list(range(num_asgens))
    reverseindices.reverse()
    finished = False

    log_setup(f"FZas_{g}_{n}_{r}_{n_part}_{self_edges}")
    set_context()

    try:
        with bz2.open(f'FZas_{g}_{n}_{r}_{n_part}_{self_edges}.pkl.bz2', 'rb') as file:
            count, finished_interior, M = pickle.load(file)
            logging.info(f"continuing from file with count {count}")
    except FileNotFoundError:
        logging.info('did not find file')
        count = 0
        finished_interior = False
        M = matrix(QQ, 0, num_asgens)

    if finished_interior:
        logging.info("interior is already done so starting from boundary")
        func = generate_boundary_FZ_as
        num_cpu = boundary_cpu
    else:
        func = generate_interior_FZ_as
        num_cpu = interior_cpu
    rels = func(g, r, marked_pts, as_gens_params, moduli_type=get_moduli(moduli, DRpy=True), num_cpu=num_cpu, start=1 + count, maxtasks=maxtasks)
    while True:
        logging.info(f"relation count: {count}")
        chunklist = []
        for i in range(chunksize):
            try:
                new_rel = list(next(rels))
                new_rel.reverse()
                chunklist.append(new_rel)
            except StopIteration:
                logging.info(f"finished chunk after {i} items")
                if not finished_interior:
                    logging.info("finished interior")
                    count = 0
                    finished_interior = True
                    rels = generate_boundary_FZ_as(g, r, marked_pts, as_gens_params, moduli_type=get_moduli(moduli, DRpy=True), num_cpu=boundary_cpu, maxtasks=maxtasks)
                else:
                    finished = True
                break
        if chunklist:
            M = M.stack(matrix(chunklist))
            logging.info(f"echelonizing using algorithm {echelon_algorithm}")
            if echelon_algorithm is None:
                M.echelonize()
            else:
                M.echelonize(algorithm=echelon_algorithm)
            logging.info("done echelonizing")
            new_rank = M.rank()
            M = M.matrix_from_rows(range(new_rank))
            count += chunksize
            logging.info("writing to file")
            with bz2.open(f'FZas_{g}_{n}_{r}_{n_part}_{self_edges}.pkl.bz2', 'wb') as file:
                pickle.dump((count, finished_interior, M), file, protocol=5)
        if finished:
            break
    process_rels_matrix(g, n, r, n_part, moduli, M, already_echelon=True, self_edges=self_edges)

    try:
        os.remove(f'FZas_{g}_{n}_{r}_{n_part}_{self_edges}.pkl.bz2')
    except FileNotFoundError:
        pass
    return


def compute_full_rels_matrix_as(g, n, r, n_part, self_edges, moduli='st', num_cpu=63, maxtasks=500):
    r"""
    Saves to disk the matrix of tautological relations without putting it into row echelon
    form with regards to
    (S_{g,n}^r/P_{g,n}^r)^((S_2 \wraith S_{``self_edges``}) \otimes (S_{``n_part``}/S_2^{``self_edges``}))
    """
    if self_edges < 2:
        raise ValueError('no interesting antisymmetry, use normal geerating_indices')
    if 3 * g - 3 + n < 2 * r:
        print('warning: this is in pairing matrix range')

    as_gens_params = (g, n, r, n_part, self_edges)

    marked_pts = get_marks_part(n, n_part)

    moduli_type = get_moduli(moduli, DRpy=True)
    log_setup(f"FZmatrix_as_{g}_{n}_{r}_{n_part}_{self_edges}")
    set_context()

    rels = generate_interior_FZ_as(g, r, marked_pts, as_gens_params, moduli_type=moduli_type, num_cpu=num_cpu, maxtasks=maxtasks)
    rowlist = []
    count = 0
    for rel in rels:
        new_rel = list(rel)
        new_rel.reverse()
        rowlist.append(new_rel)
        count += 1
        print(count)
    rels = generate_boundary_FZ_as(g, r, marked_pts, as_gens_params, moduli_type=moduli_type, num_cpu=num_cpu, maxtasks=maxtasks)
    for rel in rels:
        new_rel = list(rel)
        new_rel.reverse()
        rowlist.append(new_rel)
        count += 1
        print(count)

    M = matrix(rowlist)
    del (rowlist)
    with bz2.open(f'FZmatrix_as_{g}_{n}_{r}_{n_part}_{self_edges}.pkl.bz2', 'wb') as file:
        pickle.dump(M, file, protocol=5)
    return


#####################################
# relation computation scheduler
#####################################


def compute_relations(missing_relations, num_cpu=16):
    r"""
    Compute the relations in ``missing_relations``.
    Every computation is done in its own process so the memory gets freed up afterwards.
    """
    from .antisymmetry import compute_as_gens
    from .DR.antisym_relations import precompute_kappa_convert_as
    from multiprocessing import Queue, Process
    log_setup('relation_computation_scheduler')
    set_context()
    queue = Queue()
    p = Process(target=parse_missing_relations_list, args=(missing_relations, queue, num_cpu))
    p.start()
    p.join()
#    if p.exitcode == 1:
    if p.exitcode != 0:
        raise ValueError
    logging.info('finished computing list of missing relations')
    spin_list_least_symmetry, spin_list_more_symmetry, pairing_list, as_list_least_sym, as_list_more_sym = queue.get()
    for g, n, r, n_part in spin_list_least_symmetry:
        p = Process(target=generating_indices_known_betti_nr, args=(g, n, r, None, -1, None, 'st', n_part, num_cpu))
        logging.info(f'computing relations for g={g}, n={n}, r={r}, n_part={n_part}')
        p.start()
        p.join()
        if p.exitcode != 0:
            raise ValueError
    logging.info('finished computing 3spin relations with least symmetry')
    for g, n, r, n_part in spin_list_more_symmetry:
        p = Process(target=compute_from_less_symmetry, args=(g, n, r, n_part))
        logging.info(f'computing relations for g={g}, n={n}, r={r}, n_part={n_part}')
        p.start()
        p.join()
        if p.exitcode != 0:
            raise ValueError
    logging.info('finished computing 3spin relations')
    for g, n, r, n_part in pairing_list:
        p = Process(target=compute_basis_with_pairing, args=(g, n, r, n_part, num_cpu, 1))
        logging.info(f'computing relations for g={g}, n={n}, r={r}, n_part={n_part}')
        p.start()
        p.join()
        if p.exitcode != 0:
            raise ValueError
    for g, n, r, n_part, self_edges in as_list_least_sym + as_list_more_sym:
        p = Process(target=compute_as_gens, args=(g, n, r, n_part, self_edges))
        logging.info(f'computing antisymmetric generators for g={g}, n={n}, r={r}, n_part={n_part}, self_edges={self_edges}')
        p.start()
        p.join()
        if p.exitcode != 0:
            raise ValueError
    logging.info('finished computing antisymmetric generators')
    for g, n, r, n_part, self_edges in as_list_least_sym + as_list_more_sym:
        p = Process(target=precompute_kappa_convert_as, args=(g, n, r, n_part, self_edges))
        logging.info(f'computing antisymmetric kappa conversion data for g={g}, n={n}, r={r}, n_part={n_part}, self_edges={self_edges}')
        p.start()
        p.join()
        if p.exitcode != 0:
            raise ValueError
    logging.info('finished computing antisymmetric kappa_conversion data')
    for g, n, r, n_part, self_edges in as_list_least_sym:
        p = Process(target=compute_generating_indices_3spin_as, args=(g, n, r, n_part, self_edges, -1, 'st', num_cpu))
        logging.info(f'computing relations for g={g}, n={n}, r={r}, n_part={n_part}, self_edges={self_edges}')
        p.start()
        p.join()
        if p.exitcode != 0:
            raise ValueError
    logging.info('finished computing antisymmetric 3spin relations with least symmetry')
    for g, n, r, n_part, self_edges in as_list_more_sym:
        p = Process(target=compute_generating_indices_3spin_as, args=(g, n, r, n_part, self_edges, -1, 'st', num_cpu))
        logging.info(f'computing relations for g={g}, n={n}, r={r}, n_part={n_part}, self_edges={self_edges}')
        logging.info('this could instead be done from relations with more symmetry')
        p.start()
        p.join()
        if p.exitcode != 0:
            raise ValueError
    logging.info('finished computing relations')


def parse_missing_relations_list(missing_relations, queue, num_cpu=16):
    r"""
    For a list of (g, n, r, n_part, self_edges), compute which
    methods should be used to compute the corresponding tautological groups.
    """
    missing_rels2 = []
    for g, n, r, n_part, self_edges in missing_relations:
        if (self_edges >= 2 and not use_as_gens(g, n, r, n_part, self_edges)) or self_edges == 1:
            if not generating_indices_in_cache(g, n, r, n_part):
                missing_rels2.append((g, n, r, n_part, 0))
        else:
            missing_rels2.append((g, n, r, n_part, self_edges))
    missing_rels = set(missing_rels2)
    misrel_dict = defaultdict(list)
    misrel_dict_as = defaultdict(list)
    pairing_list = []
    for g, n, r, n_part, se in missing_rels:
        if use_as_gens(g, n, r, n_part, se):
            misrel_dict_as[(g, n, r, se)].append(n_part)
        elif not generating_indices_in_cache(g, n, r, n_part):
            if 2 * r <= 3 * g - 3 + n:
                misrel_dict[(g, n, r)].append(n_part)
            else:
                pairing_list.append((g, n, r, n_part))
                dual_gnrp = (g, n, 3 * g - 3 + n - r, n_part, 0)
                if dual_gnrp not in missing_rels:
                    if not generating_indices_in_cache(*dual_gnrp):
                        misrel_dict[dual_gnrp[:3]].append(dual_gnrp[3])
    spin_list_least_symmetry = []
    spin_list_more_symmetry = []
    for gnr, np_list in misrel_dict.items():
        np_list.sort()
        lp = less_symmetric_partitions(np_list[0])
        file_exists = False
        for par in Partitions(sum(np_list[0])):
            if par not in lp:
                if generating_indices_in_cache(*gnr, par):
                    file_exists = True
                    break
        if file_exists:
            spin_list_more_symmetry.append((*gnr, np_list[0]))
        else:
            spin_list_least_symmetry.append((*gnr, np_list[0]))
        for n_p in np_list[1:]:
            spin_list_more_symmetry.append((*gnr, n_p))

    as_list_least_symmetry = []
    as_list_more_symmetry = []
    for (g, n, r, se), np_list in misrel_dict_as.items():
        gnr = (g, n, r)
        np_list.sort()
        lp = less_symmetric_partitions(np_list[0])
        file_exists = False
        for par in Partitions(sum(np_list[0])):
            if par not in lp:
                if generating_indices_in_cache(*gnr, par, se, as_only=True):
                    file_exists = True
                    break
        if file_exists:
            as_list_more_symmetry.append((*gnr, np_list[0], se))
        else:
            as_list_least_symmetry.append((*gnr, np_list[0], se))
        for n_p in np_list[1:]:
            as_list_more_symmetry.append((*gnr, n_p, se))

    queue.put((spin_list_least_symmetry, spin_list_more_symmetry, pairing_list, as_list_least_symmetry, as_list_more_symmetry))
    return


##############################
# verify Pixton conjecture
##############################


def verify_Pixton_conjecture(g, n, r, n_part=None):
    r"""
    Verifies the Pixton conjecture for (S_{g,n}^r/P_{g,n}^r)^S_{``n_part``}.
    """
    if n_part is None:
        n_part = (1,) * n
    if generating_indices_in_cache(g, n, r, n_part):
        assert (len(general_generating_indices(g, n, r, n_part)) == get_betti(g, n, r, n_part))
        print(f'Pixton conjecture holds for g={g}, n={n}, r={r}, n_part={n_part}')
    else:
        raise ValueError(f'please first compute relations for g={g}, n={n}, r={r}, n_part={n_part}')
    return


# edited code from generating_indices_known_betti_nr
def verify_Pixton_conjecture_modp(g, n, r, n_part, modp, betti_nr=None, chunksize=None, method=None, moduli='st', num_cpu=1, interior_cpu=None, maxtasks=500):
    r"""
    Tries to verify the Pixton conjecture by computing a basis modulo ``modp``
    where ``modp`` should be a prime number.
    """
    boundary_cpu = num_cpu
    if interior_cpu is None:
        interior_cpu = num_cpu
    if chunksize == -1:
        chunksize = 999999999999999
    if n_part is None:
        n_part = [1] * n
    if method == 'newrels' and len(n_part) != n:
        raise NotImplementedError
    if method is None:
        if r >= 3 and len(n_part) == n:
            method = 'newrels'
        else:
            method = '3spin'
    if 3 * g - 3 + n < 2 * r:
        raise ValueError('compute this using pairing matrix')
    if g < 5 and betti_nr is None:
        betti_nr = get_betti(g, n, r, n_part)
        if betti_nr is None:
            raise ValueError('betti unknown')

    if modp is None:
        base_ring = QQ
    else:
        base_ring = GF(modp)

    marked_pts = get_marks_part(n, n_part)
    nr_tautgens = len(DR.all_strata(g, r, marked_pts))
    if betti_nr is not None:
        rank_goal = nr_tautgens - betti_nr
    else:
        rank_goal = None
    reverseindices = list(range(nr_tautgens))
    reverseindices.reverse()
    finished = False
    variable_chunksize = chunksize is None
    if betti_nr is None and variable_chunksize:
        raise ValueError
    log_setup(f"FZ_{method}_{g}_{n}_{r}_{n_part}")
    set_context()
    if method == '3spin':
        try:
            with bz2.open(f'FZ_{g}_{n}_{r}_{n_part}_{method}.pkl.bz2', 'rb') as file:
                count, finished_interior, M = pickle.load(file)
                M_rank = M.nrows()
                logging.info(f"continuing from file with count {count} and rank {M_rank}")
        except FileNotFoundError:
            logging.info('did not find file')
            count = 0
            finished_interior = False
            M = matrix(base_ring, 0, nr_tautgens)
            M_rank = 0

        if finished_interior:
            logging.info("interior is already done so starting from boundary")
            func = generate_boundary_FZ
            num_cpu = boundary_cpu
        else:
            func = generate_interior_FZ
            num_cpu = interior_cpu
        rels = func(g, r, marked_pts, moduli_type=get_moduli(moduli, DRpy=True), num_cpu=num_cpu, start=1 + count, maxtasks=maxtasks)
        hits = 1
        while betti_nr is None or M_rank < rank_goal:
            logging.info(f"relation count: {count}")
            chunklist = []
            if variable_chunksize:
                chunksize = guess_chunksize(M_rank, rank_goal, hits)
                logging.info(f'new chunksize: {chunksize}')
            for i in range(chunksize):
                try:
                    new_rel = list(DR.convert_vector_to_monomial_basis(next(rels), g, r, marked_pts, moduli_type=get_moduli(moduli, DRpy=True)))
                    new_rel.reverse()
                    chunklist.append(new_rel)
                except StopIteration:
                    logging.info(f"finished chunk after {i} items")
                    if not finished_interior:
                        logging.info("finished interior")
                        count = 0
                        finished_interior = True
                        rels = generate_boundary_FZ(g, r, marked_pts, moduli_type=get_moduli(moduli, DRpy=True), num_cpu=boundary_cpu, maxtasks=maxtasks)
                        if variable_chunksize:
                            chunksize = i
                    else:
                        finished = True
                    break
            if chunklist:
                M = M.stack(matrix(base_ring, chunklist))
            new_rank = M.rank()
            count += chunksize
            hits = QQ((new_rank - M_rank, chunksize))
            if new_rank > M_rank:
                logging.info(f"rank increased: {M_rank} > {new_rank} out of goal {rank_goal}")
                M_rank = new_rank
            if finished and betti_nr is None:
                break
            if finished and not M_rank == rank_goal:
                raise ValueError
    if method == 'newrels':
        try:
            with bz2.open(f'FZ_{g}_{n}_{r}_{n_part}_{method}.pkl.bz2', 'rb') as file:
                count, M = pickle.load(file)
                M_rank = M.nrows()
                logging.info(f"continuing from file with count {count} and rank {M_rank}")
        except FileNotFoundError:
            logging.info('did not find file')
            count = 0
            M = matrix(base_ring, 0, nr_tautgens)
            M_rank = 0
        log_memory()
        logging.info("obtaining full relations matrix")
        fullM = DR.rels_matrix(g, r, n, symm=0, moduli_type=get_moduli(moduli, DRpy=True), usespin=False, quiet=False, num_cpu=1)
        logging.info("have full matrix")

        total_rels = fullM.nrows()
        if count != 0:
            fullM = fullM.matrix_from_rows(range(count, fullM.nrows()))
        hits = 1
        while betti_nr is None or M_rank < rank_goal:
            log_memory()
            if variable_chunksize:
                chunksize = guess_chunksize(M_rank, rank_goal, hits, rels_left=total_rels - count)
                logging.info(f'new chunksize: {chunksize}')
            logging.info(f"relation count: {count}")
            if fullM.nrows() > chunksize:
                chunkmatrix = fullM.matrix_from_rows(range(chunksize))
                fullM = fullM.matrix_from_rows(range(chunksize, fullM.nrows()))
            else:
                chunkmatrix = fullM
                finished = True
            chunkmatrix = matrix(base_ring, [DR.convert_vector_to_monomial_basis(chunkmatrix.row(i), g, r, tuple(range(1, n + 1)),
                                                                                 moduli_type=get_moduli(moduli, DRpy=True)) for i in range(chunkmatrix.nrows())])
            chunkmatrix = chunkmatrix.matrix_from_columns(reverseindices)
            M = M.stack(chunkmatrix)
            log_memory()
            new_rank = M.rank()
            count += chunksize
            hits = QQ((new_rank - M_rank, chunksize))
            if new_rank > M_rank:
                log_memory()
                logging.info(f'rank increased: {M_rank} > {new_rank} out of goal {rank_goal}')
                M_rank = new_rank
            if finished and betti_nr is None:
                break
            if finished and not M_rank == rank_goal:
                raise ValueError

    return f'finished succesfully with rank(M) = {M_rank} and rank_goal = {rank_goal}'
