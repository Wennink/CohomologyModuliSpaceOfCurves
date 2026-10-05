r"""
This submodule contains original code by Aaron Pixton (apixton@mit.edu)

It has been converted to python files and split into several files.
"""

from .algebra import convert_vector_to_monomial_basis
from .double_ramification_cycle import DR_compute, DR_sparse, DR_reduced
from .evaluation import socle_evaluation, socle_formula
from .relations import FZ_rels, rels_matrix, betti, FZ_matrix, pairing_matrix, pairing_submatrix, FZ_methods_sanity_check
from .graph import Graph, X, num_strata, num_pure_strata, autom_count, single_stratum, num_of_stratum, all_strata
from .moduli import MODULI_SM, MODULI_RT, MODULI_CT, MODULI_ST
from .utils import interpolate
