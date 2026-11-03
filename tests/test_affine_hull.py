"""Check full-hull certificates against raw CNF and independent tiny hulls."""

from copy import deepcopy
import itertools
import unittest

from pnp_lab.affine_hull import (
    check_cnf_coordinate_separation,
    coordinate_separation_certificate_for_leaf_cnf,
)
from pnp_lab.reductions import three_cnf_to_two_cnf_xor


def raw_models(n, cnf):
    return [sum(bit << j for j, bit in enumerate(values))
            for values in itertools.product((0, 1), repeat=n)
            if all(any(values[abs(lit) - 1] == int(lit > 0) for lit in clause)
                   for clause in cnf)]


def difference_span_dimension(models):
    basis = {}
    for model in models:
        value = model ^ models[0]
        while value:
            pivot = value.bit_length() - 1
            if pivot not in basis:
                basis[pivot] = value
                break
            value ^= basis[pivot]
    return len(basis)


class AffineHullCertificateTests(unittest.TestCase):
    def test_signed_bridge_models_have_full_affine_hull(self):
        for clause in ((1, 2, 1), (-1, 2, -2), (-1, -1, -2), (1,), (-2, 1)):
            reduction = three_cnf_to_two_cnf_xor(("x", "y"), (clause,))
            n = len(reduction.affine.variables)
            cert = coordinate_separation_certificate_for_leaf_cnf(n, 2, reduction.cnf)
            self.assertTrue(check_cnf_coordinate_separation(n, reduction.cnf, cert))
            models = raw_models(n, reduction.cnf)
            self.assertEqual(difference_span_dimension(models), n)
            self.assertLess(len(models), 1 << n)

    def test_empty_scope_requires_an_actual_model(self):
        cert = coordinate_separation_certificate_for_leaf_cnf(0, 0, ())
        self.assertTrue(check_cnf_coordinate_separation(0, (), cert))
        self.assertFalse(check_cnf_coordinate_separation(0, ((),), cert))
        self.assertFalse(check_cnf_coordinate_separation(True, (), cert))
        for n in range(1, 5):
            cert = coordinate_separation_certificate_for_leaf_cnf(n, 0, ())
            self.assertTrue(check_cnf_coordinate_separation(n, (), cert))

    def test_tampered_pairs_and_models_are_rejected(self):
        cnf = ((1, 3), (-2, 4))
        cert = coordinate_separation_certificate_for_leaf_cnf(4, 2, cnf)
        corruptions = []
        bad = deepcopy(cert); bad["base_model"] = 0; corruptions.append(bad)
        bad = deepcopy(cert); bad["pairs"][0]["right"] = bad["pairs"][0]["left"]; corruptions.append(bad)
        bad = deepcopy(cert); bad["pairs"][0]["coordinate"] = True; corruptions.append(bad)
        bad = deepcopy(cert); bad["pairs"].pop(); corruptions.append(bad)
        bad = deepcopy(cert); bad["pairs"][2]["right"] = 0; corruptions.append(bad)
        bad = deepcopy(cert); bad["n_variables"] = 5; corruptions.append(bad)
        for bad in corruptions:
            self.assertFalse(check_cnf_coordinate_separation(4, cnf, bad))

    def test_pattern_restriction_and_nonfull_hull_are_not_ignored(self):
        for cnf in (((1,),), ((1, -3),), ((1, 3), (-2, 3)), ((3, 4),), ((),)):
            with self.assertRaises(ValueError):
                coordinate_separation_certificate_for_leaf_cnf(4, 2, cnf)
        free = coordinate_separation_certificate_for_leaf_cnf(2, 2, ())
        self.assertFalse(check_cnf_coordinate_separation(2, ((1,),), free))
        self.assertFalse(check_cnf_coordinate_separation(2, ((0,),), free))


if __name__ == "__main__":
    unittest.main()
