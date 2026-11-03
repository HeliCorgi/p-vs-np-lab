"""Independent small-instance semantics and representation checks."""

import importlib.util
import itertools
import json
from pathlib import Path
import unittest


SPEC = importlib.util.spec_from_file_location(
    "parity_projection_under_test",
    Path(__file__).resolve().parents[1] / "experiments" / "parity_projection.py",
)
assert SPEC is not None and SPEC.loader is not None
parity = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(parity)


def ordinary_evaluation(cnf, assignment):
    """Separate tuple/dict evaluator, avoiding the implementation's bit evaluator."""
    return all(any(assignment[abs(literal)] if literal > 0
                       else not assignment[abs(literal)] for literal in clause)
               for clause in cnf)


class ParityProjectionTests(unittest.TestCase):
    def test_gate_equivalence_and_missing_clause_negative_control(self):
        gate = parity.xor_gate_clauses(1, 2, 3)
        for values in itertools.product((False, True), repeat=3):
            assignment = dict(enumerate(values, start=1))
            self.assertEqual(ordinary_evaluation(gate, assignment),
                             values[2] == (values[0] != values[1]))
        for dropped in range(4):
            faulty = gate[:dropped] + gate[dropped + 1:]
            incorrect_rows = [values for values in itertools.product((False, True), repeat=3)
                              if ordinary_evaluation(faulty, dict(enumerate(values, start=1)))
                              and values[2] != (values[0] != values[1])]
            self.assertEqual(len(incorrect_rows), 1)

    def test_projection_by_independent_existential_enumeration(self):
        for n in range(2, 6):
            cnf = parity.xor_chain_cnf(n)
            for boundary in itertools.product((False, True), repeat=n):
                extensions = 0
                for auxiliary in itertools.product((False, True), repeat=n - 1):
                    assignment = dict(enumerate(boundary + auxiliary, start=1))
                    extensions += ordinary_evaluation(cnf, assignment)
                self.assertEqual(extensions, int(sum(boundary) % 2 == 0))

    def test_all_normalized_implicates_are_exactly_the_generated_primes(self):
        # A normalized non-tautological clause chooses absent/positive/negative
        # independently for each variable. Exhaust all 3**n possibilities.
        n = 5
        even = [dict(enumerate(values, start=1))
                for values in itertools.product((False, True), repeat=n)
                if sum(values) % 2 == 0]
        valid = set()
        for choices in itertools.product((0, 1, -1), repeat=n):
            clause = tuple(variable * sign for variable, sign in enumerate(choices, start=1) if sign)
            if all(ordinary_evaluation((clause,), assignment) for assignment in even):
                valid.add(clause)
        self.assertEqual(valid, set(parity.boundary_prime_cnf(n)))
        self.assertEqual(len(valid), 2 ** (n - 1))
        self.assertTrue(all(len(clause) == n for clause in valid))

    def test_removing_output_pin_changes_the_projected_relation(self):
        n = 4
        cnf = parity.xor_chain_cnf(n)
        # A useful negative control: the gates alone allow both parities, with
        # exactly one auxiliary extension for every boundary assignment.
        self.assertEqual(parity.brute_projection_counts(cnf[:-1], n, n - 1),
                         (1,) * (1 << n))

    def test_obdd_positive_control_and_deterministic_record(self):
        for n in range(2, 9):
            obdd = parity.parity_obdd(n)
            self.assertEqual(len(obdd), 2 * n - 1)
            for assignment in range(1 << n):
                expected = sum((assignment >> bit) & 1 for bit in range(n)) % 2 == 0
                self.assertEqual(parity.obdd_holds(obdd, assignment), expected)
        first = parity.run_experiment([3, 5], brute_max_n=5)
        second = parity.run_experiment([5, 3], brute_max_n=5)
        self.assertEqual(json.dumps(first, sort_keys=True), json.dumps(second, sort_keys=True))
        self.assertTrue(all(case["checks_passed"] for case in first["cases"]))


if __name__ == "__main__":
    unittest.main()
