import json
from pathlib import Path
import random
import subprocess
import sys
import unittest

from pnp_lab.frontier_sat import decide_three_cnf

ROOT = Path(__file__).resolve().parents[1]


class SourceDecisionTests(unittest.TestCase):
    def test_signed_source_oracle_and_reordered_lift(self):
        rng = random.Random(413006)
        for _ in range(64):
            names = ('a', 'b', 'unused')
            cs = [tuple(rng.choice((-2, -1, 1, 2)) for _ in range(rng.randrange(1, 4)))
                  for _ in range(rng.randrange(4))]
            models = {b for b in range(8) if all(any(((b >> (abs(k)-1)) & 1) == (k>0)
                                                      for k in c) for c in cs)}
            order = list(range(3*len(cs)))
            rng.shuffle(order)
            got = decide_three_cnf(names, cs, group_order=order)
            self.assertEqual(got['status'], 'SAT' if models else 'UNSAT')
            if models:
                self.assertIn(got['source_witness_mask'], models)
                self.assertFalse(got['source_witness']['unused'])
            else:
                self.assertIsNone(got['source_witness'])

    def test_constants_explicit_budget_and_validation(self):
        self.assertEqual(decide_three_cnf(('unused',), [], max_transitions=0)['source_witness'], {'unused': False})
        self.assertEqual(decide_three_cnf(('u',), [()], max_transitions=0)['status'], 'UNSAT')
        self.assertEqual(decide_three_cnf(('a', 'b', 'c'), [[1,2,-3]], max_transitions=0)['status'], 'SAT')
        with self.assertRaises(ValueError):
            decide_three_cnf(('a',), [[1]], group_order=(0,1,True))
        with self.assertRaises(ValueError):
            decide_three_cnf((), [[]], max_transitions=-1)
        with self.assertRaises(ValueError):
            decide_three_cnf(('x',), [(),(2,)])

    def test_cli_three_outcomes(self):
        script = [sys.executable, str(ROOT/'scripts/solve_three_cnf.py')]
        example = str(ROOT/'examples/three_cnf_odd_cycle.json')
        for args,code,status in (([example],0,'UNSAT'),([example,'--max-transitions','0'],2,'UNKNOWN'),
                                 (['-','--max-transitions','0'],0,'SAT')):
            p = subprocess.run(script+args,input='{"variables": ["a","b","c"], "clauses":[[1,-2,3]]}',
                               capture_output=True,text=True)
            self.assertEqual(p.returncode,code,p.stderr)
            self.assertEqual(json.loads(p.stdout)['status'],status)
