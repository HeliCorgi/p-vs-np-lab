"""End-to-end controls on the real merged-flat sparse bridge, not a hand-chosen basis."""
from functools import reduce
from itertools import product
import json
from operator import xor
from pathlib import Path
import random
import subprocess
import sys
import unittest

from pnp_lab.support_solver import decide_xor_choices
from pnp_lab.ternary_support import three_cnf_to_weight_two_supports


CUBE = [tuple((i+1)*v for i,v in enumerate(signs)) for signs in product((-1,1),repeat=3)]
VARS = ('x','y','z')


class OverlapDispatchTests(unittest.TestCase):
    def test_true_cube_now_certified_without_frontier_transitions(self):
        gs=three_cnf_to_weight_two_supports(VARS,CUBE).supports
        self.assertEqual(decide_xor_choices(gs,0,method='holes')['status'],'UNKNOWN')
        r=decide_xor_choices(gs,0,max_transitions=0)
        self.assertEqual((r['backend'],r['status']),('overlap_project','UNSAT'))
        op=r['residual']['overlap_result']
        self.assertEqual((op['fiber_dimension'],op['event_count']),(19,32))
        self.assertGreater(op['parameter_result']['pairs_tested'],0)
        self.assertLessEqual(op['parameter_result']['pairs_tested'],128)
        r=decide_xor_choices(gs,0,method='refute',degree=4,max_rows=6200)
        self.assertEqual(r['status'],'UNSAT')
        cert=r['overlap_result']['parameter_result']['certificate']
        self.assertEqual(cert['degree'],4)

    def test_budget_unknown_and_separately_charged_fallback(self):
        gs=three_cnf_to_weight_two_supports(VARS,CUBE).supports
        for method,opts in [('project',{'max_pairs':0}),('lattice',{'max_intersections':0}),
                            ('refute',{'degree':4,'max_rows':0})]:
            r=decide_xor_choices(gs,0,method=method,**opts)
            self.assertEqual((r['status'],r['witness']),('UNKNOWN',None))
            self.assertIsNone(r.get('merged_decomposition_count'))
        stop=decide_xor_choices(gs,0,max_transitions=0,max_pairs=0)
        self.assertEqual((stop['status'],stop['backend']),('UNKNOWN','affine_frontier'))
        self.assertEqual(stop['prior_overlap_attempt']['parameter_result']['max_pairs'],0)
        self.assertEqual(stop['residual']['transitions'],0)

    def test_small_original_choice_oracle_and_merge_count_scope(self):
        rng=random.Random(990506)
        for _ in range(70):
            gs=[tuple(rng.sample(range(8),rng.randrange(1,4))) for _ in range(rng.randrange(1,5))]
            rhs=rng.randrange(8)
            raw_count=sum(reduce(xor,w,0)==rhs for w in product(*gs))
            for m in ('project','lattice'):
                r=decide_xor_choices(gs,rhs,method=m)
                self.assertEqual(r['status'],'SAT' if raw_count else 'UNSAT')
                if r['status']=='SAT':
                    self.assertEqual(len(r['witness']),len(gs))
                    self.assertTrue(all(x in g for x,g in zip(r['witness'],gs)))
                    self.assertEqual(reduce(xor,r['witness'],0),rhs)
                    if m=='lattice':
                        self.assertGreater(r['merged_decomposition_count'],0)
                        self.assertLessEqual(r['merged_decomposition_count'],raw_count)
        gs=[(0,1,2),(0,1,4)]   # both (0,0) and (1,1) work; after merging there is one selected point.
        r=decide_xor_choices(gs,0,method='lattice')
        self.assertEqual((r['merges'],r['merged_decomposition_count']),(1,1))
        self.assertIn('not source models',r['count_scope'])

    def test_source_cli_unsat_and_lifted_unique_model(self):
        cli=[sys.executable,str(Path(__file__).resolve().parents[1]/'scripts/solve_three_cnf.py'),
             '-', '--encoding', 'sparse','--method','project']
        for cs in (CUBE,CUBE[:-1]):
            models=[w for w in range(8) if all(any(bool(w & (1<<(abs(l)-1)))==(l>0) for l in c) for c in cs)]
            p=subprocess.run(cli,input=json.dumps({'variables':VARS,'clauses':cs}),text=True,capture_output=True)
            self.assertEqual(p.returncode,0,p.stderr)
            r=json.loads(p.stdout)
            self.assertEqual(r['status'],'SAT' if models else 'UNSAT')
            self.assertEqual(r['source_witness_mask'],models[0] if models else None)

    def test_limits_and_explicit_scope(self):
        for kw in ({'max_pairs':False},{'max_intersections':-1},{'max_rows':-2},{'degree':True}):
            with self.assertRaises(ValueError): decide_xor_choices([[]],0,method='project',**kw)
        with self.assertRaises(ValueError):
            decide_xor_choices([(0,1,2,3)],0,method='lattice')
