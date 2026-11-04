import json
from pathlib import Path
import subprocess
import sys
import unittest

from pnp_lab.support_solver import decide_xor_choices


class SupportDispatchTests(unittest.TestCase):
    def test_known_classes_and_fallback_budget(self):
        linear = decide_xor_choices([(0,7),(2,5)],2,max_transitions=0)
        self.assertEqual((linear['backend'],linear['status']),('binary_affine','SAT'))
        match = decide_xor_choices([(0,1,2),(2,4)],5,max_transitions=0)
        self.assertEqual((match['backend'],match['witness']),('unit_matching',[1,4]))
        general = decide_xor_choices([(0,1,3),(0,2,3)],0,max_transitions=0)
        self.assertEqual((general['backend'],general['status']),('translated_unit_matching','SAT'))
        self.assertEqual(decide_xor_choices([[]],0)['status'],'UNSAT')
        with self.assertRaises(ValueError):
            decide_xor_choices([[],[False]],0)

    def test_source_cli_sparse_model_and_unknown(self):
        cli = [sys.executable,str(Path(__file__).resolve().parents[1]/'scripts/solve_three_cnf.py'),
               '-', '--encoding', 'sparse']
        obj = {'variables':['a','b','c'], 'clauses':[[1,2,3],[-1,-2,-3]]}
        for extra,expect in (([], 'SAT'),(['--method','frontier','--max-transitions','0'],'UNKNOWN')):
            p=subprocess.run(cli+extra,input=json.dumps(obj),text=True,capture_output=True)
            self.assertEqual(p.returncode,0 if expect=='SAT' else 2,p.stderr)
            r=json.loads(p.stdout);self.assertEqual(r['status'],expect)
            if expect=='SAT':
                bits=r['source_witness'];self.assertEqual(set(bits.values()),{True,False})


class LiftedDispatchTests(unittest.TestCase):
    def test_affine_presolve_then_graph_lifts_across_original_groups(self):
        from itertools import product
        from functools import reduce
        from operator import xor
        gs=[(3,4),(0,1,2),(0,4,5),(11,)]
        actual={reduce(xor,x,0) for x in product(*gs)}
        for t in range(16):
            r=decide_xor_choices(gs,t,method='graphic',max_tree_trials=64)
            self.assertEqual(r['status'],'SAT' if t in actual else 'UNSAT')
            self.assertGreaterEqual(r['absorbed_groups'],2)
            if r['status']=='SAT':
                self.assertTrue(all(x in g for x,g in zip(r['witness'],gs)))
                self.assertEqual(reduce(xor,r['witness'],0),t)

    def test_missing_optional_recognizer_is_unknown(self):
        r=decide_xor_choices([(0,1,6)],0,method='cmr',cmr_executable='/does/not/exist/cmr-graphic')
        self.assertEqual((r['status'],r['reason']),('UNKNOWN','cmr_not_found'))

    def test_nongraphic_partial_and_total_dispatch_are_separate(self):
        gs=[(0,1,2),(0,1,4),(0,1,6)]
        for target in range(8):
            graph=decide_xor_choices(gs,target,method='graphic')
            self.assertEqual(graph['status'],'UNKNOWN')
            auto=decide_xor_choices(gs,target,max_transitions=0)
            self.assertEqual((auto['backend'],auto['status']),('hole_flats','SAT'))
            self.assertEqual(auto['witness'][0]^auto['witness'][1]^auto['witness'][2],target)
        for target in range(16):
            self.assertEqual(decide_xor_choices([(0,1,2),(0,4,8),(0,5,10)],target,method='holes')['status'],'SAT')
