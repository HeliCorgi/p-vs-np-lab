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
        self.assertEqual((general['backend'],general['status']),('affine_frontier','UNKNOWN'))
        self.assertEqual(decide_xor_choices([[]],0)['status'],'UNSAT')
        with self.assertRaises(ValueError):
            decide_xor_choices([[],[False]],0)

    def test_source_cli_sparse_model_and_unknown(self):
        cli = [sys.executable,str(Path(__file__).resolve().parents[1]/'scripts/solve_three_cnf.py'),
               '-', '--encoding', 'sparse']
        obj = {'variables':['a','b','c'], 'clauses':[[1,2,3],[-1,-2,-3]]}
        for extra,expect in (([], 'SAT'),(['--max-transitions','0'],'UNKNOWN')):
            p=subprocess.run(cli+extra,input=json.dumps(obj),text=True,capture_output=True)
            self.assertEqual(p.returncode,0 if expect=='SAT' else 2,p.stderr)
            r=json.loads(p.stdout);self.assertEqual(r['status'],expect)
            if expect=='SAT':
                bits=r['source_witness'];self.assertEqual(set(bits.values()),{True,False})
