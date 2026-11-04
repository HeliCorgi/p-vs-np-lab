import json
from pathlib import Path
import subprocess
import sys
import unittest

from pnp_lab.selector_events import compile_compact_events
from pnp_lab.overlap_refutation import verify_cover_certificate

ROOT=Path(__file__).resolve().parents[1]
CUBE=json.loads((ROOT/'examples/overlap_cube_unsat.json').read_text())


class OverlapCliTests(unittest.TestCase):
    def run_case(self, obj, *opts):
        p=subprocess.run([sys.executable,str(ROOT/'scripts/solve_overlap.py'),'-',*opts],
                         input=json.dumps(obj),capture_output=True,text=True)
        self.assertIn(p.returncode,(0,2),p.stderr)
        r=json.loads(p.stdout)
        self.assertEqual(p.returncode,int(r['status']=='UNKNOWN')*2)
        return r

    def test_compact_certificate_and_insufficient_degree(self):
        r=self.run_case(CUBE,'--method','refute','--encoding','compact','--degree','3')
        self.assertEqual(r['status'],'UNSAT')
        e=compile_compact_events(CUBE['variables'],CUBE['clauses'])
        self.assertTrue(verify_cover_certificate(e.n_parameters,e.events,r['result']['certificate'],max_degree=3))
        self.assertEqual(self.run_case(CUBE,'--method','refute','--degree','2')['status'],'UNKNOWN')

    def test_count_scope_and_original_witness(self):
        obj=dict(CUBE,clauses=CUBE['clauses'][:-1])
        for mode,count in [('strict',24),('odd',32),('compact',4),('parsimonious',1)]:
            r=self.run_case(obj,'--encoding',mode,'--method','count','--slice-source')
            self.assertEqual((r['status'],r['source_witness_mask'],r['result']['survivor_count']),('SAT',0,count))
            if mode=='parsimonious':self.assertEqual(r['source_model_count'],1)
            else:self.assertNotIn('source_model_count',r)

    def test_auxiliary_projection_and_invalid_flags(self):
        self.assertEqual(self.run_case(CUBE,'--method','project')['status'],'UNSAT')
        p=subprocess.run([sys.executable,str(ROOT/'scripts/solve_overlap.py'),'-','--method','refute','--max-pairs','1'],
                         input=json.dumps(CUBE),text=True,capture_output=True)
        self.assertEqual(p.returncode,1)
