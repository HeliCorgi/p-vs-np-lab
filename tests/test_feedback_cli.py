import json
import subprocess
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


class FeedbackCLITests(unittest.TestCase):
    def test_both_original_decisions_and_mismatched_proof(self):
        reports = {}
        def cli(label,*args,stdin=None):
            return subprocess.run([sys.executable,str(ROOT/'scripts/solve_feedback.py'),
                str(ROOT/f'examples/phase17_feedback_{label}.json'),*args],
                input=stdin,capture_output=True,text=True)
        for label in ('sat','unsat'):
            run = cli(label,'--family-budget')
            self.assertEqual(run.returncode,0,run.stderr)
            self.assertEqual(json.loads(run.stdout)['status'],label.upper())
            reports[label] = run.stdout
            check = cli(label,'--check','-',stdin=run.stdout)
            self.assertEqual(check.returncode,0,check.stderr)
        self.assertEqual(cli('sat','--check','-',stdin=reports['unsat']).returncode,1)
        self.assertEqual(cli('unsat','--check','-',stdin=reports['sat']).returncode,1)
        cap = cli('unsat','--max-edges','0')
        self.assertEqual(cap.returncode,2)
        self.assertIsNone(json.loads(cap.stdout)['certificate'])
