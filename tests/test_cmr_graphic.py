"""Offline adapter checks; the separate CMR workflow runs the genuine executable."""
import subprocess
import unittest
from unittest.mock import patch

from pnp_lab.cmr_graphic import _forest_certificate, _matrix_text, decide_with_cmr
from pnp_lab.graphic_support import verify_graphic_certificate


def result(out='',err='',code=0):
    return subprocess.CompletedProcess([],code,out,err)


VERSION=result(err='CMR version 1.4.0 (Release build).\n')
POS='Matrix IS graphic.\n'
TRIANGLE='10 20 r1\n20 30 r2\n20 10 c1\n20 30 c2\n30 10 c3\n'


class CmrAdapterTests(unittest.TestCase):
    def test_sparse_coordinates_and_positive_round_trip(self):
        self.assertEqual(_matrix_text(2,[2,3]),'2 2 3\n2 1 1\n1 2 1\n2 2 1\n')
        # D = [3,5,6], with coordinates 1,2,3. Neither translation offset
        # nor literal coordinate magnitudes may leak into the matrix input.
        offset=1<<79
        g=[(offset,offset^3,offset^5)]
        for t,expected in ((offset^3,'SAT'),(offset^6,'UNSAT')):
            with patch('pnp_lab.cmr_graphic.subprocess.run',side_effect=[VERSION,result(TRIANGLE,POS)]) as p:
                v=decide_with_cmr(g,t)
            self.assertEqual(v['status'],expected)
            self.assertEqual(v['cmr']['recognition'],'verified_graphic')
            self.assertTrue(verify_graphic_certificate(g,v['certificate']))
            self.assertEqual(p.call_args.kwargs['input'],_matrix_text(2,[1,2,3]))
            if expected=='SAT':
                self.assertEqual(v['witness'],[t])

    def test_disconnected_parallel_edges_glue_and_invalid_chords(self):
        data='a b r1\nx y r2\nb a c1\nx y c2\n'
        cert,count=_forest_certificate(data,[1,2],[1,2]);self.assertEqual(count,2)
        self.assertTrue(verify_graphic_certificate([(0,1),(0,2)],cert))
        for bad in [data.replace('x y c2','a y c2'),data.replace('x y c2','y y c2'),
                    data.replace('x y c2','x y c7'),data.replace('x y c2','b a c2'),
                    data.replace('x y r2','b a r2'),data+'a b c1\n']:
            with self.assertRaises(ValueError):
                _forest_certificate(bad,[1,2],[1,2])

    def test_external_failures_do_not_decide_even_easy_sat(self):
        for replies,reason in (([FileNotFoundError()],'cmr_not_found'),
                ([VERSION,subprocess.TimeoutExpired('cmr',1)],'cmr_timeout'),
                ([result(err='CMR version 1.3.1 (Release build).')],'cmr_version_mismatch'),
                ([VERSION,result(err='Matrix is NOT graphic.\n')],'cmr_reports_nongraphic'),
                ([VERSION,result(err=POS,code=2)],'cmr_process_failure'),
                ([VERSION,result(out=TRIANGLE,err='unrecognized result')],'unrecognized_cmr_output'),
                ([VERSION,result(out=TRIANGLE.replace('30 10 c3','20 10 c3'),err=POS)],'invalid_cmr_graph_certificate')):
            with patch('pnp_lab.cmr_graphic.subprocess.run',side_effect=replies):
                r=decide_with_cmr([(0,3,5)],0)
            self.assertEqual((r['status'],r['reason'],r['witness']),('UNKNOWN',reason,None))

    def test_rank_zero_and_bad_inputs(self):
        with patch('pnp_lab.cmr_graphic.subprocess.run',return_value=VERSION) as p:
            v=decide_with_cmr([(2,),(5,)],7)
        self.assertEqual(v['witness'],[2,5]);self.assertEqual(p.call_count,1)
        for args in [([(),(False,)],0),([],True),([(0,1,2,3)],0)]:
            with self.assertRaises(ValueError):decide_with_cmr(*args)
        with self.assertRaises(ValueError):decide_with_cmr([],0,timeout=float('nan'))
