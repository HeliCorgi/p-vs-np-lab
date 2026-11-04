from fractions import Fraction as F
import unittest
from pnp_lab.alternation_trade import replay, standard_trace, checkpoint_envelope


class AlternationTradeTests(unittest.TestCase):
    def test_published_traces_and_both_sides(self):
        self.assertEqual(standard_trace('7/5',template='three')['strict_gap'],'1/25')
        self.assertFalse(standard_trace('71/50',template='three')['strict_contradiction'])
        r=standard_trace('8/5')
        self.assertEqual([l['time'] for l in r['lines']],
                         ['82/25','2','1','8/5','64/25','32/25','256/125','2048/625'])
        self.assertEqual(r['strict_gap'],'2/625')
        for n in range(15800,16201):
            c=F(n,10000)
            self.assertEqual(standard_trace(c)['strict_contradiction'],c**4<c*c+4)

    def test_both_passed_input_sizes_matter(self):
        # The first slowdown after the speedup has a logarithmic guess
        # and unit residual exponent, but reads an input of exponent 3.
        r=replay('3/2',4,[('up',3),('down',),('down',)])
        self.assertEqual(r['lines'][2]['time'],'9/2')
        b=standard_trace('8/5')['lines'][5]['blocks']
        self.assertEqual([v['passed'] for v in b], ['32/25','32/25'])

    def test_scope_and_strictness_guards(self):
        for args in ((2,2,[('up',2)]),(2,2,[('down',)]),(2,2,[('up',1)]),
                     (2,3,[('up',1),('down',),('down',),('up',1)]),
                     (2,2,[('up',1.0)]),(2,2,[('generalize',)]),(2,2,[])):
            with self.assertRaises(ValueError):
                replay(*args)
        for kw in ({'space':'polynomial'}, {'model':'unrestricted-TM'}):
            with self.assertRaises(ValueError):
                replay('7/5',2,[('up',1),('down',),('down',)],**kw)
        equality=replay('4/3','16/7',[('up',1),('down',),('down',)])
        self.assertEqual(equality['strict_gap'],'0')
        self.assertFalse(equality['strict_contradiction'])

    def test_snapshot_envelope_against_rational_grid(self):
        for a,s in [('3','0'),('3','1/3'),('3','3'),('1','1/4')]:
            A,S = F(a),F(s); q=checkpoint_envelope(a,s)
            x, cost=F(q['split']),F(q['envelope'])
            self.assertEqual(cost,max(1,x+S,A-x))
            self.assertTrue(all(max(1,y+S,A-y)>=cost for y in [A*i/80 for i in range(81)]))
        self.assertEqual(checkpoint_envelope(3,3),{'split':'0','envelope':'3'})
        with self.assertRaises(ValueError):checkpoint_envelope(2,3)
