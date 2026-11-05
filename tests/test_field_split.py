import copy
import unittest

from pnp_lab.field_split import check_field_split,field_split_refute,switch_flow
from pnp_lab.ternary_flow import prism_edges,scramble


class FieldSplitTests(unittest.TestCase):
    def test_switched_branches_and_raw_binding(self):
        n,rows,_=switch_flow(prism_edges(3),6)
        rows,_=scramble(n,rows,None,18185)
        out=field_split_refute(n,rows)
        cert=out['certificate']
        self.assertEqual(out['status'],'UNSAT')
        self.assertTrue(check_field_split(n,rows,cert))
        self.assertEqual({b['prime'] for b in cert['branches']},{2,3})
        for change in ('selector','branch','prime','missing','bool','term'):
            bad=copy.deepcopy(cert)
            if change=='selector': bad['selector']=n+1
            elif change=='branch': bad['branches'].reverse()
            elif change=='prime': bad['branches'][0]['prime']=5
            elif change=='missing': bad['branches'].pop()
            elif change=='bool': bad['selector']=True
            else: bad['branches'][1]['terms'].clear()
            self.assertFalse(check_field_split(n,rows,bad),change)
        n,sat,word=switch_flow(prism_edges(3),6,satisfiable=True)
        sat,word=scramble(n,sat,word,18185)
        self.assertFalse(check_field_split(n,sat,cert))
        self.assertTrue(all(any(bool(word>>(abs(l)-1)&1)==(l>0) for l in c) for c in sat))
        self.assertEqual(field_split_refute(n,sat)['status'],'UNKNOWN')

    def test_no_cut_or_exhausted_budget_is_not_a_decision(self):
        n,cs,_=switch_flow(prism_edges(3),6)
        for cap in (dict(max_candidates=0),dict(max_scopes=0)):
            r=field_split_refute(n,cs,**cap)
            self.assertEqual(r['status'],'UNKNOWN')
            self.assertIsNone(r['certificate'])
            self.assertTrue(r['stats']['budget_limited'])
        self.assertEqual(field_split_refute(10**10,[(1,2,3)])['status'],'UNKNOWN')
        with self.assertRaises(ValueError): field_split_refute(n,cs,max_candidates=True)
