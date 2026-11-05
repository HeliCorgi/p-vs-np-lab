import unittest

from pnp_lab.support_localization import support_audit


class SupportAuditTests(unittest.TestCase):
    def test_semantic_minimum_is_not_an_arbitrary_first_support(self):
        cs=[(1,2,4),(-4,1,3),(1,2,5),(-5,1,3)]
        r=support_audit(5,cs,[(1,2,3)],width=3,s=4)
        goal=next(x for x in r['lines'] if x['clause']==[1,2,3])
        self.assertEqual(goal['minimum_raw_supports'],[[0,1],[2,3]])
        self.assertEqual(r['scopes'][0]['pooled_raw_ids'],[0,1,2,3])
        self.assertFalse(r['boundary_condition'])

    def test_structural_support_can_exceed_pooled_semantic_minima(self):
        cs=[(1,2,3),(1,4,5),(1,6,7)]
        r=support_audit(7,cs,[(2,3,4,5,6,7)],width=4,s=6,delta=(2,1))
        p=r['scopes'][0]
        self.assertEqual((r['closure_lines'],p['lines'],p['pooled_raw_ids']),(3,[],[]))
        self.assertEqual(p['common_raw_ids'],[0,1,2])
        self.assertTrue(p['all_square_faces'] and p['common_entails'])
        # Check shared ambient witnesses, not just four separately projected
        # words with different assignments on the other coordinates.
        for f in p['square_faces']:
            i,j=f['axes']
            base=f['base']
            for word in (base,base^(1<<(i-1)),base^(1<<(j-1)),base^(1<<(i-1))^(1<<(j-1))):
                self.assertTrue(all(any((word>>(l-1))&1 for l in c) for c in cs))

    def test_short_axioms_and_false_face(self):
        r=support_audit(2,[(1,2)],[(1,2)],width=2,s=2,delta=(2,1))
        self.assertTrue(r['boundary_condition'] and r['scopes'][0]['all_unit_edges'])
        self.assertFalse(r['proper_ternary'] or r['scopes'][0]['all_square_faces'])
        pinned=support_audit(1,[(1,)],[(1,)],width=1,s=2)
        self.assertFalse(pinned['scopes'][0]['all_unit_edges'])

    def test_caps_protect_evidence_and_unused_coordinate_numbers(self):
        n=10**12
        cs=[(n,1,2),(-n,3,4)]
        r=support_audit(n,cs,[(1,2,3,4)],width=4,s=4)
        self.assertEqual(r['labels'],[1,2,3,4,n])
        self.assertEqual(r['counts']['explicit_cube_words'],32)
        for limit in (dict(max_rows=0),dict(max_work=1),dict(max_table_bits=1)):
            cap=support_audit(n,cs,[(1,2,3,4)],width=4,s=4,**limit)
            self.assertEqual(cap['status'],'UNVERIFIED')
            self.assertNotIn('scopes',cap)
        for bad in [[(1,-1)],[(2,2)],[()]]:
            with self.assertRaises(ValueError):
                support_audit(3,bad,[],width=4,s=3)
