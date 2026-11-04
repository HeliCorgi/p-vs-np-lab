from itertools import product
import unittest

from pnp_lab.parity_shadow import ShadowMatching


class ParityShadowTests(unittest.TestCase):
    def test_syndrome_images_against_raw_signed_cnf(self):
        for k in (2,3,4):
            width=k-1
            closed=ShadowMatching(k); opened=ShadowMatching(k,True)
            self.assertEqual(len(set(closed.binary_clauses())-set(opened.binary_clauses())),k-1)
            self.assertFalse(set(opened.binary_clauses())-set(closed.binary_clauses()))
            for t in (closed,opened):
                conflicts=[(1<<(-a-1)) | (1<<(-b-1)) for a,b in t.binary_clauses()]
                hits=set()
                for x in range(1 << (k*width)):
                    y=None
                    if not any(x & c == c for c in conflicts):
                        y=sum((((x>>(i*width)) & ((1<<width)-1)).bit_count()%2)<<i for i in range(k))
                        hits.add(y)
                    self.assertEqual(t.syndrome_of_matching(x),y)
                self.assertEqual(hits,set(range((1<<k)-int(not t.opened))))
                for s in hits:
                    x=t.lift(s)
                    self.assertTrue(all(x & c != c for c in conflicts))

    def test_every_small_linear_map_including_inconsistent_redundant_rows(self):
        # All 3-by-3 maps, all outputs. Independent direct oracle over the
        # syndrome sets already checked by raw assignment enumeration above.
        twins=[ShadowMatching(3,b) for b in (False,True)]
        for rows in product(range(8),repeat=3):
            ys=[sum(((h & s).bit_count()%2)<<i for i,h in enumerate(rows)) for s in range(8)]
            for b in range(8):
                equations=list(zip(rows,[(b>>i)&1 for i in range(3)]))
                answers=[]
                for t in twins:
                    r=t.query(equations); answers.append(r['status'])
                    want=b in (ys if t.opened else ys[:-1])
                    self.assertEqual(r['status'],'SAT' if want else 'UNSAT')
                    if want:
                        self.assertEqual(ys[t.syndrome_of_matching(r['witness'])],b)
                if len(set(ys))<8:
                    self.assertEqual(*answers)

    def test_many_combined_rows_and_independent_hall_check(self):
        k=64; t=ShadowMatching(k); u=ShadowMatching(k,True)
        # A triangular invertible change of coordinates of the target equations.
        full=[((1<<(i+1))-1,(i+1)%2) for i in range(k)]
        for skip in (0,k//2,k-1):
            sub=full[:skip]+full[skip+1:]
            for twin in (t,u):
                w=twin.query(sub)
                self.assertEqual(w['status'],'SAT')
                s=twin.syndrome_of_matching(w['witness'])
                self.assertTrue(all((s & h).bit_count()%2==b for h,b in sub))
        bad=t.query(full); self.assertEqual(bad['reason'],'unique_syndrome_hall_cut')
        self.assertTrue(t.verify_hall_cut(t.target,bad['cut']))
        self.assertFalse(u.verify_hall_cut(u.target,bad['cut']))
        self.assertFalse(t.verify_hall_cut(t.target^1,bad['cut']))
        self.assertFalse(t.verify_hall_cut(t.target,dict(rows=[0,0],resources=[])))
        self.assertEqual(u.syndrome_of_matching(u.query(full)['witness']),u.target)
