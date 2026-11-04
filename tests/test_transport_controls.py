import unittest
from pnp_lab.transport_controls import directed_tags,flip_hard_siblings,coherent
from pnp_lab.label_controls import prefix_restriction
from pnp_lab.witness_transport import check_transport,find_flip_transport,apply_transport,KIND


class TransportControls(unittest.TestCase):
    def test_proper_oneway_block(self):
        n,f=directed_tags(1,shield=False)
        a,b=[prefix_restriction(f,1,i) for i in (1,0)]  # equality => OR after a flip
        self.assertFalse(check_transport(n,a,b,dict(kind=KIND,images=[1,2,3])))
        cert=find_flip_transport(n,a,b)
        self.assertIsNotNone(cert)
        for w in range(1<<n):
            if coherent(w,a): self.assertTrue(coherent(apply_transport(n,cert,w),b))
        for v in range(1<<n):
            self.assertFalse(check_transport(n,b,a,dict(kind=KIND,
                images=[(-1 if v>>i&1 else 1)*(i+1) for i in range(n)])))
        self.assertTrue(check_transport(n,b,a,dict(kind=KIND,images=[True]*n)))

    def test_gate_reduction_all_short_and_degenerate_forms(self):
        formulas=[[],[()],[(1,),(-1,)],[(1,-1,2)],[(1,1,1),(-1,)],[(1,2),(-1,-2)]]
        for f in formulas:
            n=2;mx,rows=flip_hard_siblings(n,f)
            src,tar=[prefix_restriction(rows,1,b) for b in (1,0)]
            self.assertEqual([w for w in range(0,1<<mx,2) if coherent(w,src)],[0])
            for mask in range(1<<n):
                self.assertEqual(coherent(mask,f),any(coherent((mask<<1)|(q<<(n+1)),tar)
                    for q in range(1<<(mx-n-1))))
            for w in range(0,1<<mx,2):
                c=dict(kind=KIND,images=[(-1 if w>>i&1 else 1)*(i+1) for i in range(mx)])
                self.assertEqual(check_transport(mx,src,tar,c),coherent(w,tar))

    def test_shield_admits_exactly_the_same_old_assignments(self):
        k=1;n,plain=directed_tags(k,[(1,)],shield=False)
        mx,rich=directed_tags(k,[(1,)])
        for w in range(1<<n):
            # Helpers are p,q and then two copies per a,z,p,q in insertion order.
            def lift(h):
                base = w | (h<<n)
                return base | sum(((base>>(j-1))&1)*3 << (5+2*(j-2)) for j in range(2,6))
            self.assertEqual(coherent(w,plain),any(coherent(lift(h),rich) for h in range(4)))
