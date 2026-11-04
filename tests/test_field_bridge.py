import copy
from itertools import combinations,product
import random
import unittest

from pnp_lab.mixed_modular import mixed_modular_refute,check_field_bridge,_Space,_sparse
from pnp_lab.ternary_flow import mixed_port_flow,scramble
from pnp_lab.four_ports import four_port_flow


class FieldBridgeTests(unittest.TestCase):
    def test_exact_short_equations_against_exhaustive_field_points(self):
        rng=random.Random(140115)
        for p in (2,3):
            pts=list(product(range(p),repeat=5))
            for trial in range(32):
                witness=rng.choice(pts);rows=[];s=_Space(5,p,[])
                for t in range(rng.randint(1,6)):
                    d={j:rng.randint(1,p-1) for j in range(1,6) if rng.randrange(2)}
                    b=sum(a*witness[j-1] for j,a in d.items())%p;rows.append((d,b))
                    res=s.reduce(d,b)
                    if res[0]:self.assertFalse(s.insert(res,t))
                models=[pt for pt in pts if all(sum(a*pt[j-1] for j,a in d.items())%p==b for d,b in rows)]
                for width in (1,2,3,4):
                    actual={(tuple(d.items()),b) for d,b in _sparse(s,width)};expected=set()
                    for k in range(1,(min(width,2) if p==2 else width)+1):
                        for support in combinations(range(1,6),k):
                            for tail in product(range(1,p),repeat=k-1):
                                d=tuple(zip(support,(1,)+tail))
                                bs={sum(a*pt[j-1] for j,a in d)%p for pt in models}
                                if len(bs)==1:expected.add((d,bs.pop()))
                    self.assertEqual(actual,expected)

    def test_no_silent_cross_field_addition_or_spurious_refutation(self):
        n,cs,*_=mixed_port_flow(4);cs,_=scramble(n,cs,None,65)
        r=mixed_modular_refute(n,cs)
        self.assertEqual(r['status'],'UNSAT')
        c=r['certificate'];self.assertTrue(check_field_bridge(n,cs,c))
        cast=next(i for i,node in enumerate(c['nodes']) if node['op']=='boolean')
        wrong=copy.deepcopy(c);wrong['nodes'][cast]['rhs']^=1
        self.assertFalse(check_field_bridge(n,cs,wrong))
        cycle=copy.deepcopy(c);cycle['nodes'][cast]['from']=cast
        self.assertFalse(check_field_bridge(n,cs,cycle))
        bad=copy.deepcopy(c);bad['nodes'][-1]['rhs']=0
        self.assertFalse(check_field_bridge(n,cs,bad))
        _,sat,*_=mixed_port_flow(4,ternary_rhs=1);sat,_=scramble(n,sat,None,65)
        self.assertFalse(check_field_bridge(n,sat,c))
        self.assertEqual(mixed_modular_refute(n,cs,max_short_rows=0)['status'],'UNKNOWN')

    def test_four_ports_and_raw_boolean_safety(self):
        n,cs,_=four_port_flow(4);self.assertEqual(mixed_modular_refute(n,cs)['status'],'UNKNOWN')
        self.assertEqual(mixed_modular_refute(n,cs,bridge_width=4)['status'],'UNSAT')
        rng=random.Random(140247)
        for _ in range(65):
            n=rng.randint(1,6);cs=[tuple(rng.randint(1,n)*rng.choice((-1,1)) for _ in range(rng.randrange(1,4))) for _ in range(rng.randrange(16))]
            r=mixed_modular_refute(n,cs,bridge_width=4)
            if r['status']=='UNSAT':
                self.assertTrue(check_field_bridge(n,cs,r['certificate']))
                self.assertFalse(any(all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in row) for row in cs) for x in range(1<<n)))
