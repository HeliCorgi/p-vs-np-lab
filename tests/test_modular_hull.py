import copy
from itertools import combinations, product
import json
import random
import unittest

from pnp_lab.modular_hull import (
    check_modular_hull, check_modular_row, collect_modular_rows,
    discover_scopes, modular_hull_refute,
)


def _holds(cnf,point):
    return all(any(bool((point>>(abs(l)-1))&1)==(l>0) for l in row) for row in cnf)


def _k4(defect,seed):
    """Small independently built P3 flow; all-zero trit word is valid for defect=0."""
    edges=list(combinations(range(4),2));n=3*len(edges)
    cs=[]
    for e in range(len(edges)):
        vs=tuple(range(3*e+1,3*e+4))
        cs.append(vs)
        cs.extend((-v,-w) for v,w in combinations(vs,2))
    for i in range(4):
        star=[(e,1 if u==i else -1) for e,(u,v) in enumerate(edges) if i in (u,v)]
        for abc in product(range(3),repeat=3):
            if sum(sign*t for t,(_,sign) in zip(abc,star))%3!=int(i==0)*defect:
                cs.append(tuple(-(3*e+t+1) for t,(e,_) in zip(abc,star)))
    rng=random.Random(seed);perm=list(range(1,n+1));rng.shuffle(perm)
    perm=[v*(-1 if rng.getrandbits(1) else 1) for v in perm]
    f=[tuple(perm[abs(l)-1]*(1 if l>0 else -1) for l in c) for c in cs];rng.shuffle(f)
    x=sum(1<<(abs(l)-1) for i,l in enumerate(perm) if (i%3==0)==(l>0))
    return n,f,x


class ModularHullTests(unittest.TestCase):
    def test_complete_three_bit_boolean_images_over_each_field(self):
        # Every 3-bit Boolean relation is represented by its forbidden-point
        # CNF. Compare the extension to arbitrary field points against EVERY
        # local affine equation true on the Boolean models, not another GF solver.
        bits=tuple(product((0,1),repeat=3))
        for p in (2,3):
            points=list(product(range(p),repeat=3))
            for select in range(256):
                models=[x for i,x in enumerate(bits) if select>>i&1]
                f=[tuple((j+1)*(-1 if v else 1) for j,v in enumerate(x))
                   for i,x in enumerate(bits) if not select>>i&1]
                rows,_=collect_modular_rows(3,f,prime=p)
                self.assertTrue(all(check_modular_row(3,f,p,r) for r in rows))
                result={x for x in points if all(sum(a*x[i-1] for i,a in zip(r['scope'],r['coeff']))%p==r['rhs'] for r in rows)}
                exact=set(points)
                for v in points:
                    possible={sum(a*b for a,b in zip(v,x))%p for x in models}
                    if len(possible)==1:
                        rhs=next(iter(possible));exact={x for x in exact if sum(a*b for a,b in zip(v,x))%p==rhs}
                if not models:exact.clear()
                self.assertEqual(result,exact,(p,select))

    def test_scrambled_flow_and_strict_proof_replay(self):
        for seed in (22,519):
            n,f,_=_k4(1,seed)
            r=modular_hull_refute(n,f,prime=3)
            self.assertEqual(r['status'],'UNSAT')
            proof=json.loads(json.dumps(r['certificate']))
            self.assertTrue(check_modular_hull(n,f,proof))
            self.assertGreater(len(proof['terms']),1)
            self.assertFalse(check_modular_hull(n,f,dict(proof,terms=proof['terms'][1:])))
            bad=copy.deepcopy(proof);bad['terms'][0]['rhs']=(bad['terms'][0]['rhs']+1)%3
            self.assertFalse(check_modular_hull(n,f,bad))
            self.assertFalse(check_modular_hull(n,f,dict(proof,prime=5)))
            bad=copy.deepcopy(proof);bad['terms'][0]['clauses'][0]=-1
            self.assertFalse(check_modular_hull(n,f,bad))
            self.assertEqual(modular_hull_refute(n,f,prime=2)['status'],'UNKNOWN')
            n,even,x=_k4(0,seed)
            self.assertTrue(_holds(even,x))
            self.assertFalse(check_modular_hull(n,even,proof))
            self.assertEqual(modular_hull_refute(n,even)['status'],'UNKNOWN')

    def test_limits_missing_literals_and_local_contradiction(self):
        n,f,_=_k4(1,2)
        r=modular_hull_refute(n,f,max_scopes=0)
        self.assertTrue(r['stats']['budget_limited'])
        self.assertEqual((r['status'],r['stats']['local_assignments']),('UNKNOWN',0))
        self.assertLessEqual(max(map(len,discover_scopes(n,f))),9)
        for cnf in ([(1,1),(-1,-1)],[(1,-1),()], [()]):
            r=modular_hull_refute(4,cnf)
            self.assertTrue(check_modular_hull(4,cnf,r['certificate']))
        self.assertEqual(modular_hull_refute(0,[])['status'],'UNKNOWN')
        for p in (True,1,4,'3'):
            with self.assertRaises(ValueError):modular_hull_refute(2,[],prime=p)
        with self.assertRaises(ValueError):modular_hull_refute(2,[(3,)])
        with self.assertRaises(ValueError):modular_hull_refute(2,[],max_scopes=False)
