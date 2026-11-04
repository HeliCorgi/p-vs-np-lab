from itertools import combinations
import unittest

from pnp_lab.layered_barrier import make_layers,completion_lift,blind_lift,graph_controls
from pnp_lab.width_transfer import pull


def restrict(cs,assigned):
    return tuple(tuple(l for l in c if abs(l) not in assigned) for c in cs
                 if not any(assigned.get(abs(l))==(l>0) for l in c))


class LayeredBarrierTests(unittest.TestCase):
    def test_finite_graph_types_have_distinct_signatures_and_no_nontrivial_tiny_cut(self):
        signatures=[]
        for edges in graph_controls():
            adj=[set() for _ in range(10)]
            for a,b in edges:adj[a].add(b);adj[b].add(a)
            self.assertEqual([len(v) for v in adj],[3]*10)
            for size in range(2,6):
                for subset in combinations(range(10),size):
                    verts=set(subset)
                    self.assertGreaterEqual(sum((a in verts)!=(b in verts) for a,b in edges),4)
            def cycle_count(size):
                def walk(path):
                    if len(path)==size:return int(path[0] in adj[path[-1]] and path[1]<path[-1])
                    return sum(walk(path+(v,)) for v in adj[path[-1]] if v>path[0] and v not in path)
                return sum(walk((v,)) for v in range(10))
            signatures.append(tuple(cycle_count(j) for j in (4,5,6)))
        self.assertEqual(len(set(signatures)),4)

    def test_source_completion_lifts_all_raw_and_blind_prefixes_and_missing_fixed_module(self):
        graphs=graph_controls();inst=make_layers(10,(graphs[:2],graphs[2:]))
        self.assertEqual((inst['n'],len(inst['cnf'])),(222,320))
        for word in range(4):
            base,img=completion_lift(inst,word)
            _,enc,gates,copy=blind_lift(inst,word)
            axioms=set(map(frozenset,base))
            self.assertEqual(len(axioms),80)
            for d in range(3):
                for f,gs,vmap in ((inst['cnf'],(1,2),img),(enc,gates,copy)):
                    fixed={gs[i]:bool(word>>i&1) for i in range(d)}
                    restricted=restrict(f,fixed)
                    for c in restricted:
                        tc=pull(c,vmap)
                        self.assertTrue(tc is None or tc in axioms)
                for y in range(1<<d):
                    if y==word%(1<<d):continue
                    j=next(i for i in range(d) if (word^y)>>i&1)
                    chosen={2*i+(word>>i&1) for i in range(2)}
                    self.assertNotIn(2*j+(y>>j&1),chosen)
