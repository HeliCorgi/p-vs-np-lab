import itertools
import random
import unittest
from unittest.mock import patch
from pnp_lab.decision_pruning import solve_pruned


def models(n, clauses):
    return {w for w in range(1<<n) if all(any(bool(w & (1<<(abs(l)-1)))==(l>0)
                                               for l in c) for c in clauses)}


def cube(vs):
    return tuple(tuple(s*v for s,v in zip(signs,vs)) for signs in itertools.product((-1,1),repeat=3))


class DecisionPruningTests(unittest.TestCase):
    def test_oracle_and_budget(self):
        rng=random.Random(142937)
        for i in range(96):
            n=rng.randrange(1,6); cs=[tuple(rng.choice((-1,1))*rng.randrange(1,n+1)
                for _ in range(rng.randrange(1,4))) for _ in range(rng.randrange(1,19))]
            order=list(range(n));rng.shuffle(order)
            expected='SAT' if models(n,cs) else 'UNSAT'
            for anchors in (True,False):
                r=solve_pruned(n,cs,order=order,max_width=None,label_mode=('syntax','affine','blocked')[i % 3],
                               anchor_collisions=anchors)
                self.assertEqual(r['status'],expected)
                self.assertEqual(r['widths'][-1],0)
                if not anchors:self.assertEqual(r['stats']['or_labels'],0)
            self.assertIn(solve_pruned(n,cs,order=order,max_width=1)['status'],(expected,'UNKNOWN'))

    def test_real_anchor_collision_with_status_preservation(self):
        # Four leaves: A, A&u, A&v, A&u&v. Their syntax differs but
        # A OR each partner simplifies (by subsumption) to exactly A.
        for a,want in [(cube([3,4,5]),'UNSAT'),(cube([3,4,5])[:-1],'SAT')]:
            root=a+((-1,6),(-2,7))
            self.assertEqual(bool(models(7,root)),want=='SAT')
            r=solve_pruned(7,root,label_mode='syntax',max_width=2)
            self.assertGreater(r['stats']['anchor_merges'],0)
            self.assertEqual(r['status'],want)
            q=solve_pruned(7,root,label_mode='syntax',anchor_collisions=False,max_width=2)
            self.assertEqual(q['status'],'UNKNOWN')

    def test_sound_anchor_answers_and_no_witness(self):
        # Inject a SAT-preserving label that classifies width>3 *queries*,
        # but leaves nontrivial 3-CNFs opaque. Unlike returning a truth
        # bit on all queries, this actually exercises the anchor rules.
        def locally_decide(n,h,mode):
            if max(map(len,h),default=0)>3:
                return ('YES',) if models(n,h) else ('NO',)
            return ('raw',h)
        with patch('pnp_lab.decision_pruning.residual_label',locally_decide):
            # The common width-three core controls the SAT bit; branches
            # have separate distinguishing clauses whose disjunction has
            # width four, triggering the small independent oracle.
            for core,expected in [(cube([4,5,6]),'UNSAT'),(cube([4,5,6])[:-1],'SAT')]:
                h=core+((1,2,3),(-1,7,8))
                r=solve_pruned(8,h,label_mode='syntax',max_width=None)
                self.assertEqual(r['status'],expected)
                self.assertEqual(r['stats']['anchor_true' if expected=='SAT' else 'anchor_false'],1)
                self.assertNotIn('witness',r)

    def test_unconditional_or_answer_with_actual_classifier(self):
        # On splitting v, H0=x OR y, H1=not x OR z. Both are opaque,
        # but their disjunction is a tautology, hence recognized as YES.
        h=((1,2,3),(-1,-2,4))
        r=solve_pruned(4,h,label_mode='affine',max_width=1)
        self.assertEqual((r['status'],r['stats']['anchor_true']),('SAT',1))
        self.assertEqual(solve_pruned(4,h,label_mode='affine',max_width=1,
                                      anchor_collisions=False)['status'],'UNKNOWN')

    def test_invalid_and_constant_inputs(self):
        for n,cs,kw in [(1,[(0,)],{}),(1,[(True,)],{}),(2,[(3,)],{}),
                        (1,[(1,1,1,1)],{}),(0,[''],{}),(True,[],{}),
                        (1,[],{'order':[]}), (1,[],{'order':[True]}),
                        (2,[],{'order':[0,0]}),(1,[],{'max_width':True}),
                        (0,[],{'label_mode':'semantic-oracle'}),(1,[],{'anchor_collisions':0})]:
            with self.assertRaises(ValueError):solve_pruned(n,cs,**kw)
        self.assertEqual(solve_pruned(0,[],max_width=0)['status'],'SAT')
        self.assertEqual(solve_pruned(0,[()],max_width=0)['status'],'UNSAT')
