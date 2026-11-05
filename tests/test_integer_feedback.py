from copy import deepcopy
from itertools import product
from random import Random
import unittest

from pnp_lab.integer_feedback import (check_integer_feedback, integer_feedback_refute,
                                      learn_anchor_clauses, replay_feedback_lemmas)


def tiny_network(odd=True):
    """Independent test construction: K4 checks with two fresh signs per clause."""
    core, raw, fresh = [], [], 6
    for i, vs in enumerate(((1,2,3), (1,4,5), (2,4,6), (3,5,6))):
        charge = int(odd and i == 0)
        j = 0
        for bits in product((0,1), repeat=3):
            if sum(bits) % 2 == charge:
                continue
            c = tuple(-v if b else v for v,b in zip(vs,bits))
            core.append(c)
            end = j % 3
            first = tuple(x for k,x in enumerate(c) if k != end)
            s, t = fresh+1, fresh+2
            fresh += 2
            raw.extend(((*first, s), (-t, -s), (t, c[end])))
            j += 1
    return fresh, raw, core


def satisfies(word, rows):
    return all(any(bool((word >> (abs(l)-1)) & 1) == (l>0) for l in c) for c in rows)


class IntegerFeedbackTests(unittest.TestCase):
    def test_reconstruction_and_two_independent_arithmetic_paths(self):
        n, raw, core = tiny_network()
        p = learn_anchor_clauses(n, raw)
        self.assertTrue(p['complete'])
        self.assertEqual(p['stats']['anchors'], 6)
        self.assertEqual(p['stats']['learned_clauses'], 16)
        self.assertEqual(p['stats']['path_steps'], 32)
        self.assertEqual(set(map(frozenset,p['clauses'])), set(map(frozenset,core)))
        self.assertEqual(tuple(map(tuple,p['clauses'])), replay_feedback_lemmas(n,raw,p['lemmas']))
        for parity, backend in ((True,'parity_sum'),(False,'integer_hull')):
            result = integer_feedback_refute(n, iter(raw), use_parity_sum=parity, use_signed_column=False)
            self.assertEqual((result['status'], result['stats']['backend']), ('UNSAT', backend))
            self.assertTrue(check_integer_feedback(n, raw, result['certificate']))
        good = integer_feedback_refute(n, tiny_network(False)[1], use_signed_column=False)
        self.assertEqual(good['status'],'UNKNOWN')
        self.assertIsNone(good['witness'])
        self.assertIsNone(good['certificate'])

    def test_original_clause_binding_tampering_and_sparse_renaming(self):
        n, raw, _ = tiny_network()
        def lit(l):
            return (1 if l>0 else -1) * ((-1)**abs(l)) * (10**12 + 7*abs(l))
        n = 10**12+7*n
        raw = [tuple(lit(l) for l in reversed(c)) for c in reversed(raw)]
        q = integer_feedback_refute(n,raw)
        self.assertEqual(q['status'],'UNSAT')
        cert = q['certificate']
        self.assertTrue(check_integer_feedback(n, raw, cert))
        # Bind learned syntax, raw indices, signed edges and arithmetic coordinates.
        for who in ('start','edge_direction','edge_id','conclusion','source','scope',
                    'weight','wrong_variables','boolean_path_id'):
            t = deepcopy(cert)
            a = t['lemmas'][0]
            if who=='start': a['start'] *= -1
            elif who=='edge_direction': a['path'][0] *= -1
            elif who=='edge_id': a['path'][0] = 0
            elif who=='conclusion': a['clause'][0] *= -1
            elif who=='source': a['raw'] = len(raw)
            elif who=='scope': t['integer']['terms'][0]['scope'][0] = n+1
            elif who=='weight': t['integer']['terms'][0]['weight'] = 0
            elif who=='wrong_variables': t['variables'] = n+1
            else: a['path'][0] = True
            self.assertFalse(check_integer_feedback(n,raw,t),who)
        _, even, _ = tiny_network(False)
        even = [tuple(lit(l) for l in reversed(c)) for c in reversed(even)]
        self.assertFalse(check_integer_feedback(n,even,cert))

    def test_one_way_semantics_against_raw_truth_tables(self):
        rng = Random(1701)
        positive_cases = checked_words = newly_learned = 0
        for _ in range(80):
            rows = [(1,2,3),(-1,-2,-3), (1,2,4),(-4,-5),(5,3)]
            for j in range(rng.randrange(5)):
                a,b = rng.sample(range(1,6),2)
                rows.append((rng.choice((-a,a)),rng.choice((-b,b))))
            rng.shuffle(rows)
            p = learn_anchor_clauses(5, rows)
            self.assertTrue(p['complete'])
            learned = replay_feedback_lemmas(5,rows,p['lemmas'])
            newly_learned += p['stats']['learned_clauses']
            models = [x for x in range(32) if satisfies(x,rows)]
            positive_cases += bool(models)
            checked_words += len(models)
            for x in models: self.assertTrue(satisfies(x,learned))
            result = integer_feedback_refute(5, rows, use_signed_column=False)
            if result['status']=='UNSAT':
                self.assertFalse(models)
                self.assertTrue(check_integer_feedback(5,rows,result['certificate']))
        self.assertGreater(positive_cases,40)
        self.assertGreater(checked_words,150)
        self.assertGreater(newly_learned,0)

    def test_simple_unsigned_support_is_an_entire_blind_class(self):
        from pnp_lab.simple_support import simple_support_image
        for sat, formula in ((False, [(1,),(-1,)]),(True, [(1,)])):
            n, cs, _ = simple_support_image(1, formula)
            self.assertEqual(any(satisfies(w,cs) for w in range(1 << n)),sat)
            out = integer_feedback_refute(n,cs)
            self.assertEqual(out['status'],'UNKNOWN')
            self.assertEqual(out['stats']['binary_arcs'],0)
            self.assertEqual(out['stats']['parity']['parity_rows'],0)
            self.assertEqual(out['stats']['signed_column']['exact_rows'],0)
            self.assertEqual(out['stats']['integer']['local_rows'],0)
            self.assertFalse(out['stats']['budget_limited'])

    def test_budgets_raw_normalization_and_independent_leaf_rule(self):
        n,raw,_=tiny_network()
        for options in ({'max_edges':0},{'max_lemmas':0},{'max_path_steps':1}):
            out=integer_feedback_refute(n,raw,**options)
            self.assertEqual(out['status'],'UNKNOWN')
            self.assertTrue(out['stats']['budget_limited'])
            self.assertIsNone(out['certificate'])
        cert=integer_feedback_refute(n,raw)['certificate']
        for options in ({'max_lemmas':15},{'max_path_steps':31}):
            self.assertFalse(check_integer_feedback(n,raw,cert,**options))
        # Anchor detection uses distinct signed ternaries, ignoring copies/tautologies.
        p=learn_anchor_clauses(4, [(1,2,3),(3,2,1),(-1,1,4),(-3,4)])
        self.assertEqual((p['stats']['anchors'],p['clauses']),(0,[]))
        # The semantic verifier can check a valid lemma regardless of that heuristic.
        lemmas=[dict(raw=0,start=3,path=[4],clause=[1,2,4])]
        self.assertEqual(replay_feedback_lemmas(4,[(1,2,3),(3,2,1),(-1,1,4),(-3,4)],lemmas),((1,2,4),))
        for c in ([], [(1,1,-1)], [(1,),(-1,)]):
            # A missed unanchored contradiction means UNKNOWN, not SAT.
            self.assertEqual(integer_feedback_refute(1,c,use_signed_column=False)['status'],'UNKNOWN')
        false=integer_feedback_refute(0,[()],use_signed_column=False)
        self.assertTrue(check_integer_feedback(0,[()],false['certificate']))
        with self.assertRaises(ValueError):
            integer_feedback_refute(n,raw,max_path_steps=True)
