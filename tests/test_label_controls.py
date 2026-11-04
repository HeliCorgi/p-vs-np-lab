import unittest

from pnp_lab.decision_labels import or_cnf, residual_label
from pnp_lab.decision_pruning import solve_pruned
from pnp_lab.label_controls import coupled_core, marked_model, prefix_restriction, tagged_xor
from pnp_lab.residual_controls import satisfies


class TaggedCodecTests(unittest.TestCase):
    def test_raw_existential_conservative_extension(self):
        k=2
        n, source=tagged_xor(k, [(1,2)])
        N, marked=tagged_xor(k, [(1,2)], marked=True)
        projected={w & ((1<<n)-1) for w in range(1<<N) if satisfies(marked, w)}
        self.assertEqual(projected, {w for w in range(1<<n) if satisfies(source, w)})


    def test_signed_core_and_partially_affine_core(self):
        k = 4
        for cs in ([(1,-2,3),(-1,2,4),(1,2,-4)],
                   [(1,-2),(-1,2),(-2,3,-4)]):
            n, h = tagged_xor(k, cs)
            K = tuple(tuple((k+abs(l))*(1 if l>0 else -1) for l in row) for row in cs)
            label = residual_label(n, K)
            for depth in range(k+1):
                for a in range(1 << depth):
                    self.assertEqual(residual_label(n,prefix_restriction(h,depth,a)), label)

    def test_different_marked_partners_have_distinct_visible_models(self):
        k, d = 3, 2
        n, f = tagged_xor(k, coupled_core(k), marked=True)
        hs = [prefix_restriction(f, d, a) for a in range(1 << d)]
        for anchor, idx, j in ((0, 1, 2), (3, 0, 1), (1, 2, 0)):
            left, right = or_cnf(n,hs[anchor],hs[idx]), or_cnf(n,hs[anchor],hs[j])
            # Left witness survives projection to core coords but cannot satisfy
            # the right for ANY choice of the private remaining tag bits.
            w = marked_model(k, idx)
            self.assertTrue(satisfies(left, w))
            for t in range(1 << k):
                self.assertFalse(satisfies(right, (w & ~((1<<k)-1))|t))
            self.assertNotEqual(residual_label(n, left), residual_label(n, right))

    def test_driver_cap_on_same_coupled_core(self):
        k=4
        for locked, mode, expected in ((False,'affine','SAT'),(False,'syntax','UNKNOWN'),(True,'affine','UNKNOWN')):
            n,f=tagged_xor(k,coupled_core(k),marked=locked)
            self.assertEqual(solve_pruned(n,f,max_width=4,label_mode=mode)['status'],expected)
