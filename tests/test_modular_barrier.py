import random
import unittest
from itertools import combinations,product
from pnp_lab.modular_barrier import (check_tree,forest_ball,hall_free_cube,incidence_girth,line_fixture,
                                     raw_search,satisfies,stretched_image,lift_stretched)


class LocalBarrierTests(unittest.TestCase):
    def test_forest_girth_and_simultaneous_single_bit_flips(self):
        forest=((1,2,-3),(-2,-4,5),(-2,6,7),(-6,8,-9))
        x=forest_ball(10,forest)
        self.assertIsNone(incidence_girth(10,forest))
        self.assertTrue(all(satisfies(forest,x^(1<<i)) for i in range(10)))
        cycle=forest+((1,-5,10),)
        self.assertIsNone(forest_ball(10,cycle))
        self.assertEqual(incidence_girth(10,cycle),6)

    def test_hall_squares_and_quadratic_coefficients(self):
        rng=random.Random(1400)
        for _ in range(30):
            # A forest with one shared variable at each attachment.
            cs=tuple(tuple(l if rng.randrange(2) else -l for l in row)
                     for row in ((1,2,3),(1,4,5),(3,6,7)))
            for i,j in combinations(range(1,8),2):
                base=hall_free_cube(7,cs,(i,j));u=1<<(i-1);v=1<<(j-1)
                self.assertIsNotNone(base)
                pts=(base,base|u,base|v,base|u|v)
                self.assertTrue(all(satisfies(cs,w) for w in pts))
                # Mixed second difference isolates the planted quadratic monomial
                # even when its field coefficient cancels in one characteristic.
                def poly(x):
                    xi=int(bool(x&u));xj=int(bool(x&v));return 7+2*xj+6*xi*xj+sum((a+1)*((x>>a)&1) for a in range(7))
                sums=[poly(w) for w in pts]
                self.assertEqual(sums[0]+sums[3]-sums[1]-sums[2],6)
        self.assertIsNone(hall_free_cube(3,[(1,2,3)],(1,2,3)))

    def test_raw_tree_and_pin(self):
        n,f=line_fixture(0);sat,_=raw_search(f[:151]);model,t=raw_search(f[:152])
        self.assertTrue(satisfies(f[:151],sat));self.assertIsNone(model)
        self.assertTrue(check_tree(n,f[:152],t))
        self.assertFalse(check_tree(n,f[:151],t))
        self.assertFalse(check_tree(n,f[:152],(t[0],t[1],t[1])))
        self.assertEqual(incidence_girth(n,f[:152]),6)

    def test_wiring_and_lifts(self):
        n,cs=line_fixture(0);p=cs[:151];false=cs[151][0];word,_=raw_search(p)
        src=((1,2,3),(-1,2,-3))
        m,rows,reps,starts=stretched_image(3,src,2,n,p,false)
        self.assertTrue(starts)
        self.assertEqual(incidence_girth(m,rows),6)
        for x in range(8):
            self.assertEqual(satisfies(src,x),satisfies(rows,lift_stretched(x,word,reps,starts)))
