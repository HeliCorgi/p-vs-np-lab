import unittest

from experiments.catalytic_extension_degree import (BinaryField, MODULI,
    evaluate_circuit, fresh_circuit, gatewise_extension, orbit_sum,
    repaired_fresh_extension)


def polynomial_product_mod(a,b,modulus):
    product=0
    for i in range(a.bit_length()):
        for j in range(b.bit_length()):
            if (a>>i)&(b>>j)&1:
                product ^= 1<<(i+j)
    while product.bit_length()>=modulus.bit_length():
        product ^= modulus<<(product.bit_length()-modulus.bit_length())
    return product


class CatalyticExtensionTests(unittest.TestCase):
    def test_field_products_against_independent_polynomial_reduction(self):
        for r,modulus in MODULI.items():
            field=BinaryField(r)
            for a in range(field.q):
                for b in range(field.q):
                    self.assertEqual(field.multiply(a,b),polynomial_product_mod(a,b,modulus))
            for a in range(1,field.q):
                self.assertEqual(field.power(a,field.q-1),1)

    def test_small_circuit_and_exact_failure_for_every_audited_field(self):
        for r in MODULI:
            field=BinaryField(r)
            for x in range(field.q):
                self.assertEqual(gatewise_extension(field,x),field.power(x,field.q-1))
            self.assertEqual([gatewise_extension(field,x) for x in (0,1)],[0,1])
            self.assertEqual(orbit_sum(field,field.q-1,1,0),1)
            self.assertEqual(field.power(0,field.q-1),0)
            self.assertEqual(orbit_sum(field,1,1,0),0)

    def test_averaging_for_arbitrary_low_degree_polynomial(self):
        field=BinaryField(3)
        coefficients=[3,7,5,0,1,4,6]
        def evaluate(x):
            out=0
            for a in reversed(coefficients):
                out=field.multiply(out,x)^a
            return out
        for x in range(8):
            for v in range(8):
                total=0
                for a in range(1,8):
                    total ^= evaluate(field.multiply(a,x)^v)
                self.assertEqual(total,evaluate(v))

    def test_invalid_fields_and_inputs_are_rejected(self):
        for r in (0,1,6,2.0,True):
            with self.assertRaises(ValueError):BinaryField(r)
        field=BinaryField(3)
        for a,b in ((-1,0),(0,8),(1,1.5)):
            with self.assertRaises(ValueError):field.multiply(a,b)
        for x,degree in ((8,0),(1,-1),(1,1.5)):
            with self.assertRaises(ValueError):field.power(x,degree)

    def test_repaired_extension_against_full_boolean_interpolation(self):
        field=BinaryField(3)
        circuit=fresh_circuit(2)
        n,gates,_=circuit
        self.assertTrue(all(len(g)==2 or g[1]!=g[2] for g in gates))
        for seed in range(12):
            point=[(seed+i*3+i*i)%field.q for i in range(n)]
            direct=0
            for word in range(1<<n):
                bits=[(word>>i)&1 for i in range(n)]
                term=evaluate_circuit(field,circuit,bits)
                for value,bit in zip(point,bits):
                    term=field.multiply(term,value if bit else 1^value)
                direct ^= term
            self.assertEqual(repaired_fresh_extension(field,point),direct)


if __name__=='__main__':
    unittest.main()
