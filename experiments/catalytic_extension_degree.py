#!/usr/bin/env python3
"""Audit a proposed repair in a uniform-time lower-bound investigation.

Known source: R. Williams, Simulating Time With Square-Root Space,
https://arxiv.org/abs/2502.17779v1, Theorem 1.1, Section 5 and Appendix A.
The theorem is TIME[t] contained in SPACE[O(sqrt(t log t))] for multitape
Turing machines. It does NOT preserve time t. Section 5 explicitly describes
2^Theta(b) time for the implemented extension evaluation on a b-step block.
Its space-hierarchy corollary supplies near-quadratic time lower bounds for
linear-space languages, not NP membership or exclusion of every polynomial.

Attempted repair: replace Boolean gates by field arithmetic to get a small
arithmetic circuit, and use that extension in the existing catalytic averaging
step without changing its field/degree budget. This is an executable test of
that repair, not a new lower bound, a simulator, or a novelty claim.

For F=GF(q), q=2^r, the averaging identity used here is
  sum_{a in F*} P(a*x+v) = P(v),  if deg P < q-1.
For a monomial after expansion, the positive powers a^j with 1<=j<q-1 sum
to zero over the cyclic group F*, while the constant term is repeated q-1
times, which is 1 in characteristic two. Linearity proves the identity.

A Boolean circuit G_1(x)=x, G_{i+1}(x)=AND(AND(G_i(x),G_i(x)),x)
uses 2(r-1) gates at stage r and computes x on {0,1}. Its gatewise arithmetic
extension is P_r(x)=x^(2^r-1). At x=1,v=0 every summand is 1, hence the sum
is 1, whereas P_r(0)=0. Thus a compact arithmetic extension can violate the
exact identity that licenses the space-saving procedure. This holds for all
r>=2; the finite checks below are independent exact field calculations.

The same Boolean function has the trivial degree-one extension P(x)=x, which
passes the identity. This counterexample rejects ONLY the automatic gatewise
replacement with an unchanged degree budget. It does not lower-bound all
extension constructions, time-space simulations, or algorithms for SAT.
Increasing the field, or constructing a different extension, needs fresh
time/space accounting. Neither is implemented as a general repair here.

Further repair check (to avoid relying only on removable duplicate gates):
start g=x_1,h=x_2; for i=1..r-1 set t=x_0*g*h, g=t XOR z_i, h=t XOR w_i,
with fresh variables z_i,w_i. There are 2r+1 inputs and 10(r-1) ordinary
AND/OR/NOT gates; no binary gate has identical input wires. On the affine
line x_0=x_1=x_2=a, z_i=w_i=0, the gatewise extension is again a^(2^r-1).
Thus even this version fails averaging. For every r>=4, its input count is below
q-1, so a genuine multilinear extension would meet the degree condition.

We construct that extension efficiently for THIS family: condition on the
one reused input x_0, then propagate weights on the four Boolean states (g,h),
introducing each fresh variable exactly once. Finally interpolate x_0 once.
The resulting polynomial has degree <=2r+1, O(r) field operations and a
constant number of state registers. It agrees with the original Boolean
circuit by summing the weights of its deterministic trajectories. Hence it
does satisfy averaging. This is a standard finite-state transfer computation,
not a general low-degree extension compiler: arbitrary circuits need not
have this fixed-size intermediate state. The control checks an actual repair
as well as its cost; neither version yields an NP time lower bound.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
from pathlib import Path


# Fixed irreducible polynomials over F2; every nonzero element is also checked
# for an inverse in the audit. This module is not a general field constructor.
MODULI = {2: 0b111, 3: 0b1011, 4: 0b10011, 5: 0b100101}


@dataclass(frozen=True)
class BinaryField:
    r: int

    def __post_init__(self):
        if type(self.r) is not int or self.r not in MODULI:
            raise ValueError('supported field dimensions are 2, 3, 4, 5')

    @property
    def q(self):
        return 1 << self.r

    def multiply(self, a, b):
        if any(type(x) is not int or not 0<=x<self.q for x in (a,b)):
            raise ValueError('field element out of range')
        result=0
        while b:
            if b&1:
                result ^= a
            a <<= 1
            if a&self.q:
                a ^= MODULI[self.r]
            b >>= 1
        return result

    def power(self, x, degree):
        if type(degree) is not int or degree<0:
            raise ValueError('nonnegative integer exponent required')
        if type(x) is not int or not 0<=x<self.q:
            raise ValueError('field element out of range')
        result=1
        while degree:
            if degree&1:
                result=self.multiply(result,x)
            x=self.multiply(x,x)
            degree >>= 1
        return result


def orbit_sum(field, degree, x, v):
    total=0
    for a in range(1,field.q):
        total ^= field.power(field.multiply(a,x)^v,degree)
    return total


def gatewise_extension(field, x):
    value=x
    for _ in range(field.r-1):
        value=field.multiply(field.multiply(value,value),x)
    return value


def fresh_circuit(r):
    """An ordinary Boolean DAG without duplicate fan-ins or duplicate gates."""
    n=2*r+1
    gates=[]
    def add(op,*parents):
        gates.append((op,*parents))
        return n+len(gates)-1
    def xor(a,b):
        both=add('AND',a,b)
        either=add('OR',a,b)
        inv=add('NOT',both)
        return add('AND',either,inv)
    g,h=1,2
    for i in range(1,r):
        product=add('AND',g,h)
        t=add('AND',0,product)
        g=xor(t,2*i+1)
        h=xor(t,2*i+2)
    assert all(len(gate)==2 or gate[1]!=gate[2] for gate in gates)
    assert len(set(gates))==len(gates)
    return n,tuple(gates),g


def evaluate_circuit(field, circuit, values):
    n,gates,output=circuit
    if len(values)!=n:
        raise ValueError('wrong number of input values')
    wires=list(values)
    for op,*parents in gates:
        a=wires[parents[0]]
        if op=='NOT':
            wires.append(1^a)
        else:
            b=wires[parents[1]]
            product=field.multiply(a,b)
            wires.append(product if op=='AND' else a^b^product)
    return wires[output]


def repaired_fresh_extension(field, values):
    """Multilinear extension via conditioning plus four-state propagation."""
    if len(values)<5 or len(values)%2!=1:
        raise ValueError('expected 2r+1 inputs, r>=2')
    def weight(value,bit):
        return value if bit else 1^value
    output=0
    for fixed in (0,1):
        states={(g,h):field.multiply(weight(values[1],g),weight(values[2],h))
                for g in (0,1) for h in (0,1)}
        for index in range(3,len(values),2):
            after={(g,h):0 for g in (0,1) for h in (0,1)}
            for (g,h),old in states.items():
                t=fixed & g & h
                for z in (0,1):
                    for w in (0,1):
                        transition=field.multiply(weight(values[index],z),weight(values[index+1],w))
                        after[t^z,t^w] ^= field.multiply(old,transition)
            states=after
        value=states[1,0]^states[1,1]
        output ^= field.multiply(weight(values[0],fixed),value)
    return output


def fresh_repair_audit(r):
    field=BinaryField(r)
    circuit=fresh_circuit(r)
    n,gates,_=circuit
    assert n<field.q-1
    raw_sum=fixed_sum=0
    for a in range(1,field.q):
        values=[a,a,a]+[0]*(n-3)
        raw=evaluate_circuit(field,circuit,values)
        fixed=repaired_fresh_extension(field,values)
        assert raw==field.power(a,field.q-1)
        # With all fresh inputs zero, the Boolean function is x_0*x_1*x_2.
        assert fixed==field.power(a,3)
        raw_sum ^= raw
        fixed_sum ^= fixed
    assert (raw_sum,fixed_sum)==(1,0)
    boolean_checks=0
    for word in range(1<<n):
        values=[(word>>i)&1 for i in range(n)]
        assert evaluate_circuit(field,circuit,values)==repaired_fresh_extension(field,values)
        boolean_checks+=1
    # Exact deterministic finite-field controls at non-Boolean vector inputs.
    vectors=[]
    for seed in range(12):
        x=[(seed*(i+1)+i*i+3)%field.q for i in range(n)]
        v=[(seed+i*5+1)%field.q for i in range(n)]
        total=0
        for a in range(1,field.q):
            total ^= repaired_fresh_extension(field,[field.multiply(a,u)^w for u,w in zip(x,v)])
        assert total==repaired_fresh_extension(field,v)
        vectors.append(dict(catalyst=x,target=v,result=total))
    return dict(r=r,inputs=n,ordinary_gates=len(gates),
                duplicate_binary_fanins=0,duplicate_gate_records=0,
                gatewise_restriction_degree=field.q-1,
                repaired_degree_upper_bound=n,
                gatewise_orbit_sum=raw_sum,repaired_orbit_sum=fixed_sum,
                required_value=0,boolean_assignments_checked=boolean_checks,
                repaired_vector_orbit_checks=vectors,
                repair_state_width=4,conditioned_shared_inputs=1,
                repair_field_multiplication_bound=64*(r-1)+10,
                scope='Linear-operation repair for this fixed-state family only; '
                      'no general extension compiler or new lower bound.')


def audit_field(r):
    field=BinaryField(r)
    q=field.q
    for a in range(1,q):
        assert sum(field.multiply(a,b)==1 for b in range(1,q))==1
    positive=negative=zero_catalyst=repair=0
    for x in range(q):
        assert gatewise_extension(field,x)==field.power(x,q-1)
        for v in range(q):
            for degree in range(q-1):
                assert orbit_sum(field,degree,x,v)==field.power(v,degree)
                positive+=1
            matches=orbit_sum(field,q-1,x,v)==field.power(v,q-1)
            assert matches == (x==0)
            negative+=not matches
            zero_catalyst+=matches
            assert orbit_sum(field,1,x,v)==v
            repair+=1
    assert all(gatewise_extension(field,x)==x for x in (0,1))
    return dict(r=r, field_size=q, modulus=MODULI[r],
                boolean_gates=2*(r-1), gatewise_degree=q-1,
                required_degree_strictly_below=q-1,
                low_degree_monomial_checks=positive,
                failed_high_degree_checks=negative,
                high_degree_zero_catalyst_checks=zero_catalyst,
                replacement_linear_extension_checks=repair,
                boolean_function='identity',
                explicit_failure=dict(x=1,v=0,orbit_sum=orbit_sum(field,q-1,1,0),
                                      required_value=field.power(0,q-1)))


def audit():
    fields=[audit_field(r) for r in MODULI]
    repairs=[fresh_repair_audit(r) for r in (4,5)]
    return dict(all_checks_passed=True, fields=fields, fresh_input_repairs=repairs,
                low_degree_monomial_checks=sum(f['low_degree_monomial_checks'] for f in fields),
                failed_gatewise_extension_checks=sum(f['failed_high_degree_checks'] for f in fields),
                replacement_linear_extension_checks=sum(f['replacement_linear_extension_checks'] for f in fields),
                primary_source='https://arxiv.org/abs/2502.17779v1',
                known_theorem_scope='Multitape deterministic time to deterministic space; '
                                   'not a simultaneous time guarantee or NP lower bound.',
                decision='Reject the automatic gatewise arithmetic replacement at the old degree budget. '
                         'No general efficient low-degree extension construction is obtained. '
                         'Do not treat the known space theorem as a P!=NP proof route by itself.',
                all_size_argument='For q=2^r and P=x^(q-1), P agrees with identity on Boolean inputs, '
                                  'but the orbit sum at x=1,v=0 equals 1 instead of P(0)=0.',
                scope='Exact finite checks and an elementary all-size countercheck of a proposed repair. '
                      'The same function has an easy linear extension. No new complexity lower bound '
                      'or Lean formalization is claimed.',
                new_general_time_lower_bound=False, np_membership_bridge_proved=False,
                p_vs_np_resolved=False)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out-dir',type=Path)
    args=parser.parse_args()
    text=json.dumps(audit(),sort_keys=True,indent=2)+'\n'
    if args.out_dir:
        args.out_dir.mkdir(parents=True,exist_ok=True)
        (args.out_dir/'catalytic_extension_degree.json').write_text(text,encoding='utf-8')
    else:
        print(text,end='')


if __name__=='__main__':
    main()
