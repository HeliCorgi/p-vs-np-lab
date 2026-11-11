"""Independent signed-set checker, prime-clause oracle, and bounded semantic controls.

Run after the generator: python asymmetric_demorgan_audit.py --output ...
This module does NOT use the certificate generator's resolution implementation.
"""
from __future__ import annotations

import argparse
from collections import Counter
from copy import deepcopy
from itertools import product
import json
from pathlib import Path

from asymmetric_demorgan_miter import certificate, examples, summarize


def prime_gate_clauses(inputs, output, op):
    """Build source CNF independently from all valid local truth-table rows."""
    wires = (*inputs, output)
    size = len(wires)
    valid = []
    for bits in product((0, 1), repeat=len(inputs)):
        if op == 'NOT':
            out = 1 - bits[0]
        elif op == 'AND':
            out = int(all(bits))
        elif op == 'OR':
            out = int(any(bits))
        else:
            raise AssertionError('unknown operation')
        valid.append((*bits, out))
    implied = set()
    for signs in product((-1, 0, 1), repeat=size):
        clause = frozenset(w * s for w, s in zip(wires, signs) if s)
        if not clause:
            continue
        if all(any((v == 1) if lit > 0 else (v == 0)
                   for lit, v in zip((w*s for w,s in zip(wires, signs) if s),
                                     (b for b,s in zip(bits, signs) if s))) for bits in valid):
            implied.add(clause)
    return {clause for clause in implied
            if not any(other < clause for other in implied)}


def expected_source(n, gates):
    g = len(gates)
    expected = []
    def last_wire(w):
        return w if w <= n else n + g + 4 * (w-n-1) + 4
    for i, (op, a, b) in enumerate(gates):
        p = n+i+1
        s = n+g+4*i+1
        t, r, q = s+1, s+2, s+3
        expected.extend(prime_gate_clauses((a,b), p, op))
        expected.extend(prime_gate_clauses((last_wire(a),), s, 'NOT'))
        expected.extend(prime_gate_clauses((last_wire(b),), t, 'NOT'))
        expected.extend(prime_gate_clauses((s,t), r, 'OR' if op=='AND' else 'AND'))
        expected.extend(prime_gate_clauses((r,), q, 'NOT'))
    expected += [frozenset((n+g,)), frozenset((-(n+5*g),))]
    return Counter(expected)


def check_preconditions(n, gates):
    assert n >= 2 and len(gates) >= 1
    for i, gate in enumerate(gates):
        op, a, b = gate
        assert op in ('AND', 'OR') and 1 <= a <= n+i and 1 <= b <= n+i and a != b


def independent_replay(proof):
    """Do not call generator helpers. Reject wrong source and every bad resolution."""
    n, gates, total = proof['n'], [tuple(x) for x in proof['gates']], proof['variables']
    check_preconditions(n, gates)
    g = len(gates)
    assert total == n + 5*g
    assert len(proof['axioms']) == 12*g+2
    given = [frozenset(row) for row in proof['axioms']]
    assert Counter(given) == expected_source(n, gates), 'wrong input axioms'
    assert all(len(c) > 0 and all(0 < abs(lit) <= total and -lit not in c for lit in c)
               for c in given)
    clauses = list(given)
    maximum_width = max(map(len, given))
    for step in proof['steps']:
        left, right, pivot = step['left'], step['right'], step['pivot']
        assert 0 <= left < len(clauses) and 0 <= right < len(clauses)
        assert pivot in clauses[left] and -pivot in clauses[right]
        actual = (clauses[left] - {pivot}) | (clauses[right] - {-pivot})
        assert actual == frozenset(step['clause'])
        assert all(-lit not in actual for lit in actual)
        maximum_width = max(maximum_width, len(actual))
        assert maximum_width <= 3
        clauses.append(actual)
    assert not clauses[-1], 'not a refutation'
    n_and = sum(op == 'AND' for op, _, _ in gates)
    assert len(proof['steps']) <= 15*n_and + 14*(g-n_and)+2
    return len(proof['steps']), maximum_width


def eval_clause(clause, values):
    return any((values[abs(x)] if x > 0 else not values[abs(x)]) for x in clause)


def unique_gate_extension(n, gates, word):
    g=len(gates)
    bits={i+1: bool(word>>i & 1) for i in range(n)}
    for i,(op,a,b) in enumerate(gates):
        p=n+i+1
        bits[p]=bits[a] and bits[b] if op=='AND' else bits[a] or bits[b]
    def transformed(w):
        return w if w<=n else n+g+4*(w-n-1)+4
    for i,(op,a,b) in enumerate(gates):
        s=n+g+4*i+1
        u=bits[transformed(a)]
        v=bits[transformed(b)]
        bits[s]=not u
        bits[s+1]=not v
        bits[s+2]=(bits[s] or bits[s+1]) if op=='AND' else (bits[s] and bits[s+1])
        bits[s+3]=not bits[s+2]
    return bits


def semantic_control(proof):
    n, gates = proof['n'], [tuple(x) for x in proof['gates']]
    total = proof['variables']
    raw = 0
    inputs = 0
    if n<=4:
        for word in range(1<<n):
            bits=unique_gate_extension(n,gates,word)
            assert bits[n+len(gates)] == bits[total]
            assert all(eval_clause(c,bits) for c in proof['axioms'][:-2])
            # Both outputs constrained to their *actual common value*.
            output=bits[total]
            assert (bits[n+len(gates)]==output and bits[total]==output)
            # Both opposite units cannot simultaneously hold.
            assert not all(eval_clause(c,bits) for c in proof['axioms'])
            inputs+=1
    if total<=10:
        for assignment in range(1<<total):
            bits={i:bool(assignment>>(i-1)&1) for i in range(1,total+1)}
            assert not all(eval_clause(c,bits) for c in proof['axioms'])
            raw+=1
    return inputs, raw


def corruption_controls():
    original=certificate(3,[('AND',1,2),('OR',4,3)])
    changes=[]
    for mutation in ('pivot','parent','clause','axiom'):
        altered=deepcopy(original)
        if mutation=='pivot':
            altered['steps'][0]['pivot'] *= -1
        if mutation=='parent':
            altered['steps'][0]['left'] = 100000
        if mutation=='clause':
            altered['steps'][-1]['clause'] = [1]
        if mutation=='axiom':
            altered['axioms'][0] = [999]
        try:
            independent_replay(altered)
        except AssertionError:
            changes.append(mutation)
        else:
            raise AssertionError('accepted corruption: '+mutation)
    return changes


def audit():
    cases=examples()
    assert len(cases)==11 and max(len(g) for _,_,g in cases)<=10
    results=[]
    count_steps=0
    inputs=0
    raw=0
    for name,n,gates in cases:
        proof=certificate(n,gates)
        derived,width=independent_replay(proof)
        a,b=semantic_control(proof)
        assert derived==summarize(proof)['derived_lines']
        results.append({'name':name,'checked_derived_lines':derived,'width':width,
                        'input_assignments':a,'full_assignments':b})
        count_steps+=derived
        inputs+=a
        raw+=b
    negatives=corruption_controls()
    assert all(width['width']<=3 for width in results)
    assert all(summarize(certificate(n,gates))['derived_lines']<=15*sum(op=='AND' for op,*_ in gates)+14*sum(op=='OR' for op,*_ in gates)+2 for _,n,gates in cases)
    return {'date':'2026-11-11','status':'PASS','cases':results,
            'total_independently_replayed_derived_lines':count_steps,
            'primary_truth_assignments_checked':inputs,
            'full_miter_assignments_checked':raw,
            'corruptions_rejected':negatives,
            'new_lean_theorems':0,'p_vs_np_proved':False}


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    value=audit()
    content=json.dumps(value,sort_keys=True,indent=2,ensure_ascii=False)+'\n'
    if args.output:
        args.output.write_text(content,encoding='utf-8')
    else:
        print(content,end='')
