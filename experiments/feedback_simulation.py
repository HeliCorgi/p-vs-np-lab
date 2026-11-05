"""Coefficient-level checks for the characteristic-zero / first-digit PC simulation.

Input lines are already-proved clauses; this checks the arithmetic suffix.
The prefix simulation and uniform transfer theorem are mathematical arguments.
"""
import argparse
import json
from pathlib import Path

from pnp_lab.feedback_fixture import feedback_case
from pnp_lab.global_lattice_fixtures import carry_cycle
from pnp_lab.integer_feedback import integer_feedback_refute, replay_feedback_lemmas
from pnp_lab.integer_hull import KIND, check_integer_hull, integer_hull_refute


def add(target, key, val, p):
    val += target.get(key, 0)
    if p:
        val %= p
    if val:
        target[key] = val
    else:
        target.pop(key, None)


def factor(poly, j, bit, p):
    # Fresh variable: strict multiplication by x or 1-x, no reduction.
    result = {} if bit else dict(poly)
    for mask, a in poly.items():
        assert not (mask & (1 << j))
        add(result, mask | (1 << j), a if bit else -a, p)
    return result


def audit(n, cs, cert, p):
    # 0 denotes characteristic zero; all displayed coefficients are integral.
    assert p in (0, 2, 3, 5, 7) and check_integer_hull(n, cs, cert)
    m = cert['modulus']
    assert m == 0 if not p else m > 0 and m % p == 0
    if p and cert['residual_rhs'] % p == 0:
        return dict(field=p, linear_projection=False, reason='contradiction vanishes in this field')
    total = {}
    cells = leaves = 0
    widest = 0
    for term in cert['terms']:
        weight = term['weight']
        vs = term['scope']
        pos = {v:j for j,v in enumerate(vs)}
        assert len(vs) <= 3
        poly = {}
        for w in range(1 << len(vs)):
            cells += 1
            val = weight * (sum(a for j,a in enumerate(term['coeff']) if w >> j & 1) - term['rhs'])
            if p:
                val %= p
            if not val:
                continue
            ix = next(ix for ix in term['clauses'] if not any(
                bool(w >> pos[abs(l)] & 1) == (l > 0) for l in cs[ix]))
            # Reconstruct the actual falsity polynomial of the selected premise,
            # then extend it with fresh literal factors to this complete word.
            bits = {pos[abs(l)]:int(l<0) for l in cs[ix]}
            delta = {0:1}
            for j, bit in bits.items():
                delta = factor(delta, j, bit, p)
            for j in range(len(vs)):
                if j not in bits:
                    delta = factor(delta,j,(w>>j)&1,p)
            for mask, coeff in delta.items():
                add(poly,mask,val*coeff,p)
                widest = max(widest,mask.bit_count())
            leaves += 1
        expected = {}
        add(expected,0,-weight*term['rhs'],p)
        for j,a in enumerate(term['coeff']):
            add(expected,1<<j,weight*a,p)
        assert expected == poly
        for mask, coeff in poly.items():
            key=tuple(v for j,v in enumerate(vs) if mask >> j & 1)
            add(total,key,coeff,p)
    assert set(total) == {()} and total[()] != 0
    return dict(field=p or 'Q', linear_projection=True, nonzero_constant=total[()],
                truth_cells=cells, minterm_products=leaves, largest_minterm_degree=widest)


def run():
    n, raw, _, _ = feedback_case(4,True)
    proof = integer_feedback_refute(n, raw)['certificate']
    cs = replay_feedback_lemmas(n,raw,proof['lemmas'])
    z = proof['integer']
    # Same valid sum lifted to modulus 6 by multiplying the weights by 3.
    squarefree = dict(kind=KIND,modulus=6,residual_rhs=3,
                      terms=[dict(t,weight=3*t['weight']) for t in z['terms']])
    cases = [dict(label='mod_two', **audit(n,cs,z,2)),
             dict(label='squarefree_six', **audit(n,cs,squarefree,2)),
             dict(label='unusable_prime_of_six', **audit(n,cs,squarefree,3))]
    for m,q,p in ((3,1,3),(4,2,2)):
        k, rows, _, _ = carry_cycle(m,q,wire_length=1)
        a = integer_hull_refute(k, rows, scopes={tuple(sorted(map(abs,c))) for c in rows})
        assert a['status']=='UNSAT' and a['certificate']['modulus']==m
        cases.append(dict(label='carry_mod_'+str(m), **audit(k,rows,a['certificate'],p)))
    exact = dict(kind=KIND,modulus=0,residual_rhs=1,terms=[
        dict(scope=[1],coeff=[1],rhs=1,modulus=0,clauses=[0],weight=1),
        dict(scope=[1],coeff=[1],rhs=0,modulus=0,clauses=[1],weight=-1)])
    cases.append(dict(label='exact', **audit(1,[(1,),(-1,)],exact,0)))
    assert sum(c['linear_projection'] for c in cases)==4
    return dict(all_checks_passed=True,cases=cases,
                summary=dict(cases=len(cases),checked_linear_suffixes=4,
                             invisible_linear_projections=2),
                scope='Exact finite polynomial coefficient checks of arithmetic suffixes. An invisible first digit rejects only this particular reduction to a prime field.')


if __name__ == '__main__':
    cli = argparse.ArgumentParser()
    cli.add_argument('--out-dir',type=Path,required=True)
    out = cli.parse_args().out_dir
    out.mkdir(parents=True,exist_ok=True)
    r = run()
    (out/'feedback_simulation.json').write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
    print(r['summary'])
