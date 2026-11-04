"""Discover charge conservation from the signed Boolean clauses; no timing extrapolation."""
import argparse
from itertools import product,combinations
import json
from pathlib import Path

from pnp_lab.expander_controls import cubic_control
from pnp_lab.modular_hull import modular_hull_refute,check_modular_hull
from pnp_lab.ternary_flow import onehot_flow,prism_flow,divergence,scramble


def holds(cs,x):
    return all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in row) for row in cs)


def _rank(rows,p):
    basis={}
    for row in rows:
        a=list(row)
        for j in sorted(basis):
            c=a[j]%p
            if c:a=[(u-c*v)%p for u,v in zip(a,basis[j])]
        pivot=next((j for j,c in enumerate(a) if c%p),None)
        if pivot is not None:
            inv=pow(a[pivot]%p,-1,p);basis[pivot]=[c*inv%p for c in a]
    return len(basis)


def local_dimensions():
    out=[]
    for p in (2,3):
        points=[(a,b,(-a+b+1)%p) for a,b in product(range(p),repeat=2)]
        if p==2:enc=points
        else:enc=[tuple(int(s==x) for s in triple for x in range(3)) for triple in points]
        for q in (2,3,5):
            rank=_rank([tuple((a-b)%q for a,b in zip(u,enc[0])) for u in enc[1:]],q)
            nullity=len(enc[0])-rank
            assert nullity==(3 if p==3 else 0)+int(p==q)
            out.append(dict(domain_modulus=p,coefficient_field=q,indicator_space=len(enc[0]),
                            affine_dimension=rank,number_of_independent_equations=nullity))
    return out


def run():
    records=[]
    for p in (2,3):
        for k in (3,8,32,128):
            for bad in (False,True):
                n,cs,word=prism_flow(k,bad,modulus=p)
                raw,w=scramble(n,cs,word,141014+k)
                if w is not None:assert holds(raw,w)
                inner=[]
                for q in (2,3):
                    r=modular_hull_refute(n,raw,prime=q)
                    refuted=bad and p==q
                    assert r['status']==('UNSAT' if refuted else 'UNKNOWN')
                    t=None
                    if refuted:
                        assert check_modular_hull(n,raw,json.loads(json.dumps(r['certificate'])))
                        t=len(r['certificate']['terms'])
                    inner.append(dict(prime=q,status=r['status'],terms=t,stats=r['stats']))
                records.append(dict(flow_prime=p,k=k,vertices=2*k,variables=n,clauses=len(raw),
                                    unbalanced=bad,checked_source_model=w is not None,
                                    witness_hex=(hex(w) if w is not None and k==3 else None),learners=inner))
    petersen_edges=cubic_control('petersen')[0]
    target=(1,0,0,0,0,0,0,0,0,0)
    n,cnf=onehot_flow(petersen_edges,target)
    raw,_=scramble(n,cnf,None,143819)
    sample=modular_hull_refute(n,raw,prime=3)
    assert sample['status']=='UNSAT' and check_modular_hull(n,raw,sample['certificate'])
    # A whole tiny binary encoding (not just each forbidden trit tuple).
    truth=0
    es=((0,1),(1,0),(0,1))
    for charge in product(range(3),repeat=2):
        n,f=onehot_flow(es,charge)
        got=sum(holds(f,x) for x in range(1<<n))
        assert got==(9 if sum(charge)%3==0 else 0)
        truth+=1<<n
    big=records[-1]
    return dict(schema_version=1,all_checks_passed=True,prism_controls=records,
                local_equations=local_dimensions(),petersen_control=dict(variables=45,clauses=len(raw),
                    status=sample['status'],terms=len(sample['certificate']['terms'])),
                scope='Refutes nonzero charge; balanced instances have independent witnesses, not SAT conclusions from failed search.',
                summary=dict(field_runs=2*len(records),largest_vertices=big['vertices'],largest_ternary_variables=big['variables'],
                    largest_ternary_clauses=big['clauses'],largest_ternary_proof_terms=big['learners'][1]['terms'],
                    raw_boolean_truth_assignments=truth))


if __name__=='__main__':
    a=argparse.ArgumentParser();a.add_argument('--out-dir',type=Path,required=True)
    d=a.parse_args().out_dir;d.mkdir(parents=True,exist_ok=True)
    r=run();(d/'ternary_flow.json').write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
    print(r['summary'])
