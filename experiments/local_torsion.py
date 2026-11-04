"""Determine the integer local group instead of guessing its prime power."""
import argparse,json
from itertools import combinations,product
from pathlib import Path
from pnp_lab.local_torsion import check_local_torsion,scan_local_torsion,torsion_characters
from pnp_lab.four_flow import four_prism_flow,state_permutations
from pnp_lab.ternary_flow import scramble


def relation(kind):
    good={'cyclic':lambda a,b,c:(a+b-c)%4==0,
          'klein':lambda a,b,c:a^b==c,
          'parity_only':lambda a,b,c:(a+b-c)%2==0}[kind]
    p=state_permutations(3,49811);cs=[]
    for j in range(3):
        x=tuple(range(5*j+1,5*j+6));cs.extend(((x[0],x[1],x[4]),(-x[4],x[2],x[3])))
        cs.extend((-v,-w) for v,w in combinations(x[:4],2))
    for word in product(range(4),repeat=3):
        if not good(*word):cs.append(tuple(-(5*j+1+p[j][w]) for j,w in enumerate(word)))
    return 15,tuple(cs)


def summarize(z,full=False):
    return dict(scopes=z['scanned_scopes'],profiles=z['histogram'],free_rank=z['examples'][0]['free_rank'],
                proof_operations=len(z['examples'][0]['certificate']['ops']),
                **({'example':z['examples'][0]} if full else {}))


def run():
    records=[]
    for k in (3,8):
        for bad in (False,True):
            n,cs,x=four_prism_flow(k,bad);raw,_=scramble(n,cs,x,432315+k)
            r=scan_local_torsion(n,raw)
            assert r['histogram']=={'[4]':2*k} and r['complete_for_scopes']
            example=r['examples'][0]
            assert check_local_torsion(n,raw,example['scope'],example['certificate'])
            records.append(dict(k=k,variables=n,clauses=len(raw),unbalanced=bad,**summarize(r)))
    controls=[]
    for kind,expect in [('cyclic',[4]),('klein',[2,2]),('parity_only',[2])]:
        n,cs=relation(kind);raw,_=scramble(n,cs,None,99)
        r=scan_local_torsion(n,raw);e=r['examples'][0]
        assert r['complete_for_scopes'] and r['histogram']=={str(expect):1} and e['free_rank']==6
        assert check_local_torsion(n,raw,e['scope'],e['certificate'])
        chars=torsion_characters(e['certificate']);assert [c['modulus'] for c in chars]==expect
        # Entire input is just one star. Verify these characters directly on
        # satisfying assignments independently of Smith operations or state names.
        words=[w for w in range(1<<n) if all(any(bool(w>>(abs(l)-1)&1)==(l>0) for l in c) for c in raw)]
        assert len(words)==(32 if kind=='parity_only' else 16)
        for row in chars:
            assert all(sum(a*((w>>(v-1))&1) for v,a in zip(e['scope'],row['coeff']))%row['modulus']==row['rhs'] for w in words)
        controls.append(dict(table=kind,models=len(words),example_characters=chars,**summarize(r,True)))
    return dict(schema_version=1,all_checks_passed=True,renamed_networks=records,raw_star_controls=controls,
                summary=dict(network_scopes=sum(x['scopes'] for x in records),largest_variables=records[-1]['variables'],
                             distinct_groups=['Z/4','Z/2 + Z/2','Z/2'],raw_star_assignments_checked=3*(1<<15)),
                scope='Integral affine characters of individual recovered star scopes; local torsion does not by itself refute global SAT.')


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--out-dir',type=Path,required=True)
    out=p.parse_args().out_dir;out.mkdir(exist_ok=True,parents=True)
    r=run();(out/'local_torsion.json').write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
    print(r['summary'])
