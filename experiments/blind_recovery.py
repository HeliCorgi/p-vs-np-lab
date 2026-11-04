"""Expose the old blind image after hostile coordinate/sign/order relabelling."""
import argparse
import json
from pathlib import Path
import random

from pnp_lab.blind_recovery import recover_blind,check_recovery,lift_recovered_model
from pnp_lab.simple_support import simple_support_image,forcing_models
from pnp_lab.split_parity import split_parity_refute,check_split_parity
from pnp_lab.transport_obstruction import switch_tseitin


def _require(t,what):
    if not t:raise AssertionError(what)


def _holds(f,x):
    return all(any(bool((x>>(abs(l)-1))&1)==(l>0) for l in c) for c in f)


def scramble(n,cs,rng):
    p=list(range(1,n+1));rng.shuffle(p);p=[v if rng.randrange(2) else -v for v in p]
    out=[]
    for c in cs:
        row=[p[abs(l)-1]*(1 if l>0 else -1) for l in c]
        rng.shuffle(row);out.append(tuple(row))
    rng.shuffle(out)
    return out,p


def obscure_centers(n,cs):
    # Two fresh clauses sharing each original gadget coordinate. One pure
    # helper per clause may be set true to extend any preexisting model.
    out=list(cs)
    for v in range(1,7):
        for _ in range(2):
            out.append((v,n+1,n+2));n+=2
    return n,out


def project_model(word,result):
    vals={}
    for i,l in enumerate(result['images']):
        if type(l) is bool:continue
        bit=bool(word>>i&1)==(l>0)
        _require(abs(l) not in vals or bit==vals[abs(l)],'inconsistent projected word')
        vals[abs(l)]=bit
    return sum(1<<(i-1) for i,b in vals.items() if b)


def run():
    rng=random.Random(137196);assignments=0;lifts=0;cases=0
    for j in range(48):
        n=3+j%5
        src=[tuple(rng.choice((1,-1))*v for v in rng.sample(range(1,n+1),3))
             for _ in range(1+rng.randrange(20))]
        nbig,raw,oc=simple_support_image(n,src);rows,p=scramble(nbig,raw,rng)
        r=recover_blind(nbig,rows)
        _require(check_recovery(nbig,rows,r),'proper reduction not replayable')
        # Constructor correspondences are used ONLY by this comparison oracle.
        sub={}
        for i,vs in enumerate(oc,1):
            if not vs:continue
            signed=p[vs[0]-1]
            lit=r['images'][abs(signed)-1]
            _require(type(lit) is int,'used proper source coordinate unexpectedly fixed')
            sub[i]=lit*(1 if signed>0 else -1)
        _require(len(set(map(abs,sub.values())))==r['n_reduced']==len(sub),'not a signed coordinate bijection')
        expected={frozenset(sub[abs(l)]*(1 if l>0 else -1) for l in c) for c in src}
        _require(expected=={frozenset(c) for c in r['clauses']},'source not exactly recovered')
        rx=False
        for x in range(1<<n):
            z=sum(1<<(abs(l)-1) for i,l in sub.items() if bool(x>>(i-1)&1)==(l>0))
            _require(_holds(src,x)==_holds(r['clauses'],z),'assignment-level comparison')
            assignments+=1
            if not rx and _holds(src,x):
                _require(_holds(rows,lift_recovered_model(nbig,rows,r,z)),'wrong lifted word')
                rx=True;lifts+=1
        cases+=1
    controlled=[]
    for k in (1,4,32,128):
        for odd in (True,False):
            n,src=switch_tseitin(k,odd=odd)
            big,raw,_=simple_support_image(n,src)
            rows,p=scramble(big,raw,random.Random(400+k))
            b=split_parity_refute(big,rows)
            _require(b['status']=='UNKNOWN' and b['stats']['base_rows']==b['stats']['common_rows']==0,'prepass was not silent')
            r=recover_blind(big,rows)
            _require(r['status']=='OPEN' and check_recovery(big,rows,r),'invalid preprocessing')
            parity=split_parity_refute(r['n_reduced'],r['clauses'])
            outcome=parity['status']
            if odd:
                _require(outcome=='UNSAT' and check_split_parity(r['n_reduced'],r['clauses'],parity['certificate']),'no checked contradiction')
                witness=False
            else:
                _require(outcome=='UNKNOWN','false positive')
                # All-zero unpadded edge word extends to false copies, the
                # fixed six-bit gadget model and true filler bits.
                w=forcing_models()[0] | (3<<(big-2))
                scrambled=sum(1<<(abs(l)-1) for i,l in enumerate(p) if bool(w>>i&1)==(l>0))
                _require(_holds(rows,scrambled),'wrong independent raw witness')
                z=project_model(scrambled,r)
                witness=_holds(rows,lift_recovered_model(big,rows,r,z))
                _require(witness,'model did not lift')
            controlled.append(dict(k=k,odd=odd,raw_variables=big,raw_clauses=len(rows),raw_parity=b['status'],
                                   reduced_variables=r['n_reduced'],reduced_clauses=len(r['clauses']),
                                   reduced_parity=outcome,checked_lift=witness,stats=r['stats']))
    hidden=[]
    for k in (1,4,16):
        for odd in (True,False):
            n,src=switch_tseitin(k,odd=odd)
            big,raw,_=simple_support_image(n,src)
            m,raw=obscure_centers(big,raw)
            rows,p=scramble(m,raw,random.Random(500+k))
            r=recover_blind(m,rows)
            _require(check_recovery(m,rows,r) and r['n_reduced']==m and r['stats']['packs']==0 and r['stats']['signed_components']==0,'hidden centers')
            _require({frozenset(c) for c in rows}=={frozenset(c) for c in r['clauses']},'did not leave all clauses unchanged')
            hidden.append(dict(k=k,odd=odd,variables=m,clauses=len(rows)))
    return dict(schema_version=1,all_checks_passed=True,switch_controls=controlled,hidden_controls=hidden,
                summary=dict(proper_cases=cases,source_assignments=assignments,lifted_proper_cases=lifts,
                             hidden_controls=len(hidden),largest_checked_switches=128,
                             largest_raw_variables=controlled[-1]['raw_variables'],largest_raw_clauses=controlled[-1]['raw_clauses'],
                             largest_reduced_variables=controlled[-1]['reduced_variables'],largest_reduced_clauses=controlled[-1]['reduced_clauses']),
                scope='Sound normalization, exact inversion on proper 3-CNF images modulo signed names, used variables and duplicates; no polynomial general SAT claim.')


if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--out-dir',type=Path,required=True)
    d=p.parse_args().out_dir;d.mkdir(exist_ok=True,parents=True);r=run()
    (d/'blind_recovery.json').write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
    print(r['summary'])
