"""Automatic directed branch reductions, including a hardness test of diagonal flips."""
import argparse
import json
from pathlib import Path
import random
from itertools import product
from pnp_lab.transport_controls import coherent,directed_tags,cycle_core,flip_hard_siblings
from pnp_lab.witness_transport import KIND,check_transport,find_flip_transport
from pnp_lab.decision_pruning import solve_pruned
from pnp_lab.label_controls import prefix_restriction
try:
    from experiments.blocked_pruning import shielded,contradictory_paths
except ModuleNotFoundError:
    from blocked_pruning import shielded,contradictory_paths


def require(ok,msg):
    if not ok:raise AssertionError(msg)


def stats(r):
    return {s:r[s] for s in ('status','nodes','peak_width','widths','stats')}


def run():
    tags=[]
    for k in (4,6):
        n,f=directed_tags(k,cycle_core(k))
        hist={};checks=0
        for d in range(1,k+1):
            for prefix in range(1<<(d-1)):
                weak=prefix_restriction(f,d,prefix)
                strong=prefix_restriction(f,d,prefix+(1<<(d-1)))
                cert=find_flip_transport(n,strong,weak)
                require(cert is not None and check_transport(n,strong,weak,cert),'missing directed sibling map')
                m=cert['method'];hist[m]=hist.get(m,0)+1;checks+=1
        runs={}
        for mode in ('syntax','blocked'):
            for on in (False,True):
                r=solve_pruned(n,f,label_mode=mode,anchor_collisions=False,transport=on,
                               transport_strategies=('flip',) if on else None,max_width=1)
                expect=[1]*(k+1)+[2] if on else [1,2]
                require(r['status']=='UNKNOWN' and r['widths']==expect,'width-one cap boundary')
                if on:require(r['stats']['transport_drops']==k,'unexpected number of checked deletions')
                runs[mode+('-flip' if on else '-off')]=stats(r)
        completed=solve_pruned(n,f,label_mode='blocked',anchor_collisions=False,transport=True,
                               transport_strategies=('flip',),max_width=8)
        require(completed['status']=='SAT','structured source not solved at separate cap')
        tags.append(dict(k=k,variables=n,clauses=len(f),all_sibling_pairs_checked=checks,
                         method_counts=hist,cap_one_runs=runs,cap_eight_run=stats(completed)))

    k=4;n,f=shielded(k)
    twins={}
    for label,m,clauses in [('SAT',n,f),('UNSAT',n+4,f+contradictory_paths(k+1,n+1,n+2,n+3,n+4))]:
        old=solve_pruned(m,clauses,label_mode='blocked',max_width=15)
        new=solve_pruned(m,clauses,label_mode='blocked',max_width=15,transport=True)
        require(old['status']=='UNKNOWN' and old['widths']==[1,2,4,8,16],'wrong baseline')
        require(new['status']==label and new['stats']['transport_drops']>0,'new solver misplaced old twin')
        twins[label]=dict(variables=m,clauses=len(clauses),baseline=stats(old),transport=stats(new))

    cube=tuple(tuple((i+1)*s for i,s in enumerate(signs)) for signs in product((-1,1),repeat=3))
    formulas=[(),((),),((1,),(-1,)),((1,2),(-1,-2)),cube,cube[1:]]
    rng=random.Random(120014)
    for _ in range(36):
        formulas.append(tuple(tuple(rng.choice((-1,1))*rng.randrange(1,4) for _ in range(rng.randint(1,3)))
                              for _ in range(rng.randint(1,5))))
    nonzero=probes=0
    for formula in formulas:
        n=3; m,cs=flip_hard_siblings(n,formula)
        src,tar=[prefix_restriction(cs,1,b) for b in (1,0)]
        yes=any(coherent(w,formula) for w in range(1<<n))
        valid=0
        for w in range(0,1<<m,2):
            # Removed tag ignored. Every signed mask is checked on raw siblings.
            certificate=dict(kind=KIND,images=[(-1 if w>>i&1 else 1)*(i+1) for i in range(m)])
            require(coherent(w,src)==(w==0),'source uniqueness on non-tag coordinates')
            certified=check_transport(m,src,tar,certificate)
            require(certified==coherent(w,tar),'witness assignment/flip oracle mismatch')
            probes+=1;valid+=int(certified)
        nonzero+=int(valid>0)
        require((valid>0)==yes,'diagonal certificate existence does not match input SAT')

    return dict(schema_version=1,all_checks_passed=True,tags=tags,old_shielded_twins=twins,
                discovery_controls=dict(formulas=len(formulas),satisfiable=nonzero,flip_masks=probes,
                                        method='exhaustive for small controls only, not used by finder'),
                summary=dict(largest_k=tags[-1]['k'],tag_prefix_pairs=sum(z['all_sibling_pairs_checked'] for z in tags),
                             retained_tag_width=1,tag_cap_eight=tags[-1]['cap_eight_run']['status'],
                             old_shield_sat=twins['SAT']['transport']['status'],
                             old_shield_unsat=twins['UNSAT']['transport']['status'],
                             flip_discovery_controls=len(formulas),flip_masks_checked=probes),
                scope='The width bound stops after the tag prefix. Polynomial discovery is partial; arbitrary raw diagonal certificate existence is NP-complete.')


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--out-dir',type=Path,required=True);out=p.parse_args().out_dir
    r=run();out.mkdir(exist_ok=True,parents=True)
    (out/'witness_transport.json').write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
    print(r['summary'])
