"""Checked one-case escape from the pair/layer obstruction."""
import argparse
import json
from pathlib import Path
import random
from itertools import product
from pnp_lab.case_parity import case_parity_refute,check_case_parity
from pnp_lab.expander_controls import cubic_control,gated_cubic_siblings,NAMES
from pnp_lab.simple_support import simple_support_image
from pnp_lab.blind_recovery import recover_blind,check_recovery,lift_recovered_model


def _holds(f,x):
    return all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in c) for c in f)


def _must(x):
    if not x:raise AssertionError('case parity comparison failed')


def disjoint_modules(k,odd=True):
    """k unconnected 111-variable modules with disjoint ports in both banks.

    Return a known word only on even charges, with selector zero and all
    edge values zero. A helper is not its own selector or an edge variable.
    """
    if type(k) is not int or k<1 or type(odd) is not bool:raise ValueError('invalid module arguments')
    n=0;f=[];model=0
    for module in range(k):
        s=n+1;n+=1
        l=n;n+=15;r=n;n+=15
        for side,v in enumerate((l,r)):
            _,banks=cubic_control(NAMES[side],odd)
            for c in banks:
                a,b,e=(v+x if x>0 else -(v-x) for x in c)
                n+=1;f.extend(((s if not side else -s,a,n),(-n,b,e)))
                if not side and a>0:model|=1<<(n-1)
    return n,tuple(f),None if odd else model


def _scramble(n,cs,word,seed):
    rng=random.Random(seed);p=list(range(1,n+1));rng.shuffle(p);p=[v if rng.randrange(2) else -v for v in p]
    f=[]
    for c in cs:
        d=[p[abs(l)-1]*(1 if l>0 else -1) for l in c];rng.shuffle(d);f.append(tuple(d))
    rng.shuffle(f)
    return f,None if word is None else sum(1<<(abs(l)-1) for i,l in enumerate(p) if bool(word>>i&1)==(l>0))


def run():
    modules=[];images=[]
    for k in (1,3,8):
        for odd in (True,False):
            n,cs,w=disjoint_modules(k,odd)
            rows,w=_scramble(n,cs,w,813+k)
            q=case_parity_refute(n,rows,max_pivots=1)
            _must(q['stats']['root_status']=='UNKNOWN' and q['stats']['pivots_tried']==1)
            _must(q['status']==('UNSAT' if odd else 'UNKNOWN'))
            if odd:
                _must(check_case_parity(n,rows,json.loads(json.dumps(q['certificate']))))
                ranks=[len(q['certificate'][f]['parity']['terms']) for f in ('zero','one')]
            else:
                _must(_holds(rows,w));ranks=[]
            modules.append(dict(k=k,odd=odd,variables=n,clauses=len(rows),status=q['status'],
                                checked_sat_word=not odd,child_xor_terms=ranks,stats=q['stats']))
    for odd in (True,False):
        n,orig,s,_,maps=gated_cubic_siblings(odd)
        q=case_parity_refute(n,orig,max_pivots=1)
        _must(q['status']==('UNSAT' if odd else 'UNKNOWN'))
        N,cs,oc=simple_support_image(n,orig)
        # Impose the edge-zero / selector-zero model in the even bank;
        # copy each original value, choose a gadget model + both free bits.
        x=None
        if not odd:
            model=sum(1<<i for i,l in enumerate(maps[0]) if type(l) is int and l<0)
            _must(_holds(orig,model))
            x=62|(3<<(N-2))
            for i,vs in enumerate(oc):
                if (model>>i)&1:
                    for v in vs:x|=1<<(v-1)
        real,x=_scramble(N,cs,x,139)
        z=recover_blind(N,real)
        _must(check_recovery(N,real,z) and z['status']=='OPEN')
        q2=case_parity_refute(z['n_reduced'],z['clauses'],max_pivots=1)
        _must(q2['status']==q['status'])
        if odd:_must(check_case_parity(z['n_reduced'],z['clauses'],q2['certificate']))
        else:
            _must(_holds(real,x))
            small=0;bits={}
            for i,lit in enumerate(z['images']):
                if type(lit) is bool:continue
                val=bool((x>>i)&1)==(lit>0)
                _must(bits.setdefault(abs(lit),val)==val)
            small=sum(1<<(v-1) for v,b in bits.items() if b)
            _must(_holds(real,lift_recovered_model(N,real,z,small)))
        images.append(dict(odd=odd,raw_variables=N,raw_clauses=len(real),reduced_variables=z['n_reduced'],
                           reduced_clauses=len(z['clauses']),result=q2['status'],checked_lift=not odd,stats=q2['stats']))
    # The eight sign patterns on three bits exclude every word. Replacing
    # each clause by this private chain preserves its existential meaning.
    n=3;negative=[]
    for signs in product((-1,1),repeat=3):
        a,b,c=(i*z for i,z in enumerate(signs,1))
        negative.extend(((a,n+1),(-n-1,n+2),(-n-2,b,c)));n+=2
    missed=case_parity_refute(n,negative)
    _must(missed['status']=='UNKNOWN' and missed['stats']['pivots_tried']==19 and not missed['stats']['limit_reached'])
    return dict(schema_version=1,all_checks_passed=True,modules=modules,recovered_images=images,
                unsat_miss=dict(variables=n,clauses=len(negative),status=missed['status'],stats=missed['stats']),
                summary=dict(module_controls=len(modules),largest_modules=modules[-1]['k'],largest_variables=modules[-1]['variables'],
                             largest_clauses=modules[-1]['clauses'],mask_image_variables=images[0]['raw_variables'],
                             mask_image_clauses=images[0]['raw_clauses'],successful_odd_pivots=1,
                             successful_inner_calls=modules[-2]['stats']['inner_calls'],
                             all_pivots_in_unsat_miss=19),
                scope='Proofs from two complementary restrictions, not a shallow ordinary resolution refutation. No general polynomial SAT claim.')


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--out-dir',type=Path,required=True)
    d=p.parse_args().out_dir;d.mkdir(parents=True,exist_ok=True);r=run()
    (d/'case_parity.json').write_text(json.dumps(r,sort_keys=True,indent=2)+'\n');print(r['summary'])
