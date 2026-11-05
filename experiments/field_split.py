"""Raw two-field split traces and local root-coordinate translation checks."""
import argparse
from itertools import product
import json
from pathlib import Path

from pnp_lab.field_split import check_field_split,field_split_refute,switch_flow
from pnp_lab.modular_hull import modular_hull_refute
from pnp_lab.mixed_modular import mixed_modular_refute,check_field_bridge
from pnp_lab.ternary_flow import onehot_flow,prism_edges,scramble


def word_ok(rows,word):
    return all(any(bool(word>>(abs(l)-1)&1)==(l>0) for l in c) for c in rows)


def local_translation(p):
    """Test the actual local CNF on all root-tuples, for p=2 or 3.

    For mod 2 flows use F3; for mod 3 flows use F4=F2[a]/(a^2+a+1).
    This checks finite glyphs of the transfer, not the asymptotic lower bound.
    """
    if p==2:
        order=3
        sub=lambda x,y:(x-y)%3
        mul=lambda x,y:x*y%3
    elif p==3:
        order=4
        sub=lambda x,y:x^y
        def mul(x,y):
            v=(x if y&1 else 0)^((x<<1) if y&2 else 0)
            return v if v<4 else v^7
    else:
        raise ValueError('unexpected group')
    roots=[1]
    for _ in range(1,p):
        roots.append(mul(roots[-1],2))
    assert len(set(roots))==p and mul(roots[-1],2)==1
    inv={x:next(y for y in range(1,order) if mul(x,y)==1) for x in range(1,order)}
    def indicator(x,a):
        v=1
        for b in roots:
            if b!=a:
                v=mul(v,mul(sub(x,b),inv[sub(a,b)]))
        return v
    indicators=[[indicator(x,a) for a in roots] for x in roots]
    assert indicators==[[int(i==j) for j in range(p)] for i in range(p)]
    scopes=tuples=excluded=0
    for k in (2,3):
        for directions in product((1,-1),repeat=k):
            edges=tuple((0,i+1) if sign==1 else (i+1,0) for i,sign in enumerate(directions))
            for q in range(p):
                scopes+=1
                _,rows=onehot_flow(edges,(q,)+(0,)*k,p)
                def eid(l):
                    return (abs(l)-1)//(3 if p==3 else 1)
                star=[c for c in rows if len({eid(l) for l in c})==k]
                assert len(star)==p**k-p**(k-1)
                for ts in product(range(p),repeat=k):
                    iword=(sum(indicators[t][1]<<i for i,t in enumerate(ts)) if p==2 else
                           sum(indicators[t][j]<<(3*i+j) for i,t in enumerate(ts) for j in range(3)))
                    div=1
                    for d,t in zip(directions,ts):
                        z=roots[t]
                        div=mul(div,z if d==1 else inv[z])
                    valid=word_ok(star,iword)
                    assert valid==(div==roots[q])
                    excluded+=int(not valid)
                    tuples+=1
    return dict(group=p,coefficient_field='F3' if p==2 else 'F4',stars=scopes,
                root_tuples=tuples,violating_tuples=excluded)


def run():
    cases=[]
    sample=None
    for k in (3,6):
        for sat in (False,True):
            n,rows,word=switch_flow(prism_edges(k),2*k,satisfiable=sat)
            seed=18182+k
            cs,w=scramble(n,rows,word,seed)
            baseline=[modular_hull_refute(n,cs,prime=p)['status'] for p in (2,3)]
            assert baseline==['UNKNOWN','UNKNOWN']
            r=field_split_refute(n,cs)
            case=dict(prism_vertices=2*k,seed=seed,variables=n,clauses=len(cs),
                      before_split_fields_2_3=baseline,truth='SAT' if sat else 'UNSAT',status=r['status'],
                      stats=r['stats'])
            assert not r['stats']['budget_limited']
            if sat:
                assert r['status']=='UNKNOWN' and check_field_split(n,cs,r['certificate']) is False
                assert w is not None and word_ok(cs,w)
                case['raw_sat_word_hex']=hex(w)
            else:
                cert=r['certificate']
                assert r['status']=='UNSAT' and check_field_split(n,cs,cert)
                primes=[b['prime'] for b in cert['branches']]
                assert set(primes)=={2,3}
                case.update(branch_fields=primes,branch_terms=[len(b['terms']) for b in cert['branches']],
                            certificate_bytes=len(json.dumps(cert,sort_keys=True,separators=(',',':')).encode()))
                bridge=mixed_modular_refute(n,cs,bridge_width=1,max_probes=10000,max_short_rows=5000)
                assert bridge['status']=='UNSAT' and check_field_bridge(n,cs,bridge['certificate'])
                case['previous_width_one_bridge']=dict(status='UNSAT',checked=True,
                    transfers=bridge['stats']['transfer_widths'],probes=bridge['stats']['signature_probes'])
                if sample is None:
                    sample=dict(prism_vertices=2*k,seed=seed,certificate=cert)
            cases.append(case)
    audits=[local_translation(p) for p in (2,3)]
    return dict(schema_version=1,all_checks_passed=True,cases=cases,
                sample_regenerable_refutation=sample,local_translation=audits,
                summary=dict(inputs=len(cases),mixed_refutations=2,sat_siblings_checked=2,
                             previous_unary_bridge_refutations=sum('previous_width_one_bridge' in c for c in cases),
                             largest_variables=cases[-1]['variables'],largest_clauses=cases[-1]['clauses'],
                             local_star_patterns=sum(x['stars'] for x in audits),
                             local_root_tuples=sum(x['root_tuples'] for x in audits)),
                scope='Finite prisms and raw proof replays. The all-field PC bound is for uniformly expanding graphs, not a measured degree on these prisms. One split lies outside the single-sum model.')


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--out-dir',type=Path,required=True)
    out=parser.parse_args().out_dir
    out.mkdir(parents=True,exist_ok=True)
    r=run()
    (out/'field_split.json').write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
    print(r['summary'])
