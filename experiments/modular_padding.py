"""Independent signed-scrambled controls for private-chain hiding and recovery."""
import argparse,json
from pathlib import Path

from pnp_lab.ternary_flow import prism_flow,scramble
from pnp_lab.modular_padding import (private_chain,plant_chain_model,shield_equalities,peel,lift_after_peeling,
                                     peeled_modular_refute,check_peeled_modular)
from pnp_lab.modular_hull import modular_hull_refute


def holds(cs,x):
    return all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in row) for row in cs)


def run():
    families=[];protected=[];t=10
    for k in (3,5,8):
        for bad in (False,True):
            n,base,x=prism_flow(k,bad)
            N,raw=private_chain(n,base,length=t)
            planted=None if bad else plant_chain_model(n,base,x,length=t)
            rows,word=scramble(N,raw,planted,1401+k)
            native=modular_hull_refute(N,rows,prime=3)
            assert native['status']=='UNKNOWN' and native['stats']['local_rows']==0
            q=peeled_modular_refute(N,rows,prime=3)
            assert q['status']==('UNSAT' if bad else 'UNKNOWN')
            if bad:assert check_peeled_modular(N,rows,q['certificate'])
            else:
                reduced,steps=peel(N,rows)
                unset=sum(1<<(v-1) for v,i,j in steps)
                assert holds(rows,word) and holds(reduced,word & ~unset)
                assert holds(rows,lift_after_peeling(N,rows,steps,word & ~unset))
            f=dict(k=k,unbalanced=bad,variables=N,clauses=len(rows),chain_length=t,
                   bare_rows=native['stats']['local_rows'],bare_status=native['status'],peeled_status=q['status'],
                   steps=q['stats']['steps'],residual_clauses=q['stats']['residual_clauses'],
                   residual_variables=q['stats']['residual_active_variables'],checked_sat_lift=not bad)
            assert f['steps']==t*len(base) and f['residual_variables']==n and f['residual_clauses']==len(base)
            families.append(f)
            if k!=3:continue
            M,extra,xx=shield_equalities(N,raw,planted)
            z,ww=scramble(M,extra,xx,14121+k)
            if ww is not None:assert holds(z,ww)
            inner=[]
            for p in (2,3):
                q=peeled_modular_refute(M,z,prime=p)
                assert q['status']=='UNKNOWN' and q['stats']['steps']==0 and q['stats']['modular']['global_rank']==2*N
                inner.append(dict(field=p,status=q['status'],learned_rank=2*N,peel_steps=0))
            protected.append(dict(k=k,unbalanced=bad,n=M,clauses=len(extra),learners=inner,checked_word=ww is not None))
    last=families[-1]
    return dict(schema_version=1,all_checks_passed=True,padded=families,guarded=protected,
                summary=dict(chain_controls=len(families),guarded_controls=len(protected),
                    largest_variables=last['variables'],largest_clauses=last['clauses'],largest_steps=last['steps'],
                    recovered_variables=last['residual_variables'],recovered_clauses=last['residual_clauses']),
                scope='Exponential search is not needed on the plain private chain; exact equality guards defeat this particular detector, not general SAT.')


if __name__=='__main__':
    a=argparse.ArgumentParser();a.add_argument('--out-dir',type=Path,required=True)
    d=a.parse_args().out_dir;d.mkdir(parents=True,exist_ok=True)
    r=run();(d/'modular_padding.json').write_text(json.dumps(r,sort_keys=True,indent=2)+'\n');print(r['summary'])
