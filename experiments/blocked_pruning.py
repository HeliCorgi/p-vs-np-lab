"""A repair of tagged XOR pruning, and an all-size obstruction to the repair."""
import argparse
import json
from pathlib import Path
from pnp_lab.decision_labels import canonical_cnf, blocked_normal_form, or_cnf, residual_label
from pnp_lab.decision_pruning import solve_pruned
from pnp_lab.label_controls import tagged_xor, prefix_restriction


def require(x,msg):
    if not x: raise AssertionError(msg)


def tagged_cycle(k):
    # A CNF residual which this label policy leaves opaque.
    return tuple((-(i+1),(i+1)%k+1) for i in range(k))


def shielded(k):
    if type(k) is not int or k<1:raise ValueError('expected k>=1')
    hub=k+1
    rows=[]
    for i in range(k):
        a,b=k+2+2*i,k+3+2*i
        rows.extend(((i+1,hub,a),(-(i+1),hub,b)))
    n=3*k+1
    for v in range(k+1,n+1):
        p,q=n+2*(v-k)-1,n+2*(v-k)
        rows.extend(((-v,p),(-p,q),(-q,v)))
    return 7*k+3,tuple(rows)


def contradictory_paths(h, p, q, r, s):
    return ((-h,p),(-p,q),(-q,-h),(h,r),(-r,s),(-s,h))


def witness(n,cs,w):
    return 0<=w<1<<n and all(any(bool(w & (1<<(abs(l)-1)))==(l>0) for l in c) for c in cs)


def run():
    repaired=[]
    for k in (3,4,6):
        n,cs=tagged_xor(k,tagged_cycle(k),marked=True)
        core=tuple(tuple((abs(l)+k)*(1 if l>0 else -1) for l in c) for c in tagged_cycle(k))
        expected=residual_label(n,core,mode='blocked')
        require(expected[0]=='CORE','core should remain undecided')
        levels=[]
        for d in range(k+1):
            rs=[prefix_restriction(cs,d,bits) for bits in range(1<<d)]
            new={residual_label(n,h,mode='blocked') for h in rs}
            old={residual_label(n,h,mode='affine') for h in rs}
            require(new=={expected} and len(old)==1<<d,'marked control')
            levels.append(dict(depth=d,old_keys=len(old),new_keys=len(new)))
        r=solve_pruned(n,cs,label_mode='blocked',max_width=1)
        require(r['status']=='SAT' and r['stats']['individual_merges']>=k,'raw search failed')
        repaired.append(dict(k=k,levels=levels,solver=r))

    core5=contradictory_paths(1,2,3,4,5)
    core_models=sum(witness(5,core5,w) for w in range(32))
    removed_models=[sum(witness(5,core5[:i]+core5[i+1:],w) for w in range(32))
                    for i in range(len(core5))]
    require(core_models==0 and all(removed_models),'contradictory core oracle')
    barriers=[]
    for k in (1,2,3,4):
        n,cs=shielded(k)
        require(len(cs)==8*k+3 and n==7*k+3 and witness(n,cs,(1<<n)-1),'input sanity')
        levels=[]
        # Verify the entire prefix and one complete anchor star per level;
        # the actual driver's scans below range over every anchor.
        for d in range(k+1):
            rs=[prefix_restriction(cs,d,bits) for bits in range(1<<d)]
            raw=[canonical_cnf(n,h) for h in rs]
            labs=[residual_label(n,h,mode='blocked') for h in rs]
            require(len(set(labs))==len(rs) and all(s[0]=='CORE' for s in labs),'residual label collision')
            require(all(blocked_normal_form(h)==h for h in raw),'unexpected blocked clause')
            pairs=[or_cnf(n,raw[0],h) for h in raw[1:]]
            keys=[residual_label(n,h,mode='blocked') for h in pairs]
            require(len(set(keys))==len(keys) and all(s[0]=='CORE' for s in keys),'anchor collision')
            require(all(blocked_normal_form(h)==h for h in pairs),'unexpected blocked OR clause')
            levels.append(dict(depth=d,residuals=len(rs),anchor_keys=len(set(keys))))
        r=solve_pruned(n,cs,label_mode='blocked',max_width=(1<<k)-1)
        require(r['status']=='UNKNOWN' and r['widths']==[1<<j for j in range(k+1)] and
                r['stats']['individual_merges']==0 and r['stats']['anchor_merges']==0,'actual width')
        # Six common binary clauses share h with the previous formula, but
        # neither truth value of h extends through both implication paths.
        core=contradictory_paths(k+1,n+1,n+2,n+3,n+4)
        ru=solve_pruned(n+4,cs+core,label_mode='blocked',max_width=(1<<k)-1)
        require(ru['status']=='UNKNOWN' and ru['widths']==r['widths'] and
                ru['stats']==r['stats'],'same-width UNSAT twin')
        barriers.append(dict(k=k,variables=n,clauses=len(cs),levels=levels,solver=r,
                             unsat_twin=dict(variables=n+4,clauses=len(cs)+6,solver=ru)))
    return dict(schema_version=1,all_checks_passed=True,repaired_markers=repaired,
                shielded_switches=barriers,unsat_core_oracle=dict(assignments=32,models=core_models,models_after_removing_each_clause=removed_models),
                summary=dict(largest_repaired_k=repaired[-1]['k'],largest_measured_shield_k=barriers[-1]['k'],
                             largest_measured_unpruned_width=barriers[-1]['solver']['peak_width'],
                             previous_marker_keys_at_last_k=64,blocked_marker_keys_at_last_k=1,unsat_twin_peak_width=barriers[-1]['unsat_twin']['solver']['peak_width']),
                scope='Exponential on the specified labels/order, not all SAT methods or orders. Larger sizes follow analytically.')


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--out-dir',required=True,type=Path)
    out=p.parse_args().out_dir;out.mkdir(exist_ok=True,parents=True)
    r=run();(out/'blocked_pruning.json').write_text(json.dumps(r,sort_keys=True,indent=2)+'\n');print(r['summary'])
