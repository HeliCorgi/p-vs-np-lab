"""RUP maps on the very same phase-12 raw and private-padded antichains."""
import argparse,json,random
from pathlib import Path
from pnp_lab.transport_obstruction import restrict,switch_tseitin,_complete,_scopes,_model
from pnp_lab.transport_resolution_padding import padded_tseitin
from pnp_lab.interface_transport import find_interface_transport
from pnp_lab.derived_transport import check_derived_transport,apply_derived_transport
from pnp_lab.decision_pruning import solve_pruned


def holds(rows,x):
    return all(any(bool((x>>(abs(l)-1))&1)==(l>0) for l in c) for c in rows)


def witnessed_move(k):
    n,base=switch_tseitin(k,odd=False)
    N,raw=padded_tseitin(k,odd=False); a,b=restrict(raw,k,0),restrict(raw,k,(1<<k)-1)
    r=find_interface_transport(N,a,b)
    assert r['status']=='FOUND' and check_derived_transport(N,a,b,r['certificate'])
    eq=[(sum(1<<(v-1) for v in vs),_complete(vs,cs))
        for vs,cs in _scopes(restrict(base,k,0)).items()]
    rng=random.Random(134141+k)
    for i in range(64):
        shift=rng.getrandbits(n)
        x=_model(n,[(mask,rhs^((shift&mask).bit_count()%2)) for mask,rhs in eq])^shift
        helper=n
        for cl in base:
            if any(abs(l)<=k for l in cl):continue
            if bool((x>>(abs(cl[-1])-1))&1)==(cl[-1]>0):x|=1<<helper
            helper+=1
        assert helper==N and holds(a,x)
        if holds(b,x):continue
        y=apply_derived_transport(N,r['certificate'],x)
        assert x!=y and holds(b,y)
        return dict(k=k,source_model_hex=hex(x),target_model_hex=hex(y),changed_bits=(x^y).bit_count())
    raise AssertionError('no informative even-charge witness')


def run():
    cases=[]; total=0
    for gen in (switch_tseitin,padded_tseitin):
        for k in (1,2,3,4,8,16):
            n,rows=gen(k)
            depths=range(1,k+1) if k<=3 else (k,)
            for d in depths:
                words=range(1<<d) if k<=3 else (0,(1<<d)-1)
                clauses={a:restrict(rows,d,a) for a in words}
                num=queries=nodes=0
                for a in words:
                    for b in words:
                        if a==b:continue
                        r=find_interface_transport(n,clauses[a],clauses[b])
                        assert r['status']=='FOUND' and check_derived_transport(n,clauses[a],clauses[b],r['certificate'])
                        assert r['stats']['split_trials']==0
                        num+=1;queries+=r['stats']['queries'];nodes+=r['stats']['nodes']
                total+=num;cases.append(dict(family=gen.__name__,k=k,depth=d,
                    all_pairs=(k<=3),verified_pairs=num,queries=queries,nodes=nodes))
    widths=[]
    for k in (2,4,8):
        n,cs=padded_tseitin(k)
        # Give exactly one directed comparison per requested tag split.
        re=solve_pruned(n,cs,derived_depth=0,label_mode='syntax',anchor_collisions=False,max_width=1,max_transport_checks=k)
        assert re['widths']==[1]*(k+1)+[2] and re['status']=='UNKNOWN'
        widths.append(dict(k=k,n=n,clauses=len(cs),widths=re['widths'],stats=re['stats']))
    return dict(all_checks_passed=True,schema_version=1,pairs=cases,driver=widths,
                actual_sat_moves=[witnessed_move(3),witnessed_move(8)],
                summary=dict(checked_ordered_pairs=total,max_pair_k=16,max_driver_k=8,tag_width=1),
                scope='Width-one prefix, not a full SAT decision. Prior direct systems excluded every direct map on the odd raw branches.')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--out-dir',type=Path,required=True)
    d=p.parse_args().out_dir;d.mkdir(exist_ok=True,parents=True)
    r=run();(d/'branch_interface.json').write_text(json.dumps(r,sort_keys=True,indent=2)+'\n');print(r['summary'])
