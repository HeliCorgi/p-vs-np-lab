"""Local cuts on two explicit cubic Tseitin instances and their 3-CNF siblings."""
import argparse
import json
from itertools import combinations,product
from pathlib import Path
from pnp_lab.expander_controls import NAMES,cubic_control,critical_assignment,finite_ceiling,gated_cubic_siblings,sibling_at
from pnp_lab.witness_transport import check_transport
from pnp_lab.derived_transport import derive_clause,check_clause,derive_transport,check_derived_transport


def _check(ok,s):
    if not ok:raise AssertionError(s)


def _holds(c,x):
    return any(bool(x>>(abs(l)-1)&1)==(l>0) for l in c)


def run():
    graphs=[]
    for name in NAMES:
        edges,cs=cubic_control(name);q=finite_ceiling(name)
        _check(q['isolated_vertex_supports']==10 and q['connected_supports']==566,'cut count')
        _check(q['width_at_most_three_raw']==q['falsifications_with_violated_isolated_star']==40
               and q['width_at_most_three_nonraw']==4051,'patterns')
        for j,c in enumerate(cs):
            word=critical_assignment(edges,c)
            _check([i for i,row in enumerate(cs) if not _holds(row,word)]==[j],'minimal source')
        _,ev=cubic_control(name,False)
        _check(all(_holds(c,0) for c in ev),'even control lacks zero model')
        keys={frozenset(c) for c in cs}
        passed=0
        for d in range(4):
            for vs in combinations(range(1,16),d):
                for signs in product((-1,1),repeat=d):
                    clause=tuple(a*b for a,b in zip(vs,signs))
                    r=derive_clause(15,cs,clause,depth=0)
                    _check((r['status']=='PROVED')==(frozenset(clause) in keys),'depth-zero disagreement')
                    if r['status']=='PROVED':
                        _check(check_clause(15,cs,clause,r['proof']),'bad proof')
                        passed+=1
        q['depth_zero_goals_checked']=4091;q['depth_zero_goals_proved']=passed;q['single_clause_critical_words']=40
        graphs.append(q)
    lifts=[]
    for odd in (True,False):
        n,f,s,src,maps=gated_cubic_siblings(odd)
        for t in range(2):
            residual=sibling_at(f,s,t)
            direct=dict(kind='signed-substitution-v1',images=list(maps[t]))
            _check(check_transport(n,src[t],residual,direct),'naked-to-sibling lift')
            implication=derive_transport(n,residual,src[t],images=list(range(1,n+1)),depth=0)
            _check(implication['status']=='FOUND' and check_derived_transport(n,residual,src[t],implication['certificate']),
                   'sibling-to-naked projection')
            lifts.append(dict(graph=NAMES[t],odd=odd,source_clauses=len(f),slice_clauses=len(residual),
                              retraction_on_active_axioms=len(src[t]),direct_lift=True,rup_reverse=True))
    observations=[]
    for a,b in [(0,1),(1,0)]:
        _,fa=cubic_control(NAMES[a]);_,fb=cubic_control(NAMES[b])
        q=derive_transport(15,fa,fb,depth=0)
        _check(q['status']=='UNKNOWN','unexpected cross control')
        observations.append(dict(source=NAMES[a],target=NAMES[b],status=q['status'],stats=q['stats']))
    return dict(schema_version=1,all_checks_passed=True,graphs=graphs,sibling_checks=lifts,
                cross_discovery=observations,
                summary=dict(graphs=2,vertices_per_graph=10,edges_per_graph=15,checked_small_clauses=8182,
                             raw_proved_at_depth_zero=80,critical_words=80,bilateral_sibling_controls=4),
                scope='Finite ten-vertex checks only; no asymptotic girth, expansion or exponential search cost inferred.')


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--out-dir',type=Path,required=True)
    d=p.parse_args().out_dir;d.mkdir(parents=True,exist_ok=True);r=run()
    (d/'rigid_ceiling.json').write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
    print(r['summary'])
