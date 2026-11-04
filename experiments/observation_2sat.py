#!/usr/bin/env python3
"""A codimension-preserving 2-Sub-SAT reduction on explicit affine events."""
import argparse
from itertools import combinations, product
import json
from math import comb
from pathlib import Path
import random

from pnp_lab.observation_2sat import solve_observation_2sat


def require(ok,label):
    if not ok:raise AssertionError(label)


def clique_arrangement(sizes, edge):
    """Duplicate alternatives to >=5; preserve original colored-edge predicate.

    `edge(i,a,j,b)` is queried with i<j; a and b are ORIGINAL local vertex
    IDs. Every y bit is (form & t).parity XOR offset. The final bit per
    color enforces that color's odd parity; no additional equation input.
    """
    if any(type(s) is not int or s<=0 for s in sizes):
        raise ValueError('experiment requires nonempty color classes')
    q=0; vertices=[]
    for i,s in enumerate(sizes):
        b=max(s,5); weights=[1<<(q+j) for j in range(b-1)]
        for j,w in enumerate([*weights,sum(weights)]):
            vertices.append((i,j%s,w,int(j==b-1)))
        q+=b-1
    pairs=[]
    for (i,a,w,h),(j,b,v,g) in combinations(vertices,2):
        if i==j or not edge(i,a,j,b):
            pairs.append(((w,h^1),(v,g^1)))
    return q,vertices,tuple(pairs)


def picking_oracle(sizes,edge):
    return [t for t in product(*(range(s) for s in sizes))
            if all(edge(i,t[i],j,t[j]) for i,j in combinations(range(len(t)),2))]


def verify_picked(x,vs,sizes,edge):
    require(type(x) is int and x>=0,'Expected witness mask')
    picked=[[] for _ in sizes]
    for i,a,w,h in vs:
        if ((x&w).bit_count()&1)^h:picked[i].append(a)
    require(all(len(row)==1 for row in picked),'One per color')
    t=tuple(row[0] for row in picked)
    require(all(edge(i,t[i],j,t[j]) for i,j in combinations(range(len(t)),2)),'Cross-color clique')
    return t


def run_case(sizes,edge):
    n,vs,e=clique_arrangement(sizes,edge);sols=picking_oracle(sizes,edge)
    r=solve_observation_2sat(n,e)
    require(r['status']==('SAT' if sols else 'UNSAT'),'Colored clique oracle')
    require(r['deficiency']==len(sizes) and r['distinct_forms']==len(vs) and r['rank']==n,'Exact observation deficiency')
    selected=None if not sols else verify_picked(r['witness'],vs,sizes,edge)
    require(not sols or selected in sols,'Original clique')
    return {'original_color_sizes':sizes,'padded_vertices':len(vs),'free_bits':n,'bad_events':len(e),
            'original_cliques':len(sols),'selected_original_vertices':selected,
            **{k:r[k] for k in ('status','reason','distinct_forms','rank','deficiency','subsets_tested','unique_closures_tested')},
            'theoretical_subsets_including_empty':sum(comb(len(vs),i) for i in range(len(sizes)+1))}


def _chain(k):
    # All pairs in the last two colors are incompatible. Earlier colors
    # are linked by sparse additional nonedges to keep the constraint graph
    # connected; all alternatives except #0 still remain interchangeable.
    return lambda i,a,j,b: not ((i,j)==(k-2,k-1) or (j==i+1 and a==b==0))


def run_experiment():
    cases=[]
    for k in (2,3,4):
        c=run_case([5]*k,_chain(k));c['proved_distinct_closure_lower_bound']=3**(k-2)
        require(c['unique_closures_tested']>=c['proved_distinct_closure_lower_bound'],'Closure lower bound')
        require(c['subsets_tested']+1==c['theoretical_subsets_including_empty'],'All eligible subsets attempted')
        cases.append(c)
    # One clique on the original graph, many realized choices after cloning.
    planted=run_case([2,3,2],lambda i,a,j,b:a==i%([2,3,2][i]) and b==j%([2,3,2][j]))
    require(planted['original_cliques']==1,'Planted source clique')
    rng=random.Random(975134);nsat=nunsat=0;count=0
    for _ in range(20):
        k=rng.choice((2,3));s=[rng.randrange(1,4) for _ in range(k)]
        es={(i,a,j,b) for i,j in combinations(range(k),2) for a in range(s[i]) for b in range(s[j]) if rng.randrange(3)>0}
        rr=run_case(s,lambda i,a,j,b:(i,a,j,b) in es)
        nsat+=rr['status']=='SAT';nunsat+=rr['status']=='UNSAT';count+=1
    # Raw parameter oracle independently includes affine offsets on the last
    # alternatives, not just the clique interpretation.
    n,vertices,ev=clique_arrangement([2,2],lambda i,a,j,b:a+b==1)
    raw=[x for x in range(1<<n) if not any(all(((x&w).bit_count()&1)==p for w,p in e) for e in ev)]
    source=set(verify_picked(x,vertices,[2,2],lambda i,a,j,b:a+b==1) for x in raw)
    require(source=={(0,1),(1,0)},'Raw projected alternatives')
    n,_,ev=clique_arrangement([5,5,5],_chain(3));cap=solve_observation_2sat(n,ev,max_subsets=1)
    require(cap['status']=='UNKNOWN' and cap['witness'] is None,'Budget is not UNSAT')
    return {'schema_version':1,'all_checks_passed':True,'connected_unsat':cases,'planted_sat':planted,
            'raw_oracle':{'assignments':len(range(1<<8)),'survivors':len(raw),'original_selections':sorted(source)},
            'summary':{'colored_graph_cases':len(cases)+1+count,'seeded_sat':nsat,'seeded_unsat':nunsat,
                       'largest_observed_deficiency':cases[-1]['deficiency'],
                       'largest_connected_seed_tests':cases[-1]['subsets_tested'],
                       'budget_control':cap['status']},
            'scope':'Decision and original witnesses. The underlying 2-SUB-SAT upper/lower bounds are known. The parameter is measured on a presented arrangement, not the minimum over all logically equivalent CSP encodings.'}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--out-dir',type=Path,required=True)
    out=p.parse_args().out_dir;out.mkdir(parents=True,exist_ok=True)
    report=run_experiment();(out/'observation_2sat.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n')
    print(json.dumps(report['summary'],sort_keys=True))


if __name__=='__main__':main()
