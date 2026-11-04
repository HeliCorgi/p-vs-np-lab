#!/usr/bin/env python3
"""Reproduce symbolic hole-flat and no-merge controls without expanding large flats."""
import argparse
import json
from functools import reduce
from itertools import combinations, product
from operator import xor
from pathlib import Path

from pnp_lab.hole_flats import decide_hole_flats
from pnp_lab.ternary_support import three_cnf_to_weight_two_supports


def require(condition, label):
    if not condition:
        raise AssertionError(label)


def thin(answer):
    return {k:v for k,v in answer.items() if k!='witness'}


def source_models(n, f):
    return [v for v in range(1<<n) if all(any(bool(v & (1<<(abs(x)-1)))==(x>0) for x in cl) for cl in f)]


def run_experiment():
    fano=[(0,1,2),(0,1,4),(0,1,6)]
    diffs={a^b for g in fano for a,b in combinations(g,2)}
    require(diffs==set(range(1,8)),'Fano difference restriction')
    small=[]
    for rhs in range(8):
        ans=decide_hole_flats(fano,rhs)
        valid=[p for p in product(*fano) if reduce(xor,p,0)==rhs]
        require(ans['status']=='SAT' and tuple(ans['witness']) in valid,'Fano witness')
        small.append(dict(rhs=rhs,witness=ans['witness'],full_merges=ans['full_merges']))
    chains=[]
    for m in (2,8,32,128,256):
        gs=[(0,1,1<<j) for j in range(1,m+1)]
        hole=(1<<(m+1))-1
        bad=decide_hole_flats(gs,hole)
        ok=decide_hole_flats(gs,hole^1)
        filled=decide_hole_flats(gs+[(0,1,6)],hole)
        require(bad['status']=='UNSAT' and bad['reason']=='forced_hole','Unique missing target')
        require(ok['status']=='SAT' and ok['witness']==[1<<j for j in range(1,m+1)],'High-rank witness')
        require(filled['status']=='SAT' and filled['full_merges']==1 and
                reduce(xor,filled['witness'],0)==hole,'Final hole filled')
        chains.append(dict(m=m,rank=m+1,represented_cardinality=str(hole),
                           before_filling=thin(bad),filled_non_graphic=thin(filled)))
    # A raw Fano minor on each of these actual sparse images has a separate
    # certificate; here we measure how often symbolic merging actually decides.
    f=[(1,2,3),(1,2,4),(1,3,4)]
    statuses={'SAT':0,'UNKNOWN':0}
    merge_counts=[]
    for s in product((-1,1),repeat=9):
        fs=[tuple(x*s[3*i+j] for j,x in enumerate(cl)) for i,cl in enumerate(f)]
        models=source_models(4,fs)
        require(bool(models),'Independent oracle')
        red=three_cnf_to_weight_two_supports(('x','a','b','c'),fs)
        ans=decide_hole_flats(red.supports,red.rhs)
        require(ans['status'] in statuses,'False UNSAT')
        statuses[ans['status']]+=1; merge_counts.append(ans['merges'])
        if ans['status']=='SAT':
            require(red.project_witness(ans['witness']) in models,'Source witness')
    cube=[tuple((j+1)*s for j,s in enumerate(ss)) for ss in product((-1,1),repeat=3)]
    stalls=[]
    # Repeat the shape only on disjoint sites to check formulae for counters.
    # Hardness of the no-merge subclass uses the separate all-input proof.
    for copies in (1,2,5):
        formula=[tuple((abs(x)+3*i)*(1 if x>0 else -1) for x in cl)
                 for i in range(copies) for cl in cube]
        red=three_cnf_to_weight_two_supports([f'x{i}' for i in range(3*copies)],formula)
        ans=decide_hole_flats(red.supports,red.rhs)
        require(not source_models(3,cube),'Cube independent UNSAT oracle')
        require(ans['status']=='UNKNOWN' and ans['merges']==0 and
                ans['decomposition_nullity']==19*copies,'No-merge cube')
        stalls.append(dict(copies=copies,**thin(ans)))
    diagonal=[(0,1,2),(0,4,8),(0,5,10)]
    fixes=0
    for rhs in range(16):
        plain=decide_hole_flats(diagonal,rhs)
        with_cover=decide_hole_flats(diagonal,rhs,cover=True)
        require(with_cover['status']=='SAT' and reduce(xor,with_cover['witness'],0)==rhs,'Cover lift')
        if plain['status']=='UNKNOWN':
            ev=with_cover['cover_evidence']
            require(ev['exclusion_sum']==3 and ev['total_decompositions']==4,'Diagonal counts')
            fixes+=1
    require(fixes==7,'Baseline diagonal corrections')
    cube_red=three_cnf_to_weight_two_supports(('x','y','z'),cube)
    cube_cover=decide_hole_flats(cube_red.supports,cube_red.rhs,cover=True)
    ev=cube_cover['cover_evidence']
    require(cube_cover['status']=='UNKNOWN' and ev['bad_counts']==[1<<17]*32
            and ev['exclusion_sum']==8*(1<<19),'Strict cover should fail on cube')
    optional=dict(diagonal_targets=16,additional_sat_witnesses=fixes,
                  diagonal_exclusions=3,diagonal_decompositions=4,
                  cube_status=cube_cover['status'],cube_exclusions=ev['exclusion_sum'],
                  cube_decompositions=ev['total_decompositions'])
    return {'schema_version':1,'all_checks_passed':True,'rank_three_fano':small,'high_rank_chains':chains,
            'actual_bridge_signings':dict(statuses=statuses,source_assignments_examined=512*16,
                                         min_merges=min(merge_counts),max_merges=max(merge_counts)),
            'optional_cover':optional,'no_merge_cube':stalls,'scope':'Polynomial partial decision. UNKNOWN has no implication for satisfiability. Chain cardinalities follow from the all-size identity; large represented sets were never listed.',
            'summary':dict(fano_targets_decided=8,largest_symbolic_rank=257,
                           largest_exact_one_hole_size=str((1<<257)-1),
                           bridge_signings_sat=statuses['SAT'],bridge_signings_unknown=statuses['UNKNOWN'],
                           no_merge_unsat_controls=len(stalls))}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--out-dir',type=Path,required=True)
    out=p.parse_args().out_dir;out.mkdir(parents=True,exist_ok=True)
    r=run_experiment();(out/'hole_flats.json').write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
    print(json.dumps(r['summary'],sort_keys=True))


if __name__=='__main__':
    main()
