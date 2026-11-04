#!/usr/bin/env python3
"""Reproduce the signed intersection solver's exact counts and limitations."""
import argparse
import json
from itertools import combinations, product
from pathlib import Path

from pnp_lab.overlap_lattice import solve_affine_arrangement
from pnp_lab.selector_events import compile_compact_events, compile_selector_events


def require(test, label):
    if not test:
        raise AssertionError(label)


def compact(r):
    return {k:r[k] for k in ('status','reason','survivor_count','witness','slices_total',
                              'slices_completed','component_count','max_components_per_slice',
                              'intersections_tested','witness_restrictions','peak_terms')}


def is_bad(x,event):
    return all((x&a).bit_count()%2==b for a,b in event)


def path_count(n):
    # Independent two-state DP: ending in zero requires a previous one.
    zero,one=0,1
    for _ in range(n):
        zero,one=one,zero+one
    return zero+one


def arrangement_pair(n,b):
    z=1<<n
    return [[(1<<i,0),(z,s)] for i in range(n) for s in (0,1)]+[[(z-1,b),(z,s)] for s in (0,1)]


def all_intersection_sizes(n,events,max_order):
    # Independent point table encoded as a bit set, only on these tiny instances.
    points=[sum(1<<x for x in range(1<<n) if is_bad(x,e)) for e in events]
    for k in range(1,max_order+1):
        for ix in combinations(range(len(events)),k):
            inside=(1<<(1<<n))-1
            for i in ix:inside &= points[i]
            yield k,ix,inside.bit_count()


def run_experiment():
    axes=[]
    for d in (3,8,16,32,64):
        events=[[(1<<j,0) for j in range(d) if j!=i] for i in range(d)]
        ans=solve_affine_arrangement(d,events)
        require((ans['survivor_count'],ans['peak_terms'],ans['intersections_tested'],ans['component_count'])
                ==((1<<d)-d-1,d+2,(d*d+3*d-4)//2,1),'Coordinate-axis formula')
        require(ans['witness'].bit_count()>=2,'Outside all axes')
        axes.append(dict(d=d,subset_count_by_formula=1<<d,**compact(ans)))
    paths=[]
    for n in (3,6,9,12,15,18):
        events=[[(1<<i,0),(1<<(i+1),0)] for i in range(n-1)]
        ans=solve_affine_arrangement(n,events)
        require(ans['survivor_count']==path_count(n) and ans['component_count']==1,'Path recurrence or connectivity')
        require(ans['peak_terms'] >= 1 << (n//3),'Induced matching lower bound')
        require(not any(is_bad(ans['witness'],e) for e in events),'Path witness')
        paths.append(dict(n=n,all_size_dictionary_lower_bound=1<<(n//3),**compact(ans)))
    events=[[(1<<i,0),(1<<(i+1),0)] for i in range(59)]
    cutoff=solve_affine_arrangement(60,events,max_intersections=96)
    require((cutoff['status'],cutoff['survivor_count'],cutoff['witness'],cutoff['intersections_tested'])
            ==('UNKNOWN',None,None,96),'Incomplete exact count cannot prove UNSAT')

    low_order=[];checked=0
    for n in (2,3,4,5):
        ea,eb=(arrangement_pair(n,b) for b in (0,1))
        per_order=[0]*n
        a=all_intersection_sizes(n+1,ea,n);b=all_intersection_sizes(n+1,eb,n)
        for sa,sb in zip(a,b):
            require(sa==sb,'Different labelled low-order intersection cardinalities')
            per_order[sa[0]-1]+=1;checked+=1
        results=[solve_affine_arrangement(n+1,e) for e in (ea,eb)]
        counts=[r['survivor_count'] for r in results]
        require(counts==([0,2] if n%2==0 else [2,0]),'Parity circuit survivor discrepancy')
        for es,cnt in zip((ea,eb),counts):
            require(sum(not any(is_bad(x,e) for e in es) for x in range(1<<(n+1)))==cnt,
                    'Direct complement discrepancy')
        low_order.append(dict(n=n,dimension=n+1,events=len(ea),max_tested_order=n,
                              labelled_intersections_compared_per_order=per_order,
                              survivor_counts_by_last_constant=counts))

    # The fixed source separator is known from the constructor; we do not claim
    # a general automatic separator finder or charge only the surviving slice.
    cube=[tuple(sign[i]*(i+1) for i in range(3)) for sign in product((-1,1),repeat=3)]
    source_cases=[]
    for clauses in (cube,cube[1:]):
        models=[x for x in range(8) if all(any(bool(x&(1<<(abs(l)-1)))==(l>0) for l in c) for c in clauses)]
        for mode in ('strict','relaxed','compact'):
            enc=(compile_compact_events(('x','y','z'),clauses) if mode=='compact' else
                 compile_selector_events(('x','y','z'),clauses,strict=mode=='strict'))
            ans=solve_affine_arrangement(enc.n_parameters,enc.events,condition_on=(1,2,4))
            expected=0 if not models else {'strict':24,'relaxed':32,'compact':4}[mode]
            require(ans['survivor_count']==expected and ans['slices_completed']==8,'Cube slice count')
            if models:require(enc.project_witness(ans['witness']) in models,'Lifted source witness')
            source_cases.append(dict(source_clauses=len(clauses),source_models=len(models),mode=mode,
                                     parameter_dimension=enc.n_parameters,**compact(ans)))
    return dict(schema_version=1,all_checks_passed=True,
                scope='Exact counts of original parameter vectors, not necessarily source models. Axis subset counts and path lower bounds are mathematical formulas, not subset-enumeration timings. Source separator bits are supplied.',
                axes=axes,connected_paths=paths,path_budget=compact(cutoff),bounded_order_pairs=low_order,
                source_separator_cases=source_cases,
                summary=dict(axes_max_dimension=axes[-1]['d'],axes_max_dimension_count=axes[-1]['survivor_count'],
                             axes_max_dimension_terms=axes[-1]['peak_terms'],axes_max_dimension_intersections=axes[-1]['intersections_tested'],
                             path_max_vertices=paths[-1]['n'],path_max_terms=paths[-1]['peak_terms'],path_max_intersections=paths[-1]['intersections_tested'],
                             bounded_order_pairs=len(low_order),labelled_low_order_intersections=checked,
                             cube_slices=source_cases[0]['slices_completed'],cube_parameter_survivors=source_cases[0]['survivor_count'],
                             sat_sibling_counts_by_encoding={r['mode']:r['survivor_count'] for r in source_cases if r['source_models']}))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out-dir',type=Path,required=True)
    out=parser.parse_args().out_dir;out.mkdir(parents=True,exist_ok=True)
    result=run_experiment()
    (out/'overlap_lattice.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result['summary'],sort_keys=True))


if __name__=='__main__':main()
