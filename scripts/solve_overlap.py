#!/usr/bin/env python3
"""Solve explicit 3-CNF via affine forbidden sets. Exit 0=decided, 2=UNKNOWN, 1=input error."""
import argparse
import json
from pathlib import Path
import sys

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'src'))
from pnp_lab.selector_events import compile_selector_events,compile_compact_events,compile_parsimonious_events
from pnp_lab.event_projection import project_affine_events
from pnp_lab.overlap_lattice import solve_affine_arrangement
from pnp_lab.overlap_refutation import refute_affine_cover


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('input',help='JSON arrays variables and signed clauses; - for stdin')
    p.add_argument('--encoding',choices=('strict','odd','compact','parsimonious'),default='compact')
    p.add_argument('--method',choices=('project','count','refute','observations'),default='project')
    p.add_argument('--order',choices=('aux-first','greedy'),help='Projection order (default aux-first)')
    p.add_argument('--max-pairs',type=int,help='Projection pair budget; no limit by default')
    p.add_argument('--degree',type=int,help='Static refutation degree (default 3)')
    p.add_argument('--max-rows',type=int,help='Bound generated refutation rows')
    p.add_argument('--slice-source',action='store_true',help='Condition count on all original source bits')
    p.add_argument('--max-slices',type=int,help='Count slice budget (default 256)')
    p.add_argument('--max-intersections',type=int,help='Intersection-probe budget for count')
    p.add_argument('--max-subsets',type=int,help='Least-model seed budget for observations')
    a=p.parse_args()
    try:
        for method,options in (('project',(a.order,a.max_pairs)),('count',(a.max_slices,a.max_intersections)),
                               ('refute',(a.degree,a.max_rows)),('observations',(a.max_subsets,))):
            if a.method!=method and any(v is not None for v in options):raise ValueError('Option applies only to --method '+method)
        if a.slice_source and a.method!='count':raise ValueError('--slice-source requires --method count')
        obj=json.loads(sys.stdin.read() if a.input=='-' else Path(a.input).read_text())
        if (not isinstance(obj,dict) or not isinstance(obj.get('variables'),list) or
                not isinstance(obj.get('clauses'),list) or any(not isinstance(c,list) for c in obj['clauses'])):
            raise ValueError('Expected variables and clauses arrays.')
        names,cs=obj['variables'],obj['clauses']
        if a.encoding in ('strict','odd'):
            e=compile_selector_events(names,cs,strict=a.encoding=='strict')
        else:
            e=(compile_compact_events if a.encoding=='compact' else compile_parsimonious_events)(names,cs)
        n=e.n_parameters
        if a.method=='project':
            order=None if a.order=='greedy' else [*range(len(names),n),*range(len(names))]
            r=project_affine_events(n,e.events,order=order,max_pairs=a.max_pairs)
        elif a.method=='count':
            r=solve_affine_arrangement(n,e.events,condition_on=([1<<i for i in range(len(names))] if a.slice_source else ()),
                    max_slices=256 if a.max_slices is None else a.max_slices,max_intersections=a.max_intersections)
        elif a.method=='observations':
            from pnp_lab.observation_2sat import solve_observation_2sat
            r=solve_observation_2sat(n,e.events,max_subsets=a.max_subsets)
        else:
            r=refute_affine_cover(n,e.events,degree=3 if a.degree is None else a.degree,max_rows=a.max_rows)
        model=e.project_witness(r['witness']) if r['status']=='SAT' else None
        out=dict(status=r['status'],encoding=a.encoding,method=a.method,parameter_bits=n,event_count=len(e.events),
                 source_witness_mask=model,source_witness=(None if model is None else {v:bool(model & (1<<i)) for i,v in enumerate(names)}),result=r)
        if a.method=='count':
            out['count_scope']='distinct parameter assignments'
            if a.encoding=='parsimonious':out['source_model_count']=r['survivor_count']
    except (ValueError,OSError,TypeError) as exc:
        print('Input error:',exc,file=sys.stderr); return 1
    print(json.dumps(out,ensure_ascii=False,indent=2))
    return 2 if out['status']=='UNKNOWN' else 0


if __name__=='__main__':
    raise SystemExit(main())
