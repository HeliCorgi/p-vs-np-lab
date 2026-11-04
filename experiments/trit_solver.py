"""Recognized trit relations: construct independent Boolean models or raw modular refutations."""
import argparse,json
from itertools import combinations
from pathlib import Path

from pnp_lab.trit_solver import check_trit_answer,solve_trit_affine
from pnp_lab.ternary_flow import prism_flow,scramble


def _coloring(vertices,edges):
    f=[]
    for i in range(vertices):
        c=tuple(3*i+t for t in (1,2,3));f.append(c);f.extend((-a,-b) for a,b in combinations(c,2))
    for u,v in edges:f.extend((-(3*u+t),-(3*v+t)) for t in (1,2,3))
    return 3*vertices,tuple(f)


def run():
    controls=[];nonaffine=[]
    for k in (3,8,32,128):
        for bad in (False,True):
            n,cs,_=prism_flow(k,bad=bad)
            # Deliberately pass no construction witness into either routine.
            rows,_=scramble(n,cs,None,238+k)
            out=solve_trit_affine(n,rows)
            if out['status']!=('UNSAT' if bad else 'SAT') or not check_trit_answer(n,rows,out):
                raise AssertionError('wrong answer or unverified result')
            controls.append(dict(k=k,unbalanced=bad,variables=n,clauses=len(rows),
                                 status=out['status'],stats=out['stats'],
                                 solver_witness=None if bad else hex(out['witness'])))
    # The non-affine graph inequality engenders exactly the standard graph
    # 3-colorability problem. A 4-clique vs its single-edge deletion distinguish
    # actual UNSAT/SAT, though the trit procedure must decline both.
    for clique in (True,False):
        edges=list(combinations(range(4),2))
        if not clique:edges.pop()
        n,cs=_coloring(4,edges)
        model_count=sum(all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in row) for row in cs) for x in range(1<<n))
        r=solve_trit_affine(n,cs)
        if (r['status'],model_count)!=('UNKNOWN',0 if clique else 6):raise AssertionError('negative control')
        nonaffine.append(dict(K4=clique,boolean_models=model_count,status=r['status'],reason=r['reason']))
    return dict(schema_version=1,all_checks_passed=True,prisms=controls,nonaffine_colorings=nonaffine,
                summary=dict(prism_cases=len(controls),largest_variables=controls[-1]['variables'],
                             largest_clauses=controls[-1]['clauses'],largest_trit_rank=controls[-1]['stats']['rank'],
                             solver_constructed_models=sum(r['status']=='SAT' for r in controls),
                             independently_replayed_unsat=sum(r['status']=='UNSAT' for r in controls)),
                scope='Complete on recognized disjoint signed one-hot blocks with affine local trit relations; not general SAT.')


if __name__=='__main__':
    a=argparse.ArgumentParser();a.add_argument('--out-dir',required=True,type=Path)
    d=a.parse_args().out_dir;d.mkdir(parents=True,exist_ok=True)
    r=run();(d/'trit_solver.json').write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
    print(r['summary'])
