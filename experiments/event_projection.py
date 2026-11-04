"""Exact selector elimination, after which a union of affine flats can be large."""
import argparse
import json
from pathlib import Path
from itertools import product
from pnp_lab.ternary_support import three_cnf_to_weight_two_supports
from pnp_lab.support_solver import decide_xor_choices
from pnp_lab.event_projection import project_affine_events
from pnp_lab.selector_events import compile_selector_events,compile_compact_events,compile_parsimonious_events


def require(x,msg):
    if not x:raise AssertionError(msg)


def run():
    cube=[[(i+1)*y for i,y in enumerate(s)] for s in product((-1,1),repeat=3)]
    controls=[]
    for name,comp in [('strict',compile_selector_events),('compact',compile_compact_events),
                      ('parsimonious',compile_parsimonious_events)]:
        for count,cs in [(8,cube),(7,cube[:-1])]:
            e=comp(['a','b','c'],cs); order=[*range(3,e.n_parameters),0,1,2]
            r=project_affine_events(e.n_parameters,e.events,order=order)
            require(r['status']==('UNSAT' if count==8 else 'SAT'),'wrong source answer')
            if count==7:require(e.project_witness(r['witness'])==0,'wrong source witness')
            controls.append(dict(encoding=name,clauses=count,n=e.n_parameters,**r))
    legacy=[]
    for cs in (cube,cube[:-1]):
        red=three_cnf_to_weight_two_supports(('a','b','c'),cs)
        r=decide_xor_choices(red.supports,red.rhs,max_transitions=0)
        expected='UNSAT' if len(cs)==8 else 'SAT'
        require(r['status']==expected and r['backend']=='overlap_project','old solver did not dispatch')
        ov=r['residual']['overlap_result']; par=ov['parameter_result']
        sw=None if expected=='UNSAT' else red.project_witness(r['witness'])
        require(expected=='UNSAT' or sw==0,'old solver witness does not satisfy source')
        legacy.append(dict(clauses=len(cs),status=expected,backend=r['backend'],
                           old_cover=decide_xor_choices(red.supports,red.rhs,method='holes')['status'],
                           kernel_dimension=ov['fiber_dimension'],event_count=ov['event_count'],
                           pairs_tested=par['pairs_tested'],source_witness_mask=sw))
    cases=[]
    for k in (2,3,4,5,6,7,8):
        # Replace the forbidden hyperplane by two rank-two pieces on a1.
        # Eliminating all z bits leaves a product of k punctured planes.
        es=[[((1<<k)-1,0),(1<<k,s)] for s in (0,1)]
        es += [[(1<<i,1),(1<<(k+2*i+j),0)] for i in range(k) for j in range(2)]
        good=project_affine_events(3*k,es,order=[*range(k,3*k),*range(k)])
        bad=project_affine_events(3*k,es,order=range(3*k))
        mid=bad['layer_sizes'][k]
        require(good['status']==bad['status']=='SAT','nonempty image')
        require(mid*2**k>=3**k and mid==2**k,'barrier in specified implementation/order')
        cases.append(dict(k=k,groups=len(es),middle_flats=mid,lower_bound_ceiling=(3**k+2**k-1)//2**k,
                          selector_first_peak=bad['peak_events'],other_order_peak=good['peak_events'],
                          selector_first_pairs=bad['pairs_tested'],other_order_pairs=good['pairs_tested']))
    return dict(schema_version=1,all_checks_passed=True,cube_controls=controls,sparse_bridge_controls=legacy,ordered_barrier=cases,
                scope='Counts of projected flats are representation/order dependent; no general SAT lower bound.',
                summary=dict(largest_k=cases[-1]['k'],largest_observed_middle_flats=cases[-1]['middle_flats'],
                             compact_cube_pairs=next(c['pairs_tested'] for c in controls if c['encoding']=='compact' and c['clauses']==8),
                             sparse_probes_by_clause_count={str(r['clauses']):r['pairs_tested'] for r in legacy},source_controls=len(controls)))


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--out-dir',type=Path,required=True);out=p.parse_args().out_dir
    out.mkdir(parents=True,exist_ok=True);r=run()
    (out/'event_projection.json').write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
    print(r['summary'])
