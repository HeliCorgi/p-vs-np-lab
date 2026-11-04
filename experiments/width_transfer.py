"""Resolution-width transfer on actual siblings of a phase-12 blind image."""
import argparse
from itertools import combinations
import json
from pathlib import Path
from pnp_lab.width_transfer import cubic_tseitin,guarded,restrict,replay,pull,retract_proof,easy_refutation,closure_small


def run():
    examples=[]
    # The growing examples are connected cubic prism graphs, NOT a claim of
    # asymptotic expansion. The expander lower bounds are theorems, not timings.
    cases=[('K4',4,list(combinations(range(4),2)))]
    for k in (3,5,12):
        edges={(min(i,(i+1)%k)+t*k,max(i,(i+1)%k)+t*k) for t in (0,1) for i in range(k)}
        edges.update((i,i+k) for i in range(k))
        cases.append(('prism-'+str(k),2*k,sorted(edges)))
    for name,v,edges in cases:
        n,h=cubic_tseitin(v,edges);orig=set(map(frozenset,h))
        sat=guarded(n,h,contradict_on_true=False)
        assert all(any(bool(sat['model']>>(abs(l)-1)&1)==(l>0) for l in c) for c in sat['cnf'])
        r=guarded(n,h,contradict_on_true=True)
        a=restrict(r['cnf'],r['gate'],False);b=restrict(r['cnf'],r['gate'],True)
        assert {z for c in a if (z:=pull(c,r['images'])) is not None}==orig
        assert len({tuple(sorted(map(abs,c))) for c in r['cnf']})==len(r['cnf'])
        proof=easy_refutation(b);rows=replay(b,proof)
        assert rows[-1]==frozenset() and max(map(len,rows))<=6
        examples.append(dict(graph=name,vertices=v,source_variables=n,source_clauses=len(h),
                             image_variables=r['n'],image_clauses=len(r['cnf']),gate_copy=r['gate'],
                             easy_branch_proof_lines=len(proof),easy_branch_proof_width=max(map(len,rows)),
                             sat_variant_original_model_checked=True,all_hard_axiom_images_checked=True))
    _,h=cubic_tseitin(4,list(combinations(range(4),2)))
    lo=closure_small(h,3);hi=closure_small(h,4)
    assert not lo['contradiction'] and hi['contradiction'] and not replay(h,hi['proof'])[-1]
    little=((1,),(-1,));r=guarded(1,little,contradict_on_true=True);a=restrict(r['cnf'],r['gate'],False)
    before=easy_refutation(a);after=retract_proof(little,a,r['images'],before)
    assert not replay(little,after)[-1]
    return dict(schema_version=1,all_checks_passed=True,instances=examples,
                summary=dict(checked_graphs=len(examples),K4_exact_minimum_resolution_width=4,
                             width_three_K4_saturated_clauses=lo['known'],
                             max_easy_branch_width=max(c['easy_branch_proof_width'] for c in examples),
                             input_translation_lines=len(before),output_translation_lines=len(after)),
                scope='Finite proof checks, not measurements of asymptotic width. Infinite-family claims use the primary theorem.')


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--out-dir',type=Path,required=True)
    out=p.parse_args().out_dir;out.mkdir(parents=True,exist_ok=True)
    data=run();(out/'width_transfer.json').write_text(json.dumps(data,sort_keys=True,indent=2)+'\n')
    print(data['summary'])
