#!/usr/bin/env python3
"""Check arbitrary labelled binary matroids on real post-affine sparse bridge images."""
import argparse
from collections import Counter
import itertools
import json
from pathlib import Path
import random

from pnp_lab.minor_universality import build_binary_minor,verify_binary_minor
from pnp_lab.ternary_support import three_cnf_to_weight_two_supports


def run_experiment():
    seed=417031
    examples=[('empty',[]),('boundary_loops_parallel_coloop',[0,3,3,0,4]),
              ('F7',[1,2,4,3,5,6,7]),('dual_F7',[11,13,14,1,2,4,8]),
              ('long_relator',[1,2,4,8,16,32,64,127]),
              ('M_K5',[(1<<i)^(1<<j) for i,j in itertools.combinations(range(5),2)]),
              ('two_components',[1,2,3,4,8,12])]
    rng=random.Random(seed)
    for i in range(20):
        dim=rng.randint(1,6);n=rng.randint(1,12)
        examples.append((f'seeded_{i:02}',[rng.randrange(1<<dim) for _ in range(n)]))
    cases=[]
    for name,columns in examples:
        obj=build_binary_minor(columns)
        # Re-run the independent solver-domain bridge just from the source
        # formula (using the original public constructor, not synthetic masks).
        sparse=three_cnf_to_weight_two_supports(obj.variables,obj.clauses)
        check=verify_binary_minor(sparse.supports,columns,obj.certificate)
        freq=Counter(v for c in obj.clauses for v in c)
        if not (check['verified'] and check['presolve']['fixed_point'] and
                check['presolve']['contracted_rank']==3*len(obj.clauses) and
                all(len(c)==len(set(c))==3 and min(c)>0 for c in obj.clauses) and
                set(freq)==set(range(1,len(obj.variables)+1)) and all(x in (2,3) for x in freq.values())):
            raise AssertionError('invalid constructed source, presolve or minor')
        cases.append(dict(name=name,columns=columns,source_variables=len(obj.variables),
                          source_clauses=len(obj.clauses),sparse_groups=len(sparse.supports),
                          occurrence_counts=dict(sorted(Counter(freq.values()).items())),
                          designated_clause_indices=list(obj.designated_clauses),certificate_check=check))
    summary=dict(cases=len(cases),random_cases=20,all_labelled_kernel_checks=True,
                 all_post_affine_fixed_points=True,max_target_columns=max(len(c) for _,c in examples),
                 max_target_rank=max(c['certificate_check']['rank'] for c in cases),
                 max_source_clauses=max(c['source_clauses'] for c in cases),
                 named_targets=[c['name'] for c in cases if not c['name'].startswith('seeded_')])
    return dict(schema_version=1,all_checks_passed=True,seed=seed,cases=cases,summary=summary,
                scope='Matroid minors of difference systems after initial binary-group affine absorption. All constructed source formulas are positive and satisfiable. This is not a SAT lower bound or a new resolution of P vs NP.')


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--out-dir',required=True,type=Path)
    out=p.parse_args().out_dir;out.mkdir(parents=True,exist_ok=True)
    report=run_experiment();(out/'binary_minor_universality.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n')
    print(json.dumps(report['summary'],sort_keys=True))

if __name__=='__main__':main()
