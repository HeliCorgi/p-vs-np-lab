#!/usr/bin/env python3
"""Finite checks for translated matching, quotient filtering, and its source-image limit."""
from __future__ import annotations

import argparse
from functools import reduce
import json
from operator import xor
from pathlib import Path
import random

from pnp_lab.gauge_matching import decide_with_gauge_matching
from pnp_lab.ternary_support import three_cnf_to_weight_two_supports

SEED = 720019


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def xor_all(values):
    return reduce(xor, values, 0)


def affine_relaxation(supports, rhs):
    """Only exclude targets outside the affine hull of all jointly reachable sums."""
    target, pivots = rhs, {}
    for group in supports:
        if not group:
            return 'REJECTED'
        a = group[0]
        target ^= a
        for x in group[1:]:
            vector = x ^ a
            while vector:
                p = vector.bit_length()-1
                if p not in pivots:
                    pivots[p] = vector
                    break
                vector ^= pivots[p]
    while target:
        row = pivots.get(target.bit_length()-1)
        if row is None:
            return 'REJECTED'
        target ^= row
    return 'KEPT'


def check_choice(groups, rhs, r):
    if r['status'] != 'SAT':
        require(r['witness'] is None, 'Non-SAT result has a witness')
        return
    w = r['witness']
    require(len(w) == len(groups) and all(v in g for v,g in zip(w,groups))
            and xor_all(w) == rhs, 'Invalid original choice')
    unit = [c ^ v for c,v in zip(r['centers'],w)]
    require(unit == r['translated_witness'] and all(v.bit_count() <= 1 for v in unit)
            and xor_all(unit) == r['translated_rhs'] == rhs ^ xor_all(r['centers']),
            'Invalid translated choice')


def work(r):
    names = ('status', 'reason', 'groups', 'defect_groups', 'binary_defects', 'nonbinary_defects',
             'branches_total', 'outer_branches_total', 'outer_branches_checked',
             'outer_branches_inconsistent', 'raw_branches_ruled_out', 'compatible_branches_identified',
             'min_binary_rank', 'max_binary_rank', 'matching_calls', 'graph_vertices_peak', 'graph_edges_peak')
    return {k:r[k] for k in names}


def translated_controls():
    cases = []
    for m in (8,16,32):
        units = [(0, 1 << i, 1 << m) for _ in range(2) for i in range(m)]
        full = (1 << (m+1))-1
        centers = [full ^ (1 << (j % (m+1))) for j in range(2*m)]
        groups = [[x ^ c for x in s] for c,s in zip(centers,units)]
        planted = [s[1] if j < m and j % 2 == 0 else (s[2] if j == m else 0)
                   for j,s in enumerate(units)]
        target = xor_all(planted) ^ xor_all(centers)
        require(all(x.bit_count()>1 for g in groups for x in g), 'Not a genuine translation')
        r = decide_with_gauge_matching(groups,target,max_matching_calls=1,max_outer_branches=1)
        check_choice(groups,target,r)
        require((r['status'],r['defect_groups'],r['matching_calls']) == ('SAT',0,1), 'Translated control')
        case = dict(m=m, target=target, polynomial_hull=affine_relaxation(groups,target),
                    original_min_weight=min(x.bit_count() for g in groups for x in g), **work(r))
        if m == 8:
            case.update(original_supports=groups, centers=r['centers'],
                        checked_original_witness=r['witness'], translated_rhs=r['translated_rhs'],
                        translated_witness=r['translated_witness'])
        cases.append(case)
    # Three vertices of an affine square do not contain its missing corner.
    # Use a dense shift, so none of the original options is itself a unit.
    tag = 124
    groups = [(tag,tag^1,tag^2)]
    target = tag ^ 3
    r = decide_with_gauge_matching(groups,target,max_matching_calls=1)
    require(affine_relaxation(groups,target) == 'KEPT' and r['status'] == 'UNSAT'
            and r['matching_calls'] == 1, 'Affine hull/actual matching distinction')
    cases.append(dict(name='missing_affine_corner', original_supports=groups, target=target,
                      polynomial_hull='KEPT', **work(r)))
    return cases


def truth_models(n, clauses):
    return [b for b in range(1 << n)
            if all(any(((b >> (abs(x)-1)) & 1) == int(x>0) for x in c) for c in clauses)]


def exclude_mask(n, b):
    return tuple(-(i+1) if (b >> i)&1 else i+1 for i in range(n))


def source_case(n, clauses):
    models=truth_models(n,clauses)
    red=three_cnf_to_weight_two_supports([f'x{i}' for i in range(n)],clauses)
    r=decide_with_gauge_matching(red.supports,red.rhs)
    check_choice(red.supports,red.rhs,r)
    require((r['status']=='SAT') == bool(models), 'Gauge decision vs direct truth table')
    active=0
    for clause in clauses:
        for lit in clause:
            active |= 1 << (abs(lit)-1)
    for b in models:
        choices = red.lift_witness(b)
        require(all(x in g for x,g in zip(choices,red.supports)) and xor_all(choices)==red.rhs
                and red.project_witness(choices) == (b & active), 'Source lift/project')
    model = red.project_witness(r['witness']) if models else None
    if models:
        require(model in models,'Gauge witness fails source formula')
    relaxed=affine_relaxation(red.supports,red.rhs)
    require(relaxed != 'REJECTED' or not models, 'Relaxation rejected an actual solution')
    return dict(source_variables=n, source_assignments_checked=1<<n, source_models=len(models),
                polynomial_hull=relaxed, projected_witness_mask=model, **work(r))


def run_experiment():
    dense=translated_controls()
    rng=random.Random(SEED)
    random_cases=[]
    for _ in range(72):
        n=rng.randrange(1,6)
        clauses=[tuple(rng.choice((-1,1))*rng.randint(1,n) for _ in range(rng.randrange(1,4)))
                 for _ in range(rng.randrange(1,9))]
        random_cases.append(source_case(n,clauses))
    controls=[]
    unique=[exclude_mask(3,b) for b in range(8) if b != 5]
    impossible=[exclude_mask(3,b) for b in range(8)]
    for label,n,clauses in [('none',0,[]),('empty_clause',2,[()]),('unused_scope',3,[(1,)]),
                           ('one_nonconstant_model',3,unique),('no_model',3,impossible)]:
        c=source_case(n,clauses); c.update(name=label,source_cnf=clauses);controls.append(c)
    require(controls[-2]['source_models']==1 and controls[-2]['projected_witness_mask']==5
            and controls[-1]['source_models']==0
            and all(c['polynomial_hull']=='KEPT' and c['compatible_branches_identified']==8
                    for c in controls[-2:]), 'Nontrivial source/hull controls')
    cycles=[]
    for n in (3,4,5,7):
        clauses=[]
        for j in range(n):
            a,b = j+1,(j+1)%n+1
            clauses.extend(((a,b),(-a,-b)))
        c=source_case(n,clauses)
        require(c['branches_total']==2**(4*n) and c['max_binary_rank']==3*n
                and c['compatible_branches_identified']==2**n and c['polynomial_hull']=='KEPT',
                'Source-image selector rank')
        if n%2:
            require(c['status']=='UNSAT' and c['matching_calls']==2**n,'Odd-cycle all leaves')
        else:
            require(c['status']=='SAT' and c['projected_witness_mask'] in (5,10),'Even cycle')
        cycles.append(c)
    budget=[]
    r=decide_with_gauge_matching(three_cnf_to_weight_two_supports(('a','b','c'),impossible).supports,
                                 0,max_matching_calls=7)
    require(r['status']=='UNKNOWN' and r['matching_calls']==7 and r['witness'] is None,'Call budget')
    budget.append(dict(name='UNSAT_source_before_last_matching_call',**work(r)))
    r=decide_with_gauge_matching([(0,7,56)],1,max_matching_calls=0,max_outer_branches=2)
    require(r['status']=='UNKNOWN' and r['outer_branches_checked']==2 and r['matching_calls']==0,
            'Independent outer budget')
    budget.append(dict(name='outer_budget_before_last_affine_rejection',**work(r)))
    checked=random_cases+controls+cycles
    return dict(schema_version=1, all_checks_passed=True, seed=SEED,
                summary=dict(source_oracle_cases=len(checked),seeded_cases=len(random_cases),
                             source_assignments_checked=sum(c['source_assignments_checked'] for c in checked),
                             source_models_lifted=sum(c['source_models'] for c in checked),
                             source_sat=sum(c['status']=='SAT' for c in checked),
                             source_unsat=sum(c['status']=='UNSAT' for c in checked),
                             largest_matched_translated_groups=dense[-2]['groups'],
                             odd_cycle_measured_max_variables=7,odd_cycle_measured_max_calls=cycles[-1]['matching_calls'],
                             odd_cycle_raw_bound_at_max=cycles[-1]['branches_total'],
                             unknown_budget_controls=len(budget)),
                dense_translations=dense,source_controls=controls,cycles=cycles,budget_controls=budget,
                scope='Calls are measured; branches_total is a BEFORE-pruning product, not measured work. KEPT means the target is in the affine hull, not necessarily satisfiable. Every recorded SAT choice was checked, and every original-source result was compared with all original assignments. None of these finite checks establishes polynomial time on the general class.')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out-dir',type=Path,required=True)
    out=parser.parse_args().out_dir
    out.mkdir(parents=True,exist_ok=True)
    data=run_experiment()
    (out/'gauge_matching.json').write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
    print(json.dumps(data['summary'],indent=2,sort_keys=True))


if __name__=='__main__': main()
