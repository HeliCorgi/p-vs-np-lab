#!/usr/bin/env python3
"""Positive graphic certificates and checked Fano obstructions on sparse 3SAT images."""
from __future__ import annotations

import argparse
import json
from functools import reduce
from itertools import combinations, product
from operator import xor
from pathlib import Path

from pnp_lab.fano_minor import quotient_binary_groups, relabel_difference, verify_fano_minor
from pnp_lab.graphic_support import (decide_graphic_supports, graphic_difference_basis,
                                     verify_graphic_certificate)
from pnp_lab.ternary_support import three_cnf_to_weight_two_supports

ROOT = Path(__file__).resolve().parents[1]


def check(ok, message):
    if not ok:
        raise AssertionError(message)


def exact_models(clauses, n):
    return [assignment for assignment in range(1 << n) if all(
        any(bool(assignment & (1 << (abs(literal) - 1))) == (literal > 0)
            for literal in clause) for clause in clauses)]


def hidden_matching():
    # Each dense column has a distinct highest bit; the map is injective.
    # Underlying seven row choices form a chain of three overlapping triples.
    cols = [1, 3, 5, 15, 22, 53, 107]
    triples = [(0,1,2), (2,3,4), (4,5,6)]
    offsets = [1 << 9 | 11, 1 << 10 | 23, 1 << 11 | 45]
    supports = [[cols[j] ^ offset for j in triple] for triple, offset in zip(triples, offsets)]
    diameter = [max((a ^ b).bit_count() for a,b in combinations(s,2)) for s in supports]
    check(max(diameter) > 2, 'Example would fit Hamming-one balls without a basis change')
    edges = {cols[i] ^ cols[j]: (i,j) for i,j in combinations(range(7),2)}
    basis = list(graphic_difference_basis(supports))
    cert = dict(basis_vectors=basis, basis_edges=[edges[x] for x in basis])
    check(verify_graphic_certificate(supports, cert), 'Positive certificate')
    reachable = {reduce(xor, choices, 0) for choices in product(*supports)}
    totals = {'SAT': 0, 'UNSAT_by_matching': 0, 'UNSAT_outside_hull': 0}
    images = []
    for rhs0 in range(128):
        rhs = reduce(xor, (c for j,c in enumerate(cols) if rhs0 & (1 << j)),
                     reduce(xor,offsets,0))
        ans = decide_graphic_supports(supports,rhs,basis_edges=cert['basis_edges'])
        check(ans['status'] == ('SAT' if rhs in reachable else 'UNSAT'), 'Truth-table mismatch')
        if ans['status'] == 'SAT':
            w = ans['witness']
            check(len(w)==len(supports) and all(v in g for v,g in zip(w,supports))
                  and reduce(xor,w,0)==rhs, 'Original witness check')
            totals['SAT'] += 1
        elif ans['matching_calls']:
            totals['UNSAT_by_matching'] += 1
        else:
            check(ans['reason'] == 'outside_affine_hull', 'Unexpected negative without matching')
            totals['UNSAT_outside_hull'] += 1
        if rhs0 in (42,127):  # one selected vertex in each triple, or all seven vertices requested
            probe = decide_graphic_supports(supports,rhs,max_tree_trials=256)
            check(probe['status'] in ('UNKNOWN',ans['status']), 'Automatic discovery false answer')
            images.append({'underlying_rhs_mask':rhs0,'raw_target':rhs,'status':ans['status'],
                           'reason':ans['reason'],'matching_calls':ans['matching_calls'],
                           'witness':ans['witness'],'bounded_search_status':probe['status'],
                           'bounded_search_method':probe['tree_method'],'bounded_tree_trials':probe['tree_trials']})
    check(images[0]['status']=='SAT' and images[1]['status']=='UNSAT' and images[1]['matching_calls']==1,
          'Expected both matching outcomes')
    return dict(raw_supports=supports,certificate=cert,raw_group_diameters=diameter,
                full_original_choice_tuples=27,distinct_reachable_targets=len(reachable),
                target_checks=totals, examples=images)


def occurrence_columns(groups, locals0, x_positions, aux_positions):
    v = lambda j: 1 << (2*j)
    c = lambda j: 2 << (2*j)
    def local(j, value):
        return relabel_difference(groups,locals0+j,value)
    aux = [local(j,v(j)^c(j)) for j in aux_positions]
    keep = ([local(j,v(j)) for j in x_positions] + [local(x_positions[0], c(x_positions[0]))]
            + [local(j,v(j)^c(j)) for j in x_positions])
    return aux, keep


def minor(con, keep):
    return dict(contract=con,keep=keep,expected_contracted_rank=len(con),
                expected_minor_rank=3,quotient_basis_keep_indices=[0,1,3],
                expected_quotient_coordinates=list(range(1,8)))


def fixture_and_signs():
    fixture=json.loads((ROOT/'examples/graphic_fano_minor.json').read_text())
    names = fixture['source_variables']
    source = fixture['source_cnf']
    groups = three_cnf_to_weight_two_supports(names,source).supports
    fixture_check=verify_fano_minor(groups,fixture)
    t,m=9,3
    copy=[[j,0,1] for j in range(t)]
    sel=[[t+i,0,p] for i in range(m) for p in (1,2)]
    count=assignments=models=0
    for signs in product((-1,1),repeat=t):
        signed=[[x*signs[3*i+k] for k,x in enumerate(cl)] for i,cl in enumerate(source)]
        gs=three_cnf_to_weight_two_supports(names,signed).supports
        # Recover labels from raw option *values*: sign-flipped implication groups reorder the pairs.
        aux, keep = occurrence_columns(gs,t+m,(0,3,6),(1,4,2,7))
        verify_fano_minor(gs,minor(copy+sel+aux,keep))
        q,info=quotient_binary_groups(gs)
        check(info=={'binary_groups':9,'contracted_rank':9,'fixed_point':True},'Binary quotient')
        verify_fano_minor(q,minor(sel+aux,keep))
        raw_models=exact_models(signed,len(names))
        check(bool(raw_models),'Three width-three clauses on four named variables should have a model')
        models+=len(raw_models);assignments+=1<<len(names);count+=1
    return dict(named_fixture=fixture_check,signings=count,raw_minor_checks=count,
                projected_minor_checks=count,source_assignments_examined=assignments,
                summed_source_models=models,
                scope='Source models checked separately; the minor only certifies nonrepresentability.')


def signed_cube():
    names=('x','y','z')
    clauses=[tuple((j+1)*s for j,s in enumerate(signs)) for signs in product((-1,1),repeat=3)]
    check(exact_models(clauses,3)==[],'Cube not UNSAT')
    removals=[len(exact_models(clauses[:i]+clauses[i+1:],3)) for i in range(8)]
    check(removals==[1]*8,'Cube not minimally UNSAT')
    red=three_cnf_to_weight_two_supports(names,clauses);gs=red.supports;t,m=24,8
    xs,ys,zs=(0,3,6),(1,4),(2,8)
    aux,keep=occurrence_columns(gs,t+m,xs,ys+zs)
    excepted=set(xs+ys+zs)
    vdel=[relabel_difference(gs,t+m+j,1<<(2*j)) for j in range(t) if j not in excepted]
    sel=[[t+i,0,p] for i in range(3) for p in (1,2)]
    tail=vdel+sel+aux
    raw=verify_fano_minor(gs,minor([[j,0,1] for j in range(t)]+tail,keep))
    q,info=quotient_binary_groups(gs)
    check(info['fixed_point'] and info['contracted_rank']==t,'Cube presolve rank')
    post=verify_fano_minor(q,minor(tail,keep))
    return dict(source_variables=3,source_clauses=8,source_assignments_examined=8,
                source_models=0,models_after_each_single_clause_deletion=removals,
                raw_contraction_rank=raw['contraction_rank'],binary_presolve=info,
                additional_contraction_rank=post['contraction_rank'],
                quotient_coordinates=post['quotient_coordinates'])


def packing(g):
    names=[f'{v}{i}' for i in range(g) for v in ('x','a','b','c')]
    clauses=[]
    for i in range(g):
        x,a,b,c=range(4*i+1,4*i+5)
        clauses.extend(((x,a,b),(x,a,c),(x,b,c)))
    clauses.extend((4*i+4,4*i+8,4*i+12) for i in range(g-2))
    m,t=len(clauses),3*len(clauses)
    check((m,t)==(4*g-2,12*g-6),'Family size')
    red=three_cnf_to_weight_two_supports(names,clauses);gs=red.supports
    check(red.project_witness(red.lift_witness((1<<len(names))-1))==(1<<len(names))-1,
          'All-true constructive witness')
    q,info=quotient_binary_groups(gs)
    check(info['fixed_point'] and info['contracted_rank']==t,'Packing presolve rank')
    used=set();used_projection=set()
    for i in range(g):
        o,s=9*i,t+3*i
        copy=[[o+j,0,1] for j in (0,1,2,3,4,6,7)]
        sel=[[s,0,1],[s,0,2],[s+1,0,1],[s+2,0,1]]
        aux,keep=occurrence_columns(gs,t+m,[o+j for j in (0,3,6)],[o+j for j in (1,4,2,7)])
        raw=verify_fano_minor(gs,minor(copy+sel+aux,keep))
        proj=verify_fano_minor(q,minor(sel+aux,keep))
        r,p=set(raw['groups_used']),set(proj['groups_used'])
        check(len(r)==17 and len(p)==10 and not (used&r or used_projection&p),
              'Non-disjoint certificate group labels')
        used|=r;used_projection|=p
    occurrences=[sum(c.count(i) for c in clauses) for i in range(1,len(names)+1)]
    check(max(occurrences)<=5 and min(occurrences)>=2,'Bounded occurrences')
    return dict(gadgets=g,source_variables=len(names),source_clauses=m,max_source_occurrences=max(occurrences),
                source_all_true_witness_checked=True,support_groups=len(gs),binary_presolve=info,
                verified_raw_minors=g,verified_projected_minors=g,raw_disjoint_groups_used=len(used),
                projected_disjoint_groups_used=len(used_projection))


def run_experiment():
    good=hidden_matching();basic=fixture_and_signs();cube=signed_cube();packed=[packing(g) for g in (3,5,8)]
    return dict(schema_version=1,all_checks_passed=True,hidden_graphic=good,
                sign_invariance=basic,minimally_unsat_signed_cube=cube,packing=packed,
                summary=dict(hidden_targets_checked=sum(good['target_checks'].values()),
                             hidden_matching_unsat=good['target_checks']['UNSAT_by_matching'],
                             signings_with_raw_and_post_presolve_fano=basic['signings'],
                             minimally_unsat_cube_fano_checked=True,
                             largest_connected_obstruction_packing=packed[-1]['gadgets']),
                scope='Finite reproducible checks, not a general SAT lower bound. The proofs for arbitrary size are in docs/graphic_gauge.md.')


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--out-dir',type=Path,required=True)
    out=p.parse_args().out_dir;out.mkdir(parents=True,exist_ok=True)
    result=run_experiment()
    (out/'graphic_matching.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print(json.dumps(result['summary'],sort_keys=True))


if __name__=='__main__':
    main()
