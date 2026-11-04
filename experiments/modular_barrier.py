"""Finite, raw-CNF checks for the local-hull barrier; large-girth result is analytic."""
import argparse
from itertools import combinations
import json
from pathlib import Path
import random

from pnp_lab.modular_barrier import (check_tree, check_preorder, preorder, hall_free_cube, incidence_girth,
                                     lift_stretched, line_fixture, raw_search, satisfies, stretched_image)


def _nodes(t):
    return 1 if type(t) is int else 1+_nodes(t[1])+_nodes(t[2])


def _cover_bound(t):
    # If t clauses used at most t+1 vars, linearity forces at most
    # floor((t+1)*floor(t/2)/3) triples there, by vertex degree.
    return (t+1)*(t//2)//3


def fixture():
    n,rows=line_fixture(0);core=rows[:152]
    sat_word,fail=raw_search(core[:-1]);model,proof=raw_search(core)
    assert model is None and check_tree(n,core,proof) and sat_word is not None
    assert satisfies(core[:-1],sat_word) and not satisfies(core,sat_word)
    return n,core,sat_word,proof


def run():
    n,negative,pin_word,proof=fixture()
    positive=tuple(tuple(map(abs,c)) for c in negative);all_one=(1<<n)-1
    assert satisfies(positive,all_one) and len(positive)==len(negative)
    pairs=[p for c in positive for p in combinations(sorted(c),2)]
    assert len(pairs)==len(set(pairs))
    assert all(_cover_bound(t)<t for t in (1,2,3,4,5))
    assert incidence_girth(n,negative)==6
    rng=random.Random(1143);squares=axes=0
    for raw in (positive,negative):
        for _ in range(30):
            ids=rng.sample(range(len(raw)),6);five=tuple(raw[i] for i in ids[:5])
            six=tuple(raw[i] for i in ids)
            scope=sorted(set(abs(l) for c in six for l in c))
            for v in scope:
                x=hall_free_cube(n,six,[v])
                assert x is not None and satisfies(six,x) and satisfies(six,x^(1<<(v-1)))
                axes+=1
            for v,w in combinations(scope,2):
                x=hall_free_cube(n,five,[v,w])
                assert x is not None
                assert all(satisfies(five,x ^ a ^ b) for a in (0,1<<(v-1)) for b in (0,1<<(w-1)))
                squares+=1
    # Repeated occurrences in distinct clauses make the equality wires necessary.
    source=((1,2,3),(-1,2,4));pin=negative[:-1];false=negative[-1][0];k=2
    big,rows,copy,starts=stretched_image(4,source,k,n,pin,false)
    assert incidence_girth(big,rows)>2*k
    models=0
    for x in range(16):
        y=lift_stretched(x,pin_word,copy,starts)
        assert satisfies(rows,y)==satisfies(source,x)
        models+=int(satisfies(source,x))
    tokens=preorder(proof)
    assert check_preorder(n,negative,tokens)
    return dict(schema_version=1,all_checks_passed=True,
        summary=dict(variables=n,clauses=len(negative),incidence_girth=6,refutation_nodes=_nodes(proof),
                     free_axis_pairs_checked=axes,free_squares_checked=squares,stretched_variables=big,
                     stretched_clauses=len(rows),small_source_models=models),
        fixture=dict(line_dimension=5,seed=0,prefix=152,tree_preorder=tokens,pin_model=pin_word,
                     removed_clause=list(negative[-1]),positive_model=all_one,
                     all_fragments_affine_through_clauses=6,all_fragments_quadratic_through_clauses=5),
        scope="Concrete local checks and a linear-support SAT/UNSAT twin. Large-girth NP-hardness and the n/1000 random-support existence theorem are proved, not measured.")


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--out-dir',type=Path,required=True)
    out=p.parse_args().out_dir;out.mkdir(exist_ok=True,parents=True)
    data=run();(out/'modular_barrier.json').write_text(json.dumps(data,sort_keys=True,indent=2)+'\n')
    print(data['summary'])
