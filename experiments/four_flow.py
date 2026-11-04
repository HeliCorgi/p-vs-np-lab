"""Characteristic blindness on local models of a cyclic-four flow (including full stars)."""
import argparse,json
from itertools import product
from pathlib import Path
from pnp_lab.four_flow import four_flow,four_prism_flow,four_state_word,parity_lift,state_permutations
from pnp_lab.cyclic_four import solve_cyclic_four,check_cyclic_four
from pnp_lab.modular_hull import collect_modular_rows
from pnp_lab.ternary_flow import prism_edges,divergence,scramble


def holds(cs,x):
    return all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in c) for c in cs)


def _rank(table,p):
    basis={}
    for point in table:
        word=list(point)
        for j in sorted(basis):
            if word[j]%p:
                a=word[j];word=[(x-a*y)%p for x,y in zip(word,basis[j])]
        i=next((i for i,x in enumerate(word) if x%p),None)
        if i is not None:
            inv=pow(word[i]%p,-1,p);basis[i]=[x*inv%p for x in word]
    return len(basis)


def local_oracles():
    # Project to all five coordinates per participating edge, even though ordinary
    # width-nine finder does not use these 15- and 25-coordinate scopes.
    k=8;ed=prism_edges(k);vals=tuple((3*i+1)%4 for i in range(len(ed)))
    good=divergence(ed,vals,2*k,4);bad=((good[0]+2)%4,)+good[1:]
    pi=state_permutations(len(ed),14144);res=[]
    for vertices in ((0,),(0,1)):
        ix=[i for i,(a,b) in enumerate(ed) if a in vertices or b in vertices]
        def point(t):
            out=[]
            for j,s in zip(ix,t):
                target=pi[j][s];out.extend(int(target==i) for i in range(4));out.append(int(target>=2))
            return tuple(out)
        models=[]
        for t in product(range(4),repeat=len(ix)):
            div=divergence([ed[j] for j in ix],t,2*k,4)
            if all(div[v]==bad[v] for v in vertices):models.append(point(t))
        witness=point([vals[j] for j in ix])
        assert witness not in models
        base=models[0];rows=[tuple(x-y for x,y in zip(m,base)) for m in models]
        for p in (2,3,5,7):
            rank=_rank(rows,p)
            with_word=_rank(rows+[tuple(x-y for x,y in zip(witness,base))],p)
            assert rank==with_word==3*len(ix)-(len(vertices) if p==2 else 0)
            res.append(dict(field=p,vertices=len(vertices),boolean_bits=5*len(ix),
                            model_count=len(models),affine_dimension=rank,
                            common_word_in_hull=True,common_word_is_raw_model=False))
    return res


def run():
    out=[];total=0
    for k in (3,8,16,32):
        n,g,x=four_prism_flow(k);n,raw,_=four_prism_flow(k,True)
        bad,common=scramble(n,raw,x,14557+k)
        g,sat=scramble(n,g,x,14557+k)
        assert common==sat and holds(g,sat) and not holds(bad,common)
        f=[]
        for p in (2,3):
            rows,stats=collect_modular_rows(n,bad,prime=p)
            assert all(sum(a*((common>>(v-1))&1) for v,a in zip(r['scope'],r['coeff']))%p==r['rhs'] for r in rows)
            total+=len(rows)
            f.append(dict(field=p,raw_scope_rows_checked=len(rows),scope_count=stats['scopes_examined']))
        native_odd=solve_cyclic_four(n,bad);native_good=solve_cyclic_four(n,g)
        assert native_odd['status']=='UNSAT' and check_cyclic_four(n,bad,native_odd)
        assert native_odd['stats']['residual_rhs']==2
        assert native_good['status']=='SAT' and check_cyclic_four(n,g,native_good)
        out.append(dict(native_sat='SAT',native_conflict_rhs=2,native_validated=True,
                        native_unsat_terms=len(native_odd['certificate']['terms']),k=k,variables=n,clauses=len(bad),state_seed=14144,code_scramble_seed=14557+k,
                        primes=f,reference_is_balanced_model=True,reference_falsifies_unbalanced=True))
    return dict(schema_version=1,all_checks_passed=True,controls=out,large_scope_oracles=local_oracles(),
                summary=dict(ambient_prime_rows_checked=total,full_star_fields=[2,3,5,7],
                             full_two_star_boolean_bits=25,largest_raw_variables=out[-1]['variables'],
                             largest_raw_clauses=out[-1]['clauses'],largest_native_proof_terms=out[-1]['native_unsat_terms']),
                scope='Finite rows for 2,3 and complete small local tables for 2,3,5,7. All-field all-scope claim is the graph/character argument, not exhaustive enumeration.')


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--out-dir',type=Path,required=True)
    d=p.parse_args().out_dir;d.mkdir(parents=True,exist_ok=True);r=run()
    (d/'four_flow.json').write_text(json.dumps(r,sort_keys=True,indent=2)+'\n');print(r['summary'])
