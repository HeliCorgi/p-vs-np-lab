"""Finite checks of a linear-size direct-witness-transport antichain."""
import argparse
from collections import Counter
import json
from pathlib import Path
from pnp_lab.transport_obstruction import (switch_tseitin, restrict, decode_word, critical_model,
                                         conservation_refutation, verify_conservation)


def check(x,reason):
    if not x:raise AssertionError(reason)


def run():
    families=[]; witness_total=0; complete_total=0; prefix_total=0
    for k in (1,2,3,4,5):
        n,cs=switch_tseitin(k);proof=conservation_refutation(n,cs)
        check(verify_conservation(n,cs,proof),"raw root check")
        leaves=[decode_word(restrict(cs,k,word)) for word in range(1<<k)]
        check(leaves==list(range(1<<k)),"unsigned supports must encode the word")
        complete_total+=len(leaves)
        levels=[]; count=0
        for d in range(k+1):
            words=range(1<<d);sizes=set();literal_totals=set()
            spectra=[]
            for prefix in words:
                sub=restrict(cs,d,prefix);sizes.add(len(sub));literal_totals.add(sum(map(len,sub)))
                groups={tuple(sorted(map(abs,c))) for c in sub}
                degrees=Counter(v for vs in groups for v in vs)
                check({v for v,c in degrees.items() if c>3}==set(range(d+1,k+1)),"tag detection")
                spectra.append({leaves[w] for w in range(1<<k) if (w&((1<<d)-1))==prefix})
                prefix_total+=1
                if k<=3:
                    for j in range(len(sub)):
                        x=critical_model(n,sub,k,j)
                        check([i for i,c in enumerate(sub) if not any(bool(x&1<<(abs(l)-1))==(l>0) for l in c)]==[j],
                              "independent raw formula critical model check")
                        count+=1
            check(sizes=={40*k+58-6*d} and len(literal_totals)==1,"equal size and total width")
            check(all(a.isdisjoint(b) for i,a in enumerate(spectra) for b in spectra[i+1:]),"completion invariant")
            levels.append(dict(depth=d,raw_restrictions=len(words),clauses=sizes.pop(),total_literals=literal_totals.pop(),
                               completions_per_prefix=1<<(k-d)))
        witness_total+=count
        families.append(dict(k=k,n=n,clauses=len(cs),levels=levels,critical_assignments_checked=count,root_proof_terms=len(proof)))
    large=[]
    for k in (16,64,128):
        n,cs=switch_tseitin(k)
        proof=conservation_refutation(n,cs)
        check(verify_conservation(n,cs,proof),"non-enumerative root check")
        large.append(dict(k=k,n=n,clauses=len(cs),root_proof_terms=len(proof),
                          theorem_raw_leaf_antichain=str(1<<k),leaf_set_enumerated=False))
    return dict(schema_version=1,all_checks_passed=True,exhaustive_small=families,symbolic_large=large,
                summary=dict(critical_assignments_checked=witness_total,complete_unsigned_codes_checked=complete_total,
                             prefix_structures_checked=prefix_total,largest_root_checked=large[-1]['k'],
                             largest_root_variables=large[-1]['n'],largest_root_clauses=large[-1]['clauses']),
                scope="Width bound is on direct raw syntactic literal/constant certificate domination at the designated cut/order. Conservation refutes these formulas directly; no general SAT lower bound.")


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--out-dir',required=True,type=Path)
    out=p.parse_args().out_dir;out.mkdir(parents=True,exist_ok=True)
    r=run();(out/'transport_obstruction.json').write_text(json.dumps(r,sort_keys=True,indent=2)+'\n');print(r['summary'])
