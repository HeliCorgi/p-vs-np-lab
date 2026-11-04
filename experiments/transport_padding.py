"""Compare three certificate stages on private-split parity circuits."""
import argparse
import json
from pathlib import Path
from pnp_lab.decision_pruning import solve_pruned
from pnp_lab.private_resolution import check_private_parity, private_parity_refute
from pnp_lab.split_parity import split_parity_refute
from pnp_lab.transport_obstruction import restrict, switch_tseitin
from pnp_lab.transport_resolution_padding import contract_twice, padded_tseitin


def require(p,why):
    if not p:raise AssertionError(why)


def run():
    families=[]; prefix_checks=0
    for k in (1,2,3,4,8,32):
        n,rows=padded_tseitin(k);_,old=switch_tseitin(k)
        require((n,len(rows))==(45*k+86,68*k+116),"size")
        if k<=4:
            for d in range(k+1):
                for word in range(1<<d):
                    actual=contract_twice(restrict(rows,d,word))
                    require(actual==frozenset(map(frozenset,restrict(old,d,word))),"blind contraction")
                    prefix_checks+=1
        basic=split_parity_refute(n,rows)
        require(basic['status']=='UNKNOWN' and basic['stats']['base_rows']==0 and basic['stats']['common_rows']==k,
                "single-pivot gate")
        plus=private_parity_refute(n,rows)
        require(plus['status']=='UNSAT' and check_private_parity(n,rows,plus['certificate']),"resolved root proof")
        f=dict(k=k,variables=n,clauses=len(rows),bare_status=basic['status'],bare_common_rows=basic['stats']['common_rows'],
               resolved_status=plus['status'],resolvents_added=plus['stats']['resolvents_added'],
               raw_prefix_antichain_size=str(1<<k),width_from_theorem_not_enumeration=k>2)
        if k<=2:
            r=solve_pruned(n,rows,max_width=k,label_mode='blocked',transport=True,split_parity=True)
            require(r['status']=='UNKNOWN' and r['widths']==[1<<j for j in range(k+1)] and
                    r['stats']['transport_drops']==r['stats']['anchor_merges']==r['stats']['individual_merges']==0,
                    "combined branch widths")
            f['combined_at_cap']=dict(status=r['status'],widths=r['widths'],width_cap=k,
                                     or_labels=r['stats']['or_labels'],transport_checks=r['stats']['transport_checks'])
        families.append(f)
    return dict(schema_version=1, all_checks_passed=True, controls=families,
                summary=dict(prefix_contractions_checked=prefix_checks,
                             largest_combined_width_observed=4,largest_checked_k=families[-1]['k'],
                             last_variables=families[-1]['variables'],last_clauses=families[-1]['clauses'],
                             last_resolvents=families[-1]['resolvents_added']),
                scope="All-size width for the specified tag order and exact three pre-private-resolution pruning policies; bounded combined-driver runs distinguished from the proof. No general SAT lower bound.")


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--out-dir',type=Path,required=True)
    out=p.parse_args().out_dir;out.mkdir(parents=True,exist_ok=True)
    r=run();(out/'transport_padding.json').write_text(json.dumps(r,sort_keys=True,indent=2)+'\n');print(r['summary'])
