"""Finite support localization audits and a four-clause expansion failure."""
import argparse
from itertools import combinations
import json
from pathlib import Path

from pnp_lab.modular_barrier import line_fixture
from pnp_lab.support_localization import support_audit


def petals():
    rows=[(1 if j<3 else -1,2+2*j,3+2*j) for j in range(7)]
    scopes=[tuple(v for j in triple for v in rows[j][1:]) for triple in combinations(range(7),3)]
    return rows,scopes


def signed_control(rows, scopes):
    # A signed bijection on 1..15 plus reversal of raw-clause order.
    perm=lambda v: 1+7*(v-1)%15
    sigma=lambda l: (1 if l>0 else -1)*(-1 if abs(l)%3==1 else 1)*perm(abs(l))
    return ([tuple(sigma(l) for l in c[::-1]) for c in rows[::-1]],
            [tuple(perm(v) for v in scope) for scope in scopes])


def summarize_petals(rows,scopes):
    r=support_audit(15,rows,scopes,width=4,s=6,delta=(2,1))
    assert r['status']=='CHECKED' and r['proper_ternary'] and r['boundary_condition']
    assert r['min_boundary_ratio']==[2,1] and r['min_neighborhood_surplus']==2
    assert r['width_window'] and r['scope_window']
    assert r['raw_input_lines']==7 and r['closure_lines']==19
    assert max(x['minimum_support_size'] for x in r['lines'])==2
    hist={}
    for p in r['scopes']:
        t=len(p['pooled_raw_ids'])
        hist[str(t)]=hist.get(str(t),0)+1
        assert p['all_unit_edges'] and p['all_square_faces']
        assert p['common_entails'] and len(p['common_raw_ids'])==3
        assert set(p['pooled_raw_ids']) <= set(p['common_raw_ids'])
        assert t*2<=len(p['scope'])
        assert all(i>=7 for i in p['lines'])
        # Replay witnesses directly, without the bit-table code that found
        # them. Compact variable labels for these controls happen to be 1..15.
        for f in p['unit_edges']+p['square_faces']:
            base,axes=f['base'],f['axes']
            for k in range(1<<len(axes)):
                word=base
                for h,v in enumerate(axes):
                    assert not (base >> (v-1) & 1)
                    if k>>h & 1:
                        word |= 1<<(v-1)
                for c in [rows[j] for j in p['common_raw_ids']]+[r['lines'][j]['clause'] for j in p['lines']]:
                    assert any(bool(word>>(abs(l)-1)&1)==(l>0) for l in c)
    assert hist=={'0':5,'3':30}
    sample=next(p for p in r['scopes'] if p['derived']==2)
    return dict(counts=r['counts'],min_boundary_ratio=r['min_boundary_ratio'],
                min_neighborhood_surplus=r['min_neighborhood_surplus'],
                raw_clauses=rows,closure_lines=r['closure_lines'],
                max_minimum_support=2,pooled_size_histogram=hist,sample_scope=sample,
                sample_lines=[r['lines'][j] for j in sample['lines']])


def provenance_detour(k):
    # No raw copy of the target. The short proof is not a subproof of the
    # particular long path: it uses two different raw clauses.
    path=[(1,2,4)]
    for v in range(4,3+k):
        path.append((-v,1,v+1))
    path.append((-(3+k),1,3))
    other=k+4
    rows=path+[(1,2,other),(-other,1,3)]
    line=set(path[0])
    for row in path[1:]:
        cross={l for l in line if -l in row}
        assert len(cross)==1
        pivot,=cross
        line=(line-{pivot})|(set(row)-{-pivot})
        assert len(line)==3
    assert line=={1,2,3}
    r=support_audit(other,rows,[(1,2,3)],width=3,s=len(rows))
    assert r['status']=='CHECKED'
    rec=next(row for row in r['lines'] if row['clause']==[1,2,3])
    assert rec['minimum_support_size']==2 and rec['minimum_raw_supports']==[[k+1,k+2]]
    return dict(raw_clauses=rows,target=[1,2,3],actual_proof_raw_ids=list(range(k+1)),
                actual_raw_ancestors=k+1,minimum_semantic_support=rec,
                cube_words=r['counts']['explicit_cube_words'],
                raw_subsets=r['counts']['raw_subsets'])


def locate_zero_boundary():
    """Find a Pasch configuration via intersecting pair-symmetric-difference buckets."""
    n,all_rows=line_fixture(0)
    rows=all_rows[:152]
    vs=[set(map(abs,c)) for c in rows]
    assert n==31 and all(len(t)==3 for t in vs)
    pairs=combinations(range(len(rows)),2)
    assert all(len(vs[i] & vs[j])<=1 for i,j in pairs)
    groups={}
    visits=0
    for i,j in combinations(range(len(rows)),2):
        visits+=1
        key=frozenset(vs[i]^vs[j])
        for a,b in groups.get(key,[]):
            ids=(a,b,i,j)
            if len(set(ids))!=4:
                continue
            union=set().union(*(vs[v] for v in ids))
            counts={x:sum(x in vs[t] for t in ids) for x in union}
            if len(union)==6 and all(count==2 for count in counts.values()):
                # For t<=3 in a linear ternary support family, each clause
                # shares at most t-1 of its 3 variables with the others. So
                # |boundary| >= t*(4-t)>0, proving the minimum of four.
                return dict(raw_ids=ids,raw_clauses=[rows[t] for t in ids],
                            incident_variables=sorted(union),occurrences=sorted(counts.items()),
                            boundary_size=0,minimum_boundary_zero_clause_count=4,
                            linearity_pairs_checked=len(rows)*(len(rows)-1)//2,
                            pair_hash_visits=visits)
        groups.setdefault(key,[]).append((i,j))
    raise AssertionError('no four-clause zero-boundary control found')


def run():
    cs,scopes=petals()
    base=summarize_petals(cs,scopes)
    renamed=summarize_petals(*signed_control(cs,scopes))
    detour=provenance_detour(6)
    raw_failure=locate_zero_boundary()
    # Non-ternary controls delimit the surplus argument: one positive raw
    # clause can already pin a bit, or exclude one corner of a square.
    unit=support_audit(1,[(1,)],[(1,)],width=1,s=2)
    binary=support_audit(2,[(1,2)],[(1,2)],width=2,s=2,delta=(2,1))
    for x in (unit,binary):
        assert x['boundary_condition'] and x['width_window'] and x['scope_window']
    assert not unit['scopes'][0]['all_unit_edges']
    assert binary['scopes'][0]['all_unit_edges'] and not binary['scopes'][0]['all_square_faces']
    assert not unit['proper_ternary'] and not binary['proper_ternary']
    caps=support_audit(15,cs,scopes,width=4,s=6,max_table_bits=1024)
    assert caps['status']=='UNVERIFIED' and 'scopes' not in caps
    return dict(all_checks_passed=True,positive=[base,renamed],width=4,scope_size=6,
                raw_fragment_limit=6,delta=[2,1],provenance_detour=detour,
                phase16_expansion_failure=raw_failure,
                nonternary_controls=[unit,binary],capped_control=caps,
                summary=dict(positive_cases=2,raw_subsets_per_positive_case=128,
                             cube_words_per_positive_case=32768,scopes_per_case=35,
                             scopes_attaining_pool_bound_per_case=30,
                             scopes_attaining_structural_bound_per_case=35,
                             largest_pool=3,largest_minimum_support=2,
                             unit_edges_per_case=210,square_faces_per_case=525,
                             detour_actual_ancestors=7,detour_minimum_support=2,
                             phase16_minimum_zero_boundary=4),
                scope='Small exhaustive semantic audits on named inputs, not a SAT solver, not an expander generator, and not a proof of the asymptotic theorem.')


if __name__=='__main__':
    cli=argparse.ArgumentParser()
    cli.add_argument('--out-dir',type=Path,required=True)
    out=cli.parse_args().out_dir
    out.mkdir(parents=True,exist_ok=True)
    report=run()
    (out/'support_localization.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n')
    print(report['summary'])
