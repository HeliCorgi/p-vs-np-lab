"""Exhaustively check the absorption/extension invariant on a small signed 3-CNF.

This checks adversary state transitions, not an asymptotic UNSAT lower bound.
The deliberately small fixture is satisfiable; it is not a sampled expander.
"""
import argparse
import json
from pathlib import Path


def audit():
    m = 7
    raw = [((1 if j%2 else -1), (2+2*j)*(1 if j%3 else -1),
            (3+2*j)*(1 if j%2 else -1)) for j in range(m)]
    vs = {abs(l) for c in raw for l in c}
    masks = range(1<<m)
    groups = {i:frozenset(j for j in range(m) if i>>j&1) for i in masks}
    nbr = {g:frozenset(abs(l) for j in g for l in raw[j]) for g in groups.values()}
    assert all(4*len(n)>7*len(g) for g,n in nbr.items() if g)
    stats = dict(states_checked=0, residual_neighborhood_checks=0, free_edges=0,
                 forced_edges=0, both_values_checks=0, absorbed_nonempty=0,
                 largest_block=0, repair_assignments=0, histories=0,
                 signed_input_clauses=m, original_variables=len(vs))
    def validate(A,C,values):
        X = A|nbr[C]
        assert set(values)==X
        assert 8*len(nbr[C]-A)<=13*len(C) and (not C or len(C)<8*len(A))
        assert all(any(values[abs(l)]==(l>0) for l in raw[j]) for j in C)
        for U in nbr:
            if U and not (U & C):
                assert 8*len(nbr[U]-X)>13*len(U)
                stats['residual_neighborhood_checks'] += 1
        stats['states_checked'] += 1
        stats['largest_block']=max(stats['largest_block'],len(C))
    def ask(A,C,values,x):
        if x in values:
            stats['forced_edges']+=1
            return [(values[x], A,C,dict(values))]
        X = set(values)
        A1 = A|{x}
        eligible=(U for U in nbr if C<=U and 8*len(nbr[U]-A1)<=13*len(U))
        C1=max(eligible,key=lambda U:(len(U),tuple(sorted(U))))
        add=sorted(C1-C)
        stats['absorbed_nonempty']+=bool(add)
        # Find distinct fresh satisfying variables, explicitly excluding the
        # queried one. This choice works before the adversary sees its value.
        def match(i,used,chosen):
            if i==len(add): return chosen
            for l in raw[add[i]]:
                v=abs(l)
                if v not in used:
                    answer=match(i+1,used|{v},chosen+[(v,l>0)])
                    if answer is not None:return answer
            return None
        matching=match(0,X|{x},[])
        assert matching is not None
        states=[]
        for value in (False,True):
            ext=dict.fromkeys(A1|nbr[C1],False)
            ext.update(values)
            ext.update(matching)
            ext[x]=value
            assert all(ext[k]==v for k,v in values.items())
            validate(A1,C1,ext)
            states.append((value,A1,C1,ext))
            stats['free_edges']+=1
            stats['repair_assignments']+=len(matching)
        stats['both_values_checks']+=1
        return states
    empty=frozenset()
    validate(empty,empty,{})
    # Every ordered pair of distinct queries. Then deliberately ask an already
    # fixed coordinate and a fresh coordinate depending on previous replies.
    for x in sorted(vs):
        for a,A,C,val in ask(empty,empty,{},x):
            for y in sorted(vs-{x}):
                for b,A1,C1,v1 in ask(A,C,val,y):
                    fixed=sorted(set(v1)-{x,y})
                    forced=fixed[0] if fixed else x
                    answers=ask(A1,C1,v1,forced)
                    assert len(answers)==1
                    _,A2,C2,v2=answers[0]
                    rest=sorted(vs-set(v2))
                    if rest:
                        future=rest[-1] if a != b else rest[0]
                        stats['histories']+=len(ask(A2,C2,v2,future))
    assert stats['absorbed_nonempty'] and stats['forced_edges'] and stats['largest_block']>=2
    # Two arbitrary pins can defeat a naive all-pinnings theorem even in a
    # single proper clause. The free-query strategy does not require that.
    c=raw[0]
    pins={abs(l):l<0 for l in c[:2]}
    good=[bit for bit in (False,True) if any(
        (pins|{abs(c[2]):bit})[abs(l)]==(l>0) for l in c)]
    assert good==[c[2]>0]
    return dict(schema_version=1,all_checks_passed=True,summary=stats,
                two_false_pins_force_third=True,
                scope='All ordered first/second queries and both free replies on the seven-petal satisfiable control; residual expansion checked on every disjoint subfamily. A finite audit of the strategy, not evidence of hardness of this fixture.')


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--out-dir',type=Path,required=True)
    out=parser.parse_args().out_dir
    out.mkdir(parents=True,exist_ok=True)
    r=audit()
    (out/'branch_localization.json').write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
    print(r['summary'])
