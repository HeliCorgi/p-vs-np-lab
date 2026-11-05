"""Exact order-four signed-integer marginal audit on the subdivided K4 switch.

The generator is known to this verifier. It checks finite tables, not a
procedure to discover the graph, and not a proof for arbitrary expanders.
"""
import argparse
from collections import defaultdict
from itertools import combinations, product
import json
from math import comb
from pathlib import Path

from pnp_lab.field_split import check_field_split, field_split_refute, switch_flow


def giant(vertices, edges, deleted):
    adj=[[] for _ in range(vertices)]
    for i,(u,v) in enumerate(edges):
        if i not in deleted:
            adj[u].append(v)
            adj[v].append(u)
    left=set(range(vertices))
    sizes=[]
    largest=()
    while left:
        root=min(left)
        left.remove(root)
        part=[root]
        for u in part:
            for v in adj[u]:
                if v in left:
                    left.remove(v)
                    part.append(v)
        sizes.append(len(part))
        if 2*len(part)>vertices:
            largest=tuple(sorted(part))
    return largest,sorted(sizes,reverse=True)


def catalogue(edges, p):
    # Exhaust the seven edge labels rather than use an algebraic rank
    # argument. The index is the full vertex divergence vector.
    valid=defaultdict(list)
    for vals in product(range(p), repeat=len(edges)):
        charge=[0]*5
        for (u,v),a in zip(edges,vals):
            charge[u]+=a
            charge[v]-=a
        valid[tuple(x%p for x in charge)].append(vals)
    return valid


def run():
    k=4
    graph=tuple(combinations(range(4),2))
    u,v=graph[0]
    edges=((u,4),(4,v))+graph[1:]
    E=len(edges)
    n,cs,_=switch_flow(graph,4)
    assert n==1+4*E==29
    refute=field_split_refute(n,cs)
    assert refute['status']=='UNSAT' and check_field_split(n,cs,refute['certificate'])
    giants={}
    for d in range(k+1):
        for x in combinations(range(E),d):
            g,sizes=giant(5,edges,frozenset(x))
            assert g and 2*len(g)>5
            giants[frozenset(x)]=g
    lack=next((x,sizes) for x in combinations(range(E),5)
              for g,sizes in [giant(5,edges,frozenset(x))] if not g)
    catalog={p:catalogue(edges,p) for p in (2,3)}
    # sigma=0: mod-2 bank active, inactive mod-3 bank has a zero flow.
    # sigma=1: mod-3 active, mod-2 demands 1 at both vertex 0 and port 4.
    inactive={0:(0,)*E,1:catalog[2][(1,0,0,0,1)][0]}

    def boolean_word(s,bits,trits):
        return (s | sum(bit<<(1+i) for i,bit in enumerate(bits)) |
                sum(1<<(1+E+3*i+t) for i,t in enumerate(trits)))

    active_words={}
    for sigma,p in ((0,2),(1,3)):
        for r in range(5):
            demand=([1,0,0,0,0] if sigma==0 else [0,0,0,0,1])
            demand[r]=(demand[r]-1)%p
            flows=catalog[p][tuple(demand)]
            assert len(flows)==p**3
            active_words[sigma,r]=tuple(boolean_word(sigma,
                vals if sigma==0 else inactive[1], inactive[0] if sigma==0 else vals)
                for vals in flows)

    # A single globally fixed defect does not work: at least one raw
    # clause is violated where the defect has landed.
    bad_word=active_words[0,0][0]
    failed=next(i for i,c in enumerate(cs) if not any(bool(bad_word>>(abs(l)-1)&1)==(l>0) for l in c))
    # Store rational branch tables as counts scaled by p^k; signed tables
    # then consist entirely of Python integers. Only levels <k are cached.
    data={}
    coefficients=(-5,1)
    scales=(2**k,3**k)
    assert sum(a*b for a,b in zip(coefficients,scales))==1
    raw=defaultdict(list)
    for c in cs:
        raw[tuple(sorted(map(abs,c)))].append(c)
    stats=dict(scopes=0,cells=0,branch_word_projections=0,projection_equalities=0,
               raw_zero_mass_cells=0,negative_cells=0,positive_cells=0,
               zero_cells=0,min_signed=0,max_signed=0,minimum_giant_vertices=5)
    selector_mass=None
    for width in range(k+1):
        for S in combinations(range(1,n+1),width):
            powers=(1<<width)
            stats['scopes']+=1
            stats['cells']+=powers
            # Connect one-hot coordinates to their underlying field edge.
            xs=(frozenset(v-2 for v in S if 2<=v<=E+1),
                frozenset((v-E-2)//3 for v in S if v>=E+2))
            tables=[]
            for sigma,p in ((0,2),(1,3)):
                g=giants[xs[sigma]]
                stats['minimum_giant_vertices']=min(stats['minimum_giant_vertices'],len(g))
                words=active_words[sigma,g[0]]
                counts=[0]*powers
                for w in words:
                    word=sum(((w>>(v-1))&1)<<j for j,v in enumerate(S))
                    counts[word]+=1
                stats['branch_word_projections']+=len(words)
                assert all((c*p**k)%len(words)==0 for c in counts)
                row=tuple(c*p**k//len(words) for c in counts)
                assert sum(row)==p**k and min(row)>=0
                tables.append(row)
            signed=tuple(coefficients[0]*a+coefficients[1]*b for a,b in zip(*tables))
            assert sum(signed)==1
            tables.append(signed)
            stats['min_signed']=min(stats['min_signed'],min(signed))
            stats['max_signed']=max(stats['max_signed'],max(signed))
            stats['negative_cells']+=sum(c<0 for c in signed)
            stats['positive_cells']+=sum(c>0 for c in signed)
            stats['zero_cells']+=signed.count(0)
            if S==(1,):
                selector_mass=signed
                assert signed==(-80,81)
            # Verify every raw constraint wholly in this scope even for
            # the two component tables: there is no cancellation loophole.
            pos={v:j for j,v in enumerate(S)}
            for size in (2,3):
                for sub in combinations(S,size):
                    for c in raw.get(sub,()):
                        wrong=sum(1<<pos[abs(l)] for l in c if l<0)
                        mask=sum(1<<pos[v] for v in sub)
                        for w in range(powers):
                            if w&mask==wrong:
                                assert all(t[w]==0 for t in tables)
                                stats['raw_zero_mass_cells']+=1
            for j in range(width):
                small=data[S[:j]+S[j+1:]]
                for w in range(powers//2):
                    zero=((w>>j)<<(j+1)) | (w&((1<<j)-1))
                    one=zero|(1<<j)
                    for big,little in zip(tables,small):
                        assert big[zero]+big[one]==little[w]
                        stats['projection_equalities']+=1
            if width<k:
                data[S]=tuple(tables)
    assert stats['scopes']==sum(comb(n,t) for t in range(k+1))
    assert stats['projection_equalities']==3*sum(comb(n,t)*t*(1<<(t-1)) for t in range(1,k+1))
    return dict(all_checks_passed=True,level=k,variables=n,clauses=len(cs),oriented_edges=edges,
                branch_scales=scales,bezout_weights=coefficients,selector_integer_masses=selector_mass,
                edge_sets_with_giant=len(giants),missing_giant_at_five=dict(deleted=lack[0],parts=lack[1]),
                fixed_defect_negative_control=dict(sigma=0,defect=0,raw_word=bad_word,
                                                   violated_clause_id=failed,clause=cs[failed]),
                raw_refutation_checked=True,stats=stats,
                summary=dict(level=k,variables=n,checked_scopes=stats['scopes'],table_cells=stats['cells'],
                             checked_projection_equalities=stats['projection_equalities'],
                             negative_integer_cells=stats['negative_cells'],
                             selector_masses=selector_mass,edge_sets_with_giant=len(giants),
                             minimum_giant_vertices=stats['minimum_giant_vertices']),
                scope='All scope tables through order four on one 29-variable UNSAT switch. Signed integer marginals, not probabilities or a Boolean assignment. No general expansion lower bound inferred from this example. Missing giant for five deleted edges is a failure of this construction criterion, not a level-five infeasibility proof.')


if __name__=='__main__':
    cli=argparse.ArgumentParser()
    cli.add_argument('--out-dir',type=Path,required=True)
    out=cli.parse_args().out_dir
    out.mkdir(parents=True,exist_ok=True)
    report=run()
    (out/'coprime_marginals.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n')
    print(report['summary'])
