"""Choose a model map using target binary implications and its remaining interface.

Only independent raw-CNF certificate replay can authorize deletion. Component
IDs and cheap graph comparisons never enter the trusted checker.
"""
from collections import defaultdict
from .decision_labels import canonical_cnf
from .derived_transport import derive_transport


def literal_components(n,clauses):
    """SCCs of the signed binary implication graph, stable in explicit input size."""
    c=canonical_cnf(n,clauses,3)
    adj={v:[] for j in range(1,n+1) for v in (j,-j)}
    rev={v:[] for v in adj}
    for row in c:
        if len(row)==2:
            a,b=row
            for u,v in ((-a,b),(-b,a)):
                adj[u].append(v);rev[v].append(u)
    visited=set();finish=[]
    for start in adj:
        if start in visited:continue
        visited.add(start);stack=[(start,0)]
        while stack:
            u,i=stack[-1]
            if i==len(adj[u]):finish.append(u);stack.pop();continue
            v=adj[u][i];stack[-1]=(u,i+1)
            if v not in visited:visited.add(v);stack.append((v,0))
    comp={}
    for root in reversed(finish):
        if root in comp:continue
        comp[root]=root;stack=[root]
        while stack:
            u=stack.pop()
            for v in rev[u]:
                if v not in comp:comp[v]=root;stack.append(v)
    return comp


def interface_images(n,target):
    """Use external clause variables as names for otherwise movable equivalence classes."""
    c=canonical_cnf(n,target,3)
    comp=literal_components(n,c)
    if any(comp[j]==comp[-j] for j in range(1,n+1)):return None
    visible=set()
    for row in c:
        ids={comp[l] for l in row}
        if not any(comp[-l] in ids for l in row):visible.update(map(abs,row))
    groups=defaultdict(list)
    for j in range(1,n+1):groups[frozenset((comp[j],comp[-j]))].append(j)
    images=list(range(1,n+1))
    for vs in groups.values():
        names=[j for j in vs if j in visible]
        rep=min(names or vs)
        for j in vs:
            images[j-1]=rep if comp[j]==comp[rep] else -rep
    return images


def find_interface_transport(n,source,target,*,depth=0,max_nodes=None,max_queries=None):
    images=interface_images(n,target)
    r=derive_transport(n,source,target,images=images,depth=depth,max_nodes=max_nodes,
                       max_queries=max_queries,strategies=())
    if r['certificate'] is not None:r['certificate']['method']='interface-rup'
    return r
