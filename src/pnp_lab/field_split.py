"""One Boolean case split, with a separately checked prime-field sum per side."""
from .integer_probe import _restrict
from .modular_hull import _input, modular_hull_refute, check_modular_hull
from .ternary_flow import _encode

KIND = 'one-split-two-fields-v1'


def switch_flow(edges, vertices, *, satisfiable=False):
    """Fixture only. No graph, ports, selector or charge is passed to discovery.

    Subdivide the first edge, giving the same selector one degree-two port
    in each of two disjoint flow banks. For the satisfiable control both
    banks have zero charge at selector zero.
    """
    edges = tuple(tuple(e) for e in edges)
    if (type(vertices) is not int or vertices < 4 or type(satisfiable) is not bool
            or not edges or any(len(e)!=2 or e[0]==e[1] or any(
                type(v) is not int or not 0<=v<vertices for v in e) for e in edges)
            or len({tuple(sorted(e)) for e in edges})!=len(edges)):
        raise ValueError('expected a simple cubic graph')
    deg = [0]*vertices
    for a,b in edges:
        deg[a]+=1
        deg[b]+=1
    if any(d!=3 for d in deg):
        raise ValueError('expected cubic graph')
    adj=[[] for _ in deg]
    for a,b in edges:
        adj[a].append(b)
        adj[b].append(a)
    seen={0}
    queue=[0]
    for a in queue:
        for b in adj[a]:
            if b not in seen:
                seen.add(b)
                queue.append(b)
    if len(seen)!=vertices:
        raise ValueError('expected a connected graph')
    u,v = edges[0]
    ed = ((u,vertices),(vertices,v))+edges[1:]
    port = {vertices:1}
    q = [0]*(vertices+1)
    q[0] = int(not satisfiable)
    n2, f = _encode(ed,q,2,offset=1,ports=port)
    n, g = _encode(ed,[0]*(vertices+1),3,offset=n2,ports=port)
    word = (sum(1<<(n2+3*i) for i in range(len(ed))) if satisfiable else None)
    return n,f+g,word


def _cut_candidates(cs):
    """Occurrence labels only. A separator is a heuristic, never a checked premise.

    Count connected components before and after deletion. Do not try all
    valuations of a disconnected or nonseparating variable.
    """
    adj={}
    for c in cs:
        vs={abs(x) for x in c}
        for x in vs:
            adj.setdefault(x,set()).update(vs-{x})
    def components(skip):
        left=set(adj)
        left.discard(skip)
        sizes=[]
        while left:
            todo=[left.pop()]
            size=0
            while todo:
                x=todo.pop()
                size+=1
                for y in adj[x]:
                    if y in left:
                        left.remove(y)
                        todo.append(y)
            sizes.append(size)
        return sorted(sizes,reverse=True)
    base=len(components(None))
    candidates=[]
    for x in sorted(adj):
        c=components(x)
        if len(c)>base:
            candidates.append((-c[1],x))
    return [x for _,x in sorted(candidates)]


def check_field_split(n,clauses,cert):
    """Reconstruct both restrictions directly, then replay their field sums."""
    try:
        cs=_input(n,clauses)
        if (not isinstance(cert,dict) or set(cert)!={'kind','selector','branches'}
                or cert['kind']!=KIND or type(cert['selector']) is not int
                or not 1<=cert['selector']<=n or not isinstance(cert['branches'],list)
                or len(cert['branches'])!=2):
            return False
        v=cert['selector']
        for val,proof in enumerate(cert['branches']):
            residual=[]
            for row in cs:
                if any(abs(l)==v and (l>0)==bool(val) for l in row):
                    continue
                residual.append(tuple(l for l in row if abs(l)!=v))
            if not check_modular_hull(n,residual,proof):
                return False
        return True
    except (TypeError, ValueError, IndexError, KeyError, AttributeError):
        return False


def field_split_refute(n,clauses,*,max_candidates=32,max_scopes=None):
    if any(k is not None and (type(k) is not int or k<0) for k in (max_candidates,max_scopes)):
        raise ValueError('invalid budget')
    cs=_input(n,clauses)
    candidates=_cut_candidates(cs)
    stats=dict(candidates=len(candidates),tried=0,field_calls=0,scopes_examined=0,
               local_assignments=0,budget_limited=False)
    for v in candidates:
        if max_candidates is not None and stats['tried']>=max_candidates:
            stats['budget_limited']=True
            break
        stats['tried']+=1
        branches=[]
        for l in (-v,v):
            rows=_restrict(cs,(l,))
            for p in (2,3):
                result=modular_hull_refute(n,rows,prime=p,max_scopes=max_scopes)
                stats['field_calls']+=1
                stats['scopes_examined']+=result['stats']['scopes_examined']
                stats['local_assignments']+=result['stats']['local_assignments']
                stats['budget_limited'] |= result['stats']['budget_limited']
                if result['status']=='UNSAT':
                    branches.append(result['certificate'])
                    break
            else:
                break
        if len(branches)==2:
            cert=dict(kind=KIND,selector=v,branches=branches)
            if not check_field_split(n,cs,cert):
                raise AssertionError('split failed original-CNF replay')
            return dict(status='UNSAT',certificate=cert,stats=stats)
    return dict(status='UNKNOWN',certificate=None,stats=stats)
