"""Share short consequences between F2 and F3, checking all casts on Boolean words.

Unlike adding equations with different moduli, every change of field carries a
semantic implication valid on the indicated Boolean cube. Width bounds the
support of a bridge, not the support of Gaussian intermediate consequences.
"""
from bisect import bisect_right
from collections import defaultdict
from functools import lru_cache
from .modular_hull import _input, collect_modular_rows, check_modular_row, _annihilator

KIND='boolean-field-bridge-v1'


def _add(d,m,e,p):
    for j,c in e.items():
        v=(d.get(j,0)+m*c)%p
        if v:d[j]=v
        else:d.pop(j,None)


def _eq_args(n,pairs,p):
    if type(pairs) is not list:raise ValueError
    d={}
    for j,a in pairs:
        if type(j) is not int or type(a) is not int or not 1<=j<=n or not 1<=a<p or j in d:raise ValueError
        d[j]=a
    return d


def _as_node(op,p,row,b,**data):
    return dict(op=op,p=p,row=[list(t) for t in sorted(row.items())],rhs=b,**data)


def check_field_bridge(n,clauses,cert):
    """Replay a topologically ordered proof; do not run discovery or row reduction."""
    try:
        cs=_input(n,clauses)
        if not isinstance(cert,dict) or cert.get('kind')!=KIND:return False
        nodes=cert['nodes']
        if type(nodes) is not list or not nodes:return False
        done=[]
        def parent(i):
            if type(i) is not int or not 0<=i<len(done):raise ValueError
            return done[i]
        for node in nodes:
            p=node['p'];b=node['rhs']
            if type(p) is not int or p not in (2,3) or type(b) is not int or not 0<=b<p:return False
            d=_eq_args(n,node['row'],p);op=node['op']
            if op=='local':
                t=node['evidence']
                if not check_modular_row(n,cs,p,t):return False
                if {v:c for v,c in zip(t['scope'],t['coeff']) if c}!=d or t['rhs']!=b:return False
            elif op=='sum':
                rr={};bb=0
                if type(node['terms']) is not list or not node['terms']:return False
                for j,m in node['terms']:
                    pp,v,a=parent(j)
                    if pp!=p or type(m) is not int or not 1<=m<p:return False
                    for var,c in v.items():rr[var]=(rr.get(var,0)+m*c)%p
                    bb=(bb+m*a)%p
                if {v:a for v,a in rr.items() if a}!=d or b!=bb:return False
            elif op=='boolean':
                pp,old,bb=parent(node['from'])
                if pp==p or len(old)>4 or not d.keys()<=old.keys():return False
                keys=tuple(old)
                for w in range(1<<len(keys)):
                    if (sum(old[v] for j,v in enumerate(keys) if w>>j&1)%pp==bb and
                        sum(d.get(v,0) for j,v in enumerate(keys) if w>>j&1)%p!=b):return False
            else:return False
            done.append((p,d,b))
        return done[-1][1]=={} and done[-1][2]==1
    except (TypeError,KeyError,IndexError,ValueError,AttributeError):return False


def _trim(nodes):
    todo=[len(nodes)-1];used=set(todo)
    while todo:
        node=nodes[todo.pop()]
        ids=[j for j,_ in node['terms']] if node['op']=='sum' else [node['from']] if node['op']=='boolean' else []
        for ix in ids:
            if ix not in used:used.add(ix);todo.append(ix)
    order=sorted(used);ix={j:i for i,j in enumerate(order)};out=[]
    for j in order:
        node=nodes[j].copy()
        if node['op']=='sum':node['terms']=[[ix[k],a] for k,a in node['terms']]
        if node['op']=='boolean':node['from']=ix[node['from']]
        out.append(node)
    return dict(kind=KIND,nodes=out)


class _Space:
    def __init__(self,n,p,nodes):
        self.n,self.p,self.nodes=n,p,nodes;self.basis={}

    def reduce(self,d,b):
        # Return residue and a combination of stored raw proof nodes:
        # (d,b) = (residue,c) + combo.
        r=d.copy();c=b;comb={}
        while r:
            v=min(r)
            if v not in self.basis:break
            row,rhs,ids=self.basis[v];a=r[v]
            _add(r,-a,row,self.p);c=(c-a*rhs)%self.p;_add(comb,a,ids,self.p)
        return r,c,comb

    def insert(self,residue,nodeid):
        r,c,comb=residue;p=self.p
        if not r and not c:return False
        ids={j:(-a)%p for j,a in comb.items()};ids[nodeid]=1
        scale=pow(r[min(r)] if r else c,-1,p)
        ids={j:a*scale%p for j,a in ids.items()}
        if not r:
            self.nodes.append(_as_node('sum',p,{},1,terms=sorted(ids.items())))
            return True
        self.basis[min(r)]=({v:a*scale%p for v,a in r.items()},c*scale%p,ids)
        return False

    def proof(self,d,b):
        r,c,comb=self.reduce(d,b)
        if r or c:raise AssertionError('uncertified small row')
        if len(comb)==1:
            j,a=next(iter(comb.items()))
            if a==1:return j
        self.nodes.append(_as_node('sum',self.p,d,b,terms=sorted(comb.items())))
        return len(self.nodes)-1

    def coordinates(self):
        # x_v = offset + a signed vector on free coordinates, stored as a
        # pair of bit sets (coefficients 1,2). Coordinates descend by pivot.
        sig={};offset={}
        active={j for row,_,_ in self.basis.values() for j in row}
        for v in sorted(active,reverse=True):
            if v not in self.basis:sig[v]=(1<<(v-1),0);offset[v]=0;continue
            row,t,_=self.basis[v];s=(0,0)
            for j,c in row.items():
                if j==v:continue
                s=_plus(s,_times(sig[j],(-c)%self.p),self.p)
                t=(t-c*offset[j])%self.p
            sig[v]=s;offset[v]=t
        return sig,offset


def _times(s,a):
    return s[::-1] if a==2 else s  # a is a nonzero field element


def _plus(a,b,p):
    if p==2:return a[0]^b[0],0
    x,y=a;u,v=b;z=~(x|y);w=~(u|v)
    return (z&u)|(x&w)|(y&v),(z&v)|(y&w)|(x&u)


def _sparse(space,width,charge=lambda:None):
    # Enumerate every nonzero normal of support <= width, modulo scaling.
    # Use a free-coordinate signature dictionary instead of testing n^3 triples.
    p=space.p;sig,off=space.coordinates();bins=defaultdict(list)
    active=sorted(sig)
    for i in active:bins[sig[i]].append(i)
    pair_bins=defaultdict(list)
    if width==4 and p==3:
        for ki,k in enumerate(active):
            for l in active[ki+1:]:
                for t in (1,2):
                    charge()
                    v=_plus(sig[k],_times(sig[l],t),p)
                    pair_bins[v].append((k,l,t))
    for ii,i in enumerate(active):
        charge();s=sig[i]
        if s==(0,0):yield {i:1},off[i]
        if width<2:continue
        for a in range(1,p):
            charge();js=bins.get(_times(s,(-pow(a,-1,p))%p),[])
            for t in range(bisect_right(js,i),len(js)):
                j=js[t];yield {i:1,j:a},(off[i]+a*off[j])%p
        # The Boolean hull of a ternary F2 parity is full over F3: it
        # contributes no row to the other field, whichever RHS is used.
        if width<3 or p==2:continue
        for j in active[ii+1:]:
            for a in range(1,p):
                t=_plus(s,_times(sig[j],a),p)
                for b in range(1,p):
                    charge();ks=bins.get(_times(t,(-pow(b,-1,p))%p),[])
                    for h in range(bisect_right(ks,j),len(ks)):
                        k=ks[h];yield {i:1,j:a,k:b},(off[i]+a*off[j]+b*off[k])%p
                    if width==4:
                        # k,l,t represent the normalized tail x_k+t*x_l.
                        charge();hits=pair_bins.get(_times(t,(-pow(b,-1,p))%p),[])
                        z=bisect_right(hits,(j,space.n+1,3))
                        for index in range(z,len(hits)):
                            k,l,h=hits[index];c=b*h%p
                            yield {i:1,j:a,k:b,l:c},(off[i]+a*off[j]+b*off[k]+c*off[l])%p


@lru_cache(maxsize=256)
def _casts(coeff,b,p):
    q=5-p;w=len(coeff);bits=0
    for a in range(1<<w):
        if sum(c for j,c in enumerate(coeff) if a>>j&1)%p==b:bits|=1<<a
    return tuple(_annihilator(bits,w,q))


class _Cap(Exception):pass


def mixed_modular_refute(n,clauses,*,bridge_width=3,max_short_rows=None,max_probes=None):
    if type(bridge_width) is not int or not 0<=bridge_width<=4:raise ValueError('bridge_width must be 0..4')
    if any(v is not None and (type(v) is not int or v<0) for v in (max_short_rows,max_probes)):raise ValueError('bad bridge budget')
    cs=_input(n,clauses);nodes=[];spaces={p:_Space(n,p,nodes) for p in (2,3)}
    stats=dict(local={},rounds=0,signature_probes=0,short_rows_checked=0,new_transfers=0,budget_limited=False,
               transfer_widths={},final_ranks={})
    def result(ok):
        stats['final_ranks']={str(p):len(v.basis) for p,v in spaces.items()}
        cert=_trim(nodes) if ok else None
        if ok and not check_field_bridge(n,cs,cert):raise AssertionError('invalid modular bridge')
        return dict(status='UNSAT' if ok else 'UNKNOWN',certificate=cert,stats=stats)
    for p,space in spaces.items():
        rows,st=collect_modular_rows(n,cs,prime=p);stats['local'][str(p)]=st
        for leaf in rows:
            d={v:c for v,c in zip(leaf['scope'],leaf['coeff']) if c};b=leaf['rhs']
            res=space.reduce(d,b)
            if res[0] or res[1]:
                nodeid=len(nodes);nodes.append(_as_node('local',p,d,b,evidence=leaf))
                if space.insert(res,nodeid):return result(True)
    if not bridge_width:return result(False)
    def charge():
        if max_probes is not None and stats['signature_probes']>=max_probes:raise _Cap
        stats['signature_probes']+=1
    try:
        while True:
            stats['rounds']+=1;changed=False
            for p in (2,3):
                q=5-p;src,dst=spaces[p],spaces[q]
                for d,b in _sparse(src,bridge_width,charge):
                    if max_short_rows is not None and stats['short_rows_checked']>=max_short_rows:
                        stats['budget_limited']=True;return result(False)
                    stats['short_rows_checked']+=1;parent=None;keys=tuple(d)
                    for eq in _casts(tuple(d.values()),b,p):
                        rr={v:c for v,c in zip(keys,eq) if c};cc=eq[-1]
                        res=dst.reduce(rr,cc)
                        if not res[0] and not res[1]:continue
                        if parent is None:parent=src.proof(d,b)
                        ix=len(nodes);nodes.append(_as_node('boolean',q,rr,cc,**{'from':parent}))
                        stats['new_transfers']+=1;tag=f'{p}->{q}:{len(keys)}'
                        stats['transfer_widths'][tag]=1+stats['transfer_widths'].get(tag,0)
                        if dst.insert(res,ix):return result(True)
                        changed=True
            if not changed:return result(False)
    except _Cap:
        stats['budget_limited']=True
        return result(False)
