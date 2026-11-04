"""Four Boolean ports shared between a binary-prime and a ternary-prime bank."""
from .ternary_flow import prism_edges,_encode,_solve_flow,_word


def four_port_flow(k,*,binary_rhs=1,ternary_rhs=2):
    if type(k) is not int or k<4:raise ValueError('four distinct rung positions required')
    if type(binary_rhs) is not int or binary_rhs not in (0,1) or type(ternary_rhs) is not int or ternary_rhs not in (0,1,2):raise ValueError('bad charge')
    rows=[];pv=tuple(range(2*k,2*k+4))
    for i,(a,b) in enumerate(prism_edges(k)):
        if 2*k<=i<2*k+4:rows.extend(((a,pv[i-2*k]),(pv[i-2*k],b)))
        else:rows.append((a,b))
    ports=(1,2,3,4);port_map=dict(zip(pv,ports))
    q=[0]*(2*k+4);q[0]=(-binary_rhs)%2
    n2,f=_encode(rows,q,2,4,port_map)
    q[0]=(-ternary_rhs)%3
    n,g=_encode(rows,q,3,n2,port_map)
    return n,f+g,dict(edges=rows,pv=pv,n2=n2)


def four_port_word(k,bits,*,binary_rhs=1,ternary_rhs=2):
    if len(bits)!=4 or any(type(b) is not int or b not in (0,1) for b in bits):raise ValueError('bad ports')
    n,cs,m=four_port_flow(k,binary_rhs=binary_rhs,ternary_rhs=ternary_rhs)
    x=sum(b<<j for j,b in enumerate(bits))
    for p,r,offset in ((2,binary_rhs,4),(3,ternary_rhs,m['n2'])):
        q=[0]*(2*k+4);q[0]=(-r)%p
        for v,b in zip(m['pv'],bits):q[v]=b
        w=_solve_flow(m['edges'],q,p)
        if w is None:return None
        x|=_word(w,p,offset)
    return x


def alternating_flow(k,*,total=1):
    """Five 3-port and five 4-port banks feed one 5-port bank.

    The F3 triplet in each group enforces weight two. Binary parity of that
    triplet and its terminal then forces the terminal to zero. The 5-port
    ternary bank checks the sum of the five terminals. No selector names or
    equations are provided to a solver.
    """
    if type(k) is not int or k<5 or type(total) is not int or total not in (0,1,2):
        raise ValueError('invalid alternating network')
    n=20;out=[];word=sum(1<<(3*j+i) for j in range(5) for i in (0,1))
    def bank(ports,prime,rhs):
        nonlocal n,word
        old=n;m=len(ports);es=[];pv=tuple(range(2*k,2*k+m))
        for j,(a,b) in enumerate(prism_edges(k)):
            if 2*k<=j<2*k+m:es.extend(((a,pv[j-2*k]),(pv[j-2*k],b)))
            else:es.append((a,b))
        q=[0]*(2*k+m);q[0]=(-rhs)%prime
        n,cs=_encode(es,q,prime,old,dict(zip(pv,ports)));out.extend(cs)
        for v,b in zip(pv,ports):q[v]=word>>(b-1)&1
        ws=_solve_flow(es,q,prime)
        if ws is not None:word|=_word(ws,prime,old)
    for j in range(5):
        xyz=tuple(range(3*j+1,3*j+4))
        bank(xyz,3,2);bank(xyz+(16+j,),2,0)
    bank(tuple(range(16,21)),3,total)
    return n,tuple(out),word if total==0 else None
