"""Explicit sibling restrictions for directed Boolean witness transport."""


def _width3(n, clauses):
    if type(n) is not int or n<0:
        raise ValueError("expected a nonnegative variable count")
    rows=tuple(tuple(c) for c in clauses)
    if any(len(c)>3 or any(type(v) is not int or not 1<=abs(v)<=n for v in c) for c in rows):
        raise ValueError("expected width at most three on the stated variables")
    return rows


def directed_tags(k, core=(), *, shield=True):
    """Source IDs: tags 1..k, a and z in next two consecutive k-bit blocks.
    Core input uses local IDs 1..k for its a variables. Shield is conservative.
    """
    if type(k) is not int or k<1 or type(shield) is not bool:raise ValueError("bad parameters")
    rows=[tuple((1 if v>0 else -1)*(k+abs(v)) for v in c) for c in _width3(k,core)]
    n=3*k
    for j in range(1,k+1):
        t,a,z=j,k+j,2*k+j
        rows.extend(((t,a,z),(-t,-a,z),(-t,a,-z)))
        if shield:
            p,q=n+1,n+2
            n+=2
            rows.extend(((z,p,q),(-z,-p,-q)))
    if shield:
        # Exact equality triangles are closed under complementing the whole triangle.
        for v in range(k+1,n+1):
            p,q=n+1,n+2
            n+=2
            for u,w in ((v,p),(p,q),(q,v)):rows.extend(((-u,w),(u,-w)))
    return n, tuple(rows)


def cycle_core(k):
    """Not-all-equal windows; every even k>=4 allows the alternating word."""
    if type(k) is not int or k<3:raise ValueError("need at least three core variables")
    rows=[]
    for i in range(k):
        c=tuple(1+(i+j)%k for j in range(3))
        rows.extend((c,tuple(-v for v in c)))
    return tuple(rows)


def flip_hard_siblings(n, clauses):
    """SAT <= existence of one certified diagonal flip between sibling residuals.

    ID 1 is the tag, 2 through n+1 the source variables. In the tag=1
    branch all non-tag bits must be zero. Fresh variables have one occurrence
    on each side of their split long clause and one pin.
    """
    rows=_width3(n, clauses)
    mx=n+1
    out=[]
    for row in rows:
        shifted=tuple((1 if v>0 else -1)*(1+abs(v)) for v in row)
        if len(row)<=2:
            out.append((1,*shifted))
        else:
            mx+=1
            x,y,z=shifted
            out.extend(((1,x,mx),(-mx,y,z)))
    out.extend((-1,-v) for v in range(2,mx+1))
    return mx,tuple(out)


def coherent(word, clauses):
    return all(any(bool(word>>(abs(v)-1)&1)==(v>0) for v in c) for c in clauses)
