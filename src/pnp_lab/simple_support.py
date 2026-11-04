"""Decision reduction to proper 3-CNF with at most one clause per unsigned triple."""

# Six bits, eleven clauses. Independently checked over all 64 inputs. Removing
# the first clause leaves a satisfiable CNF forcing bits 4,5,6 to true.
GADGET=((-4,-5,-6),(-3,4,-6),(-2,-4,5),(2,3,5),(-3,-5,6),(2,-3,-4),
        (-1,4,5),(1,-2,3),(-1,3,-5),(1,-3,4),(1,2,-5))


def simple_support_image(n,clauses):
    if type(n) is not int or n<0:raise ValueError('expected explicit nonnegative scope')
    out=list(GADGET[1:])
    occur=[[] for _ in range(n)]
    next_id=7
    for raw in clauses:
        c=tuple(raw)
        if len(c)>3 or any(type(l) is not int or not 1<=abs(l)<=n for l in c):
            raise ValueError('invalid width or literal')
        if any(-l in c for l in c):continue
        c=tuple(dict.fromkeys(c))
        if not c:
            if GADGET[0] not in out:out.append(GADGET[0])
            continue
        copy=[]
        for lit in c:
            occur[abs(lit)-1].append(next_id)
            copy.append(next_id if lit>0 else -next_id)
            next_id+=1
        extra={1:(-4,-6),2:(-6,),3:()}[len(copy)]
        out.append(tuple(copy)+extra)
    for vs in occur:
        if len(vs)>=2:
            for j,a in enumerate(vs):
                # Two reverse edges on the same pair need different padding.
                false_bit=5 if len(vs)==2 and j==1 else 4
                out.append((-a,vs[(j+1)%len(vs)],-false_bit))
    # One existentially free extension also prevents the last forcing bit
    # from being an eligible single-pair resolution pivot on every image.
    out.append((-6,next_id,next_id+1))
    return next_id+1,tuple(out),tuple(tuple(vs) for vs in occur)


def forcing_models():
    return [x for x in range(64) if all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in c) for c in GADGET[1:])]
