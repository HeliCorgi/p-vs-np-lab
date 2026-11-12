#!/usr/bin/env python3
"""An ordinary-resolution refutation of a double copy of ANY specified mixed-gate DAG.

Only syntax-level Tseitin clauses and strict two-parent resolution are used.
This experiment is limited to explicitly given AND/OR/XOR/NOT DAGs; the
refutation does not decide an arbitrary CNF.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import random
from pathlib import Path


OPS = {"AND": 2, "OR": 2, "XOR": 2, "NOT": 1}
COST = {"AND": 8, "OR": 8, "XOR": 14, "NOT": 4}
CLAUSES = {"AND": 3, "OR": 3, "XOR": 4, "NOT": 2}


def normal(clause):
    s = set(clause)
    if not s or 0 in s or any(-v in s for v in s):
        raise ValueError("empty, zero-literal, or tautological source clause")
    return tuple(sorted(s, key=lambda v: (abs(v), v < 0)))


def validate(n, gates):
    if not isinstance(n, int) or n < 2 or not gates:
        raise ValueError("need at least two inputs and one gate")
    for i, (op, args) in enumerate(gates):
        if op not in OPS or len(args) != OPS[op]:
            raise ValueError("unknown gate or arity")
        if any(not isinstance(a, int) or not 1 <= a <= n+i for a in args):
            raise ValueError("forward or out-of-range wire")
        if len(args) == 2 and args[0] == args[1]:
            raise ValueError("binary gates must use distinct input wires")


def wire(n, g, original, side):
    return original if original <= n else original + (g if side == 1 else 0)


def gate_clauses(op, inputs, out):
    if op == "NOT":
        (a,) = inputs
        return ((out, a), (-out, -a))
    a,b = inputs
    if op == "AND":
        return ((-out, a), (-out, b), (out, -a, -b))
    if op == "OR":
        return ((out, -a), (out, -b), (-out, a, b))
    if op == "XOR":
        return ((a, b, -out), (a, -b, out), (-a, b, out), (-a, -b, -out))
    raise ValueError(op)


def miter(n, gates):
    """Return all and only definitional gates plus opposing output units."""
    validate(n, gates)
    g=len(gates)
    axioms=[]
    for side in (0,1):
        for i,(op,args) in enumerate(gates):
            input_wires = tuple(wire(n,g,w,side) for w in args)
            out=wire(n,g,n+i+1,side)
            axioms.extend(normal(c) for c in gate_clauses(op,input_wires,out))
    axioms.extend((normal((n+g,)), normal((-(n+2*g),))))
    assert len(axioms)==2*sum(CLAUSES[op] for op,_ in gates)+2
    return n+2*g, tuple(axioms)


def certificate(n, gates):
    """A bounded-width, exactly two-parent resolution proof without search."""
    nvars, axioms=miter(n,gates)
    g=len(gates)
    lines=list(axioms)
    ids={c:j for j,c in enumerate(axioms)}
    steps=[]
    equal={}

    def source(c):
        return ids[normal(c)]

    def resolution(left,right,pivot):
        lhs,rhs=set(lines[left]),set(lines[right])
        if pivot not in lhs or -pivot not in rhs:
            raise AssertionError("invalid generator pivot")
        c=(lhs-{pivot}) | (rhs-{-pivot})
        if any(-x in c for x in c) or len(c)>3:
            raise AssertionError("invalid generator resolvent")
        out=tuple(sorted(c,key=lambda v:(abs(v),v<0)))
        steps.append({"left":left,"right":right,"pivot":pivot,"clause":list(out)})
        lines.append(out)
        return len(lines)-1

    def rename_second(clause, original_inputs):
        """Convert occurrences of B-copy predecessor gates to A by prior equality."""
        current=source(clause)
        for w in original_inputs:
            a,b=wire(n,g,w,0),wire(n,g,w,1)
            if a==b:
                continue
            signed=b if b in lines[current] else -b
            assert signed in lines[current]
            ab,ba=equal[(a,b)]
            link=ba if signed>0 else ab
            current=resolution(current,link,signed)
        return current

    for i,(op,args) in enumerate(gates):
        aout,bout=n+i+1,n+g+i+1
        aa=tuple(wire(n,g,w,0) for w in args)
        bb=tuple(wire(n,g,w,1) for w in args)
        if op=="AND":
            a,b=aa; ap,bp=bb
            bl=rename_second((bout,-ap,-bp),args)
            q=resolution(source((-aout,a)),bl,a)
            ab=resolution(q,source((-aout,b)),-b)
            s1=rename_second((-bout,ap), (args[0],))
            s2=rename_second((-bout,bp), (args[1],))
            q=resolution(s1,source((aout,-a,-b)),a)
            ba=resolution(q,s2,-b)
        elif op=="OR":
            a,b=aa; ap,bp=bb
            s1=rename_second((bout,-ap),(args[0],))
            s2=rename_second((bout,-bp),(args[1],))
            q=resolution(source((-aout,a,b)),s1,a)
            ab=resolution(q,s2,b)
            bl=rename_second((-bout,ap,bp),args)
            q=resolution(bl,source((aout,-a)),a)
            ba=resolution(q,source((aout,-b)),b)
        elif op=="NOT":
            (a,)=aa; (ap,)=bb
            pos=rename_second((bout,ap),args)
            neg=rename_second((-bout,-ap),args)
            ab=resolution(source((-aout,-a)),pos,-a)
            ba=resolution(source((aout,a)),neg,a)
        elif op=="XOR":
            a,b=aa; ap,bp=bb
            A=[source(c) for c in gate_clauses("XOR",aa,aout)]
            B=[rename_second(c,args) for c in gate_clauses("XOR",bb,bout)]
            q0=resolution(A[0],B[1],b)
            q1=resolution(B[2],A[3],b)
            ab=resolution(q0,q1,a)
            q0=resolution(B[0],A[1],b)
            q1=resolution(A[2],B[3],b)
            ba=resolution(q0,q1,a)
        assert lines[ab]==normal((-aout,bout)), (op,lines[ab],aout,bout)
        assert lines[ba]==normal((aout,-bout)), (op,lines[ba],aout,bout)
        equal[(aout,bout)]=(ab,ba)

    q=resolution(source((n+g,)),equal[(n+g,n+2*g)][0],n+g)
    resolution(q,source((-(n+2*g),)),n+2*g)
    assert lines[-1]==()
    assert len(steps)<=2+sum(COST[op] for op,_ in gates)
    return {"variables":nvars,"axioms":[list(x) for x in axioms],"steps":steps}


def evaluate(n,gates,inputs):
    validate(n,gates)
    if len(inputs)!=n or any(bit not in (0,1,False,True) for bit in inputs):
        raise ValueError("n Boolean inputs required")
    values=[None]+[int(v) for v in inputs]
    for op,args in gates:
        x=[values[a] for a in args]
        if op=="NOT": v=1-x[0]
        elif op=="AND": v=x[0]&x[1]
        elif op=="OR": v=x[0]|x[1]
        else: v=x[0]^x[1]
        values.append(v)
    return tuple(values[1:])


def random_dag(seed, n=3, g=12):
    rng=random.Random(seed)
    gates=[]
    for i in range(g):
        op=rng.choice(tuple(OPS))
        args=tuple(rng.sample(range(1,n+i+1),OPS[op]))
        gates.append((op,args))
    return tuple(gates)


def examples():
    return (
       (2, (("AND",(1,2)),)),
       (2, (("AND",(1,2)),("OR",(1,3)))),
       (2, (("XOR",(1,2)),("NOT",(3,)),("AND",(3,4)))),
       (2, (("AND",(1,2)),("OR",(1,3)),("XOR",(3,4)),("NOT",(5,)))),
    )


def report():
    rows=[]
    for label,n,gates in [*( ("small_"+str(i),n,gate) for i,(n,gate) in enumerate(examples(),1)),
                          *(("seed_"+str(s),3,random_dag(s)) for s in (29,31,37,41,43))]:
        proof=certificate(n,gates)
        payload=json.dumps(proof,sort_keys=True,separators=(',',':')).encode()
        rows.append({"case":label,"n_inputs":n,"gates":len(gates),
                     "axioms":len(proof["axioms"]),"derived":len(proof["steps"]),
                     "bound":sum(COST[op] for op,_ in gates)+2,
                     "max_width":max(len(c) for c in proof["axioms"]+[s["clause"] for s in proof["steps"]]),
                     "sha256":hashlib.sha256(payload).hexdigest()})
    return {"scope":"Two identical mixed Boolean circuits with shared primary inputs, and opposed outputs; ordinary DAG resolution only",
            "claimed_p_vs_np_proof":False,"new_lean_theorems":0,"max_truth_table_assignments_per_case":1024,
            "cases":rows}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out",type=Path)
    args=parser.parse_args()
    result=report()
    data=json.dumps(result,indent=2,ensure_ascii=False,sort_keys=True)+"\n"
    if args.out:
        args.out.parent.mkdir(parents=True,exist_ok=True)
        args.out.write_text(data,encoding="utf-8")
    else:
        print(data,end="")


if __name__=="__main__":
    main()
