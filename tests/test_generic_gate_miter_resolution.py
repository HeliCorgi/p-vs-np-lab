"""Independent, bounded audit of mixed-gate double-copy miter certificates."""
from __future__ import annotations

from copy import deepcopy
import json
from pathlib import Path
import unittest

from experiments.generic_gate_miter_resolution import (
    certificate, evaluate, examples, gate_clauses, miter, random_dag,
    report, validate, OPS, COST)


def replay_independently(proof):
    """Separate signed-literal SET implementation, not the generator's solver."""
    n=proof["variables"]
    all_lines=[]
    for clause in proof["axioms"]:
        c=set(clause)
        if not c or len(c)!=len(clause) or any(not (1<=abs(x)<=n) or -x in c for x in c):
            raise ValueError("bad axiom")
        all_lines.append(c)
    for step in proof["steps"]:
        a,b,p=step["left"],step["right"],step["pivot"]
        if not (0<=a<len(all_lines) and 0<=b<len(all_lines)):
            raise ValueError("forward parent")
        if not (1<=abs(p)<=n and p in all_lines[a] and -p in all_lines[b]):
            raise ValueError("invalid inference")
        result=(all_lines[a]-{p}) | (all_lines[b]-{-p})
        if len(result)>3 or any(-lit in result for lit in result):
            raise ValueError("tautology or wide resolvent")
        if result != set(step["clause"]) or len(result)!=len(step["clause"]):
            raise ValueError("wrong clause")
        all_lines.append(result)
    if all_lines[-1]:
        raise ValueError("last clause not empty")
    return {"derived":len(proof["steps"]),"max_width":max(map(len,all_lines))}


def eval_clause(c,assignment):
    return any((assignment[abs(x)] if x>0 else not assignment[abs(x)]) for x in c)


def sibling_witness(n,gates,raw):
    g=len(gates)
    gate_values=evaluate(n,gates,raw)
    value=[0]*(n+2*g+1)
    for i,bit in enumerate(raw,1): value[i]=bit
    for j,bit in enumerate(gate_values[n:]):
        value[n+j+1]=bit
        value[n+g+j+1]=bit
    output=gate_values[-1]
    _,cnf=miter(n,gates)
    same_output=cnf[:-2]+(((n+g,) if output else (-(n+g),)),
                           ((n+2*g,) if output else (-(n+2*g),)))
    assert all(eval_clause(c,value) for c in same_output)
    assert not all(eval_clause(c,value) for c in cnf)
    return same_output


class GenericMiterTests(unittest.TestCase):
    def test_fixed_and_random_dags_and_fanout(self):
        samples=list(examples())+[(3,random_dag(s)) for s in (29,31,37,41,43)]
        for n,gates in samples:
            with self.subTest(gates=gates):
                proof=certificate(n,gates)
                checked=replay_independently(proof)
                self.assertEqual(checked["max_width"],3)
                self.assertEqual(proof["variables"],n+2*len(gates))
                self.assertLessEqual(checked["derived"],2+sum(COST[o] for o,_ in gates))
                self.assertEqual(len(proof["axioms"]),2+sum(2*(2 if o=='NOT' else 4 if o=='XOR' else 3) for o,_ in gates))
                for x in ([0]*n,[1]*n):
                    sibling_witness(n,gates,x)

    def test_independent_all_assignments_tiny_only(self):
        for n,gates in examples():
            size=n+2*len(gates)
            self.assertLessEqual(size,10)
            _,cnf=miter(n,gates)
            self.assertEqual(sum(all(eval_clause(c,[0]+[(z>>i)&1 for i in range(size)]) for c in cnf)
                                  for z in range(1<<size)),0)
            # The sibling has exactly 2^n satisfying extensions for output-consistent units
            seen=0
            for x in range(1<<n):
                raw=[(x>>i)&1 for i in range(n)]
                sibling_witness(n,gates,raw)
                seen+=1
            self.assertEqual(seen,1<<n)

    def test_corruptions_independently_rejected(self):
        p=certificate(*examples()[-1])
        checks=[("steps",0,"pivot", lambda x:-x),
                ("steps",0,"left",lambda x:100000),
                ("steps",-1,"clause",lambda x:[1]),
                ("axioms",0,None,lambda x:[9999])]
        for branch,idx,field,edit in checks:
            q=deepcopy(p)
            if field is None:q[branch][idx]=edit(q[branch][idx])
            else:q[branch][idx][field]=edit(q[branch][idx][field])
            with self.assertRaises(ValueError):
                replay_independently(q)

    def test_reject_violation_of_preconditions(self):
        bad=[(1,(("AND",(1,1)),)),(2,()),(2,(("XOR",(1,1)),)),
             (2,(("AND",(1,3)),)),(2,(("NOR",(1,2)),)),
             (2,(("NOT",(1,2)),))]
        for n,g in bad:
            with self.assertRaises(ValueError):validate(n,g)

    def test_saved_reproducibility(self):
        saved=json.loads((Path(__file__).resolve().parents[1]/"results"/"generic_gate_miter_resolution.json").read_text())
        self.assertEqual(report(),saved)
        self.assertFalse(saved["claimed_p_vs_np_proof"])
        self.assertEqual(saved["new_lean_theorems"],0)


if __name__=="__main__":
    unittest.main()
