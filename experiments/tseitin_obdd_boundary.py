#!/usr/bin/env python3
"""Bounded audit: constant-width interleaved OBDD vs x-first residuals.

For any m>=1 the proof of the OBDD construction is mathematical; exhaustive
CNF evaluation and suffix-signature checks stop at m=3 by preregistration.
No external SAT or BDD packages are used.
"""
from __future__ import annotations

from functools import lru_cache
import json

from experiments.tseitin_affine_lift import build_cnf, eval_clause

REJECT = "reject"
ACCEPT = "accept"


def ordered_variables(m: int) -> tuple[tuple[str, int, int], ...]:
    """(kind, pair index, DIMACS variable); all vars occur exactly once."""
    if m < 1:
        raise ValueError("m >= 1")
    stages: list[tuple[str, int, int]] = []
    for i in range(m):
        stages += [("x", i, 1+i), ("y", i, 1+m+i),
                   ("p", i, 1+2*m+i)]
        if i > 0:
            stages.append(("t", i, 3*m+i))
    assert sorted(v for _, _, v in stages) == list(range(1, 4*m))
    return tuple(stages)


def _step(m: int, kind: str, i: int, state: tuple[int, ...], bit: int):
    """State is q / (q,x) / (q,x&y) / q by successive gate stages.

    Rejected assignments jump to a shared terminal. The current parity q
    after p_i is checked by the next t_i; at i=0, t_0=p_0 implicitly.
    """
    if kind == "x":
        (q,) = state
        return (q, bit)
    if kind == "y":
        q, x = state
        return (q, x & bit)
    if kind == "p":
        q, expected = state
        if bit != expected:
            return REJECT
        q ^= bit
        if m == 1:
            return ACCEPT if q == 1 else REJECT
        return (q,)
    if kind == "t":
        (q,) = state
        if bit != q:
            return REJECT
        if i == m-1:
            return ACCEPT if q == 1 else REJECT
        return (q,)
    raise AssertionError(kind)


def build_obdd(m: int) -> dict:
    """Forward reachable-state construction of one interleaved read-once DAG."""
    order = ordered_variables(m)
    states: list[set[tuple[int, ...]]] = [{(0,)}]
    edges: dict[tuple[int, tuple[int, ...]], tuple] = {}
    for depth, (kind, i, _) in enumerate(order):
        nxt: set[tuple[int, ...]] = set()
        for state in sorted(states[depth]):
            targets = (_step(m, kind, i, state, 0),
                       _step(m, kind, i, state, 1))
            edges[(depth, state)] = targets
            for target in targets:
                if isinstance(target, tuple):
                    nxt.add(target)
        states.append(nxt)
    assert not states[-1]
    return {"m": m, "order": order, "states": tuple(tuple(sorted(s)) for s in states),
            "edges": edges}


def accept(obdd: dict, assignment: int) -> bool:
    if assignment < 0 or assignment >= 1 << (4*obdd['m']-1):
        raise ValueError("assignment outside the encoded variable universe")
    state: tuple[int, ...] | str = (0,)
    for depth, (_, _, variable) in enumerate(obdd['order']):
        if state == REJECT:
            return False
        if state == ACCEPT:
            return True
        state = obdd['edges'][(depth, state)][(assignment >> (variable - 1)) & 1]
    return state == ACCEPT


def accepting_assignments_by_dp(obdd: dict) -> int:
    """Count all accepted complete assignments using shared DAG nodes."""
    levels = len(obdd['order'])

    @lru_cache(maxsize=None)
    def count(depth: int, state: tuple[int, ...] | str) -> int:
        if state == REJECT:
            return 0
        if state == ACCEPT:
            return 1 << (levels-depth)
        assert depth < levels
        a, b = obdd['edges'][(depth, state)]
        return count(depth+1, a) + count(depth+1, b)

    return count(0, (0,))


def node_stats(obdd: dict) -> dict:
    widths = tuple(len(s) for s in obdd['states'][:-1])
    n = sum(widths)
    return {"levels":len(widths), "max_live_width":max(widths),
            "nonterminal_nodes":n, "total_nodes_including_two_terminals":n+2,
            "edges_from_nonterminal_nodes":2*n, "live_widths":widths}


def x_first_residual_signatures(m: int):
    """Independent CNF-only suffix oracle; fixed small-m audit only."""
    if not 1 <= m <= 3:
        raise ValueError("full suffix signatures are capped at m<=3")
    n, clauses, _ = build_cnf(m)
    signatures = []
    # The DIMACS prefix consists of x_0..x_{m-1}; all other bits are suffix.
    for x in range(1<<m):
        signatures.append(tuple(s for s in range(1<<(n-m))
                                if all(eval_clause(clause, x | (s<<m))
                                       for clause in clauses)))
    return tuple(signatures)


def verify(m: int) -> dict:
    if not 1 <= m <= 3:
        raise ValueError("preregistered full Boolean audit: 1 <= m <= 3")
    obdd = build_obdd(m)
    stats = node_stats(obdd)
    n, clauses, _ = build_cnf(m)
    mismatch = []
    independent_sats = 0
    for z in range(1<<n):
        oracle = all(eval_clause(c,z) for c in clauses)
        independent_sats += oracle
        if accept(obdd,z) != oracle:
            mismatch.append(z)
    assert not mismatch
    signatures = x_first_residual_signatures(m)
    assert len(set(signatures)) == 1 << m
    assert signatures[0] == ()
    assert all(signatures[x] for x in range(1,1<<m))
    assert independent_sats == sum(map(len,signatures))
    assert stats['max_live_width'] <= 4
    assert stats['nonterminal_nodes'] == 12*m-7
    assert stats['levels'] == n
    assert accepting_assignments_by_dp(obdd) == independent_sats
    assert independent_sats == (2**m-1)*2**(m-1)
    return {"m": m, "variables": n, "clauses": len(clauses),
            "full_assignments_checked":1<<n, "nonterminal_nodes":stats['nonterminal_nodes'],
            "terminal_nodes":2, "max_live_width":stats['max_live_width'],
            "live_widths":list(stats['live_widths']),
            "accepted_assignments_cnf_oracle": independent_sats,
            "accepted_assignments_dag_dp":accepting_assignments_by_dp(obdd),
            "different_x_first_suffix_residuals":len(set(signatures)),
            "nonempty_x_first_suffix_residuals":sum(bool(x) for x in signatures)}


def main() -> None:
    print(json.dumps({"scope":"preregistered exhaustive m=1..3 only",
                      "mathematical_claim":"interleaved OBDD has 12m-7 nonterminal nodes and live width <=4; x-first cut has >=2^m-1 live residuals",
                      "experiment_is_formal_proof":False,
                      "new_lean_theorems":0,
                      "results":[verify(m) for m in (1,2,3)]},sort_keys=True,indent=2))


if __name__ == "__main__":
    main()
