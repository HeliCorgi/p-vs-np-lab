#!/usr/bin/env python3
"""Fixed paired test of retained conflict information; not a P versus NP proof.

This protocol is committed before the solver/panel is executed. The candidate
uses only ordinary resolution, whose known expander-Tseitin lower bounds already
rule out a polynomial total-cost general decider of this form. The finite audit
tests rescue of the physical examples and costs of retention, not that theorem.
"""

PROTOCOL = dict(
    version=1,
    physical_blocks=[1, 4, 16],
    graph_xor_variables=[12, 24, 36, 48],
    random_variables=[12, 24, 36, 48],
    seeds=[0, 1],
    pigeonhole_holes=[2, 3, 4, 5],
    max_work=200_000,
    max_proof_literals=50_000,
    max_proof_nodes=10_000,
    max_learned_literals=10_000,
    max_depth=128,
    decision_rule='lowest index in an unsatisfied clause, false first',
    backtracking='conflict-directed in both modes',
    unknown_policy='retain all unfinished outcomes, no cap increases',
)
