"""General width-three SAT via the constant-block bridge and a support decision.

Local tables store one target-variable assignment per attainable signature.
There are no multiplicities. ``group_order`` is a possibly user-supplied
permutation of occurrence-group indices; the default is padded source order.
The transition limit covers the residual search, not polynomial preprocessing.
"""
from __future__ import annotations

from collections.abc import Sequence

from .block_bridge import three_cnf_to_constant_blocks
from .frontier import decide_signature_supports


def decide_three_cnf(variables: Sequence[str], clauses: Sequence[Sequence[int]], *,
                      group_order: Sequence[int] | None = None,
                      max_transitions: int | None = None) -> dict:
    if max_transitions is not None and (type(max_transitions) is not int or max_transitions < 0):
        raise ValueError('max_transitions must be None or a nonnegative integer.')
    reduced = three_cnf_to_constant_blocks(variables, clauses)
    groups, target = reduced.groups, reduced.bridge
    order = list(range(len(groups))) if group_order is None else list(group_order)
    if (len(order) != len(groups) or any(type(i) is not int for i in order)
            or set(order) != set(range(len(groups)))):
        raise ValueError('group_order must be a permutation of the occurrence-group indices.')
    out = dict(status=None, reason=None, source_witness=None, source_witness_mask=None,
               target_witness_mask=None, group_order=order, group_count=len(groups),
               target_variables=len(target.affine.variables), local_visits=0,
               support_sizes=[], frontier=None)
    if () in target.cnf:  # The reduction's canonical explicitly false target.
        out.update(status='UNSAT', reason='empty_source_clause')
        return out

    # Each target variable belongs to one group. One signature coordinate per
    # native XOR row; enumerate set bits instead of scanning every row per visit.
    index = {v: i for i, v in enumerate(target.affine.variables)}
    columns = [[index[v] for v in g] for g in groups]
    owner = {col: j for j, g in enumerate(columns) for col in g}
    effects = [0] * len(index)
    rhs = 0
    for row_index, (row, parity) in enumerate(target.affine.equations):
        rhs |= parity << row_index
        while row:
            bit = row & -row
            effects[bit.bit_length() - 1] |= 1 << row_index
            row ^= bit
    local_cnf: list[list[tuple[int, int]]] = [[] for _ in groups]
    for clause in target.cnf:
        owners = {owner[abs(lit) - 1] for lit in clause}
        if len(owners) != 1:
            raise AssertionError('Bridge emitted a nonlocal or empty clause.')
        pos = neg = 0
        for lit in clause:
            if lit > 0:
                pos |= 1 << (lit - 1)
            else:
                neg |= 1 << (-lit - 1)
        local_cnf[owners.pop()].append((pos, neg))
    tables: list[dict[int, int]] = []
    for j, cols in enumerate(columns):
        table: dict[int, int] = {}
        for word in range(1 << len(cols)):
            out['local_visits'] += 1
            sig = mask = 0
            for i, col in enumerate(cols):
                if word & (1 << i):
                    mask |= 1 << col
                    sig ^= effects[col]
            if all((pos & mask) or (neg & ~mask) for pos, neg in local_cnf[j]):
                table.setdefault(sig, mask)
        if len(cols) > 5 or len(table) > 5:
            raise AssertionError('Constant-block image exceeded the proved local bounds.')
        tables.append(table)
    out['support_sizes'] = [len(t) for t in tables]
    decision = decide_signature_supports([tables[i] for i in order], rhs,
                                         max_transitions=max_transitions)
    out.update(status=decision['status'], reason=decision['reason'], frontier=decision)
    if decision['status'] == 'SAT':
        full = 0
        for i, signature in zip(order, decision['witness']):
            full |= tables[i][signature]
        source = reduced.project_witness(full)  # Checks the mixed model and copy consistency.
        # Check the original, signed input directly, before returning a SAT answer.
        if not all(any(bool(source & (1 << (abs(x)-1))) == (x > 0) for x in c)
                   for c in reduced.original_cnf):
            raise AssertionError('Recovered source witness failed its original clauses.')
        out.update(source_witness_mask=source, target_witness_mask=full,
                   source_witness={v: bool(source & (1 << i))
                                   for i, v in enumerate(reduced.original_variables)})
    return out
