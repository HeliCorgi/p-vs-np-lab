"""Try one parity anchor assignment, then actually lift it by residual 2-SAT.

The only decision issued here is SAT with a raw-CNF-checked original word.
A particular proposal that fails to lift does not certify UNSAT.
"""
from collections import defaultdict

from .integer_feedback import learn_anchor_clauses
from .modular_hull import _input
from .observation_2sat import _base


def check_feedback_witness(n, clauses, witness):
    try:
        cs = _input(n, clauses)
        return (type(witness) is int and witness >= 0 and witness.bit_length() <= n and
                all(any(bool(witness >> (abs(l)-1) & 1) == (l > 0) for l in c) for c in cs))
    except (TypeError, ValueError):
        return False


def feedback_witness(n, clauses, *, max_active=4096, max_edges=1000000,
                     max_clauses=50000, max_word_bits=100000,
                     max_lemmas=50000, max_path_steps=1000000):
    """Construct a satisfying assignment without a graph, planted word, or hints.

    Each cap can be None. The arc limit bounds the learner's edge visits and,
    separately, the residual SCC graph's arc count. Integer model masks use
    dense temporary coordinates; original-label output has its own bit cap.
    """
    for limit in (max_active, max_edges, max_clauses, max_word_bits, max_lemmas, max_path_steps):
        if limit is not None and (type(limit) is not int or limit < 0):
            raise ValueError('invalid feedback witness cap')
    if type(n) is not int or n < 0 or isinstance(clauses, (str, bytes)):
        raise ValueError('invalid original formula')
    stats = dict(budget_limited=False, parity_rows=0, parity_table_cells=0,
                 rank=0, xor_reductions=0, back_substitutions=0, residual_clauses=0,
                 residual_arcs=0, scc_vertices=0, scc_calls=0, anchor_proposals=0,
                 raw_clauses_checked=0, projection=None)

    def unknown(reason, budget=False):
        stats['budget_limited'] = budget
        return dict(status='UNKNOWN', reason=reason, witness=None, certificate=None, stats=stats)

    if max_clauses is not None:
        buffered = []
        for row in clauses:
            if len(buffered) >= max_clauses:
                return unknown('raw clause cap', True)
            buffered.append(row)
        clauses = buffered
    cs = _input(n, clauses)
    active = {abs(l) for c in cs for l in c}
    stats.update(active_variables=len(active), input_clauses=len(cs))
    if max_active is not None and len(active) > max_active:
        return unknown('active variable cap', True)
    if max_word_bits is not None and max(active, default=0) > max_word_bits:
        return unknown('original word bit cap', True)
    proj = learn_anchor_clauses(n, cs, max_edges=max_edges, max_lemmas=max_lemmas,
                                max_path_steps=max_path_steps)
    stats['projection'] = proj['stats']
    if not proj['complete']:
        return unknown(proj['reason'], True)
    blocks = defaultdict(set)
    for c in proj['clauses']:
        if len(c) != 3:
            return unknown('projection is not exclusively ternary parity blocks')
        scope = tuple(map(abs, c))
        blocks[scope].add(sum(1 << i for i, l in enumerate(c) if l < 0))
    if not blocks:
        return unknown('no ternary parity blocks')
    labels = sorted({v for scope in blocks for v in scope})
    name = {v: i for i, v in enumerate(labels)}
    basis = {}
    for scope, forbidden in sorted(blocks.items()):
        # Four falsifying words of a single parity: only the opposite
        # half-cube is admitted by the conjunction of these four clauses.
        stats['parity_table_cells'] += 8
        if forbidden == {0, 3, 5, 6}:
            rhs = 1
        elif forbidden == {1, 2, 4, 7}:
            rhs = 0
        else:
            return unknown('projection is not exclusively ternary parity blocks')
        stats['parity_rows'] += 1
        a = sum(1 << name[v] for v in scope)
        while a:
            pivot = a.bit_length()-1
            if pivot not in basis:
                basis[pivot] = (a, rhs)
                stats['rank'] += 1
                break
            m, c = basis[pivot]
            a ^= m
            rhs ^= c
            stats['xor_reductions'] += 1
        if not a and rhs:
            return unknown('inconsistent parity proposal; no model constructed')
    y = 0
    for pivot, (a, rhs) in sorted(basis.items()):
        y |= ((rhs ^ ((y & a).bit_count() % 2)) << pivot)
        stats['back_substitutions'] += 1
    stats['anchor_proposals'] = 1
    fixed = {v: bool(y >> i & 1) for v, i in name.items()}
    remaining = sorted(active.difference(fixed))
    names = {v: i for i, v in enumerate(remaining)}
    binary = []
    for c in cs:
        row = set(c)
        if any(-l in row for l in row) or any(abs(l) in fixed and fixed[abs(l)] == (l > 0) for l in row):
            continue
        residual = sorted((l for l in row if abs(l) not in fixed), key=abs)
        if len(residual) > 2:
            return unknown('proposed assignment leaves a nonbinary clause')
        if not residual:
            return unknown('proposed assignment falsifies a raw clause')
        stats['residual_arcs'] += len(residual)
        if max_edges is not None and stats['residual_arcs'] > max_edges:
            return unknown('residual arc cap', True)
        binary.append(tuple((names[abs(l)], int(l < 0)) for l in residual))
        stats['residual_clauses'] += 1
    stats.update(scc_calls=1, scc_vertices=2*len(remaining))
    ext = _base(len(remaining), binary)
    if ext is None:
        return unknown('this parity assignment has no residual lift')
    word = sum(1 << (v-1) for v, bit in fixed.items() if bit)
    word |= sum(1 << (v-1) for i, v in enumerate(remaining) if ext >> i & 1)
    if not check_feedback_witness(n, cs, word):
        raise AssertionError('constructed word fails original formula')
    stats.update(raw_clauses_checked=len(cs), original_word_bits=word.bit_length())
    return dict(status='SAT', reason='checked lifted assignment on original clauses',
                witness=word, certificate=None, stats=stats)
