"""Decide explicit XOR-choice instances by local translations and perfect matching.

A fixed local XOR translation changes the target by its centre and preserves
all choices bijectively. Every support contained in a radius-one ball thereby
becomes a unit-mask support. Other supports are partitioned, and nonmatchable
binary selectors are further restricted by an exact GF(2) *necessary* test.
This decides existence, not the number of choices. The general case still
has exponentially many branches. Matching UNSAT relies on unit_matching.
"""
from __future__ import annotations

from dataclasses import dataclass
from functools import reduce
from itertools import combinations, product
from math import prod
from operator import xor

from .frontier import _Basis, _read_groups
from .unit_matching import decide_unit_supports


@dataclass(frozen=True)
class GaugePiece:
    """Original (untranslated) options, with a verified radius-one centre."""
    center: int
    options: tuple[int, ...]


def _pair_centers(a, b):
    d = a ^ b
    w = d.bit_count()
    if w == 1:
        return (a, b)
    if w == 2:
        low = d & -d
        return (a ^ low, a ^ d ^ low)
    return ()  # Callers give distinct options; distance >= 3 is impossible.


def _center(options):
    if all(v.bit_count() <= 1 for v in options):
        return 0
    if len(options) == 1:
        return options[0]
    # Any centre must cover the first two options. At distance one, only
    # the endpoints work. At distance two, only their two midpoints work.
    for c in sorted(_pair_centers(options[0], options[1])):
        if all((v ^ c).bit_count() <= 1 for v in options):
            return c
    return None


def radius_one_center(support):
    """Return a centre of a containing Hamming ball, None if none, 0 for empty."""
    return _center(_read_groups([support])[0])


def _partition(options):
    pieces = []
    while options:
        center = _center(options)
        if center is not None:
            pieces.append(GaugePiece(center, options))
            break
        # Greedily take a ball covering the most remaining choices. Any ball
        # containing >=2 distinct choices has a centre from one of these
        # pairs. A singleton is always possible. Ties use the smaller centre.
        centers = set(options)
        for a, b in combinations(options, 2):
            centers.update(_pair_centers(a, b))
        best, best_c = (), None
        for c in sorted(centers):
            part = tuple(x for x in options if (x ^ c).bit_count() <= 1)
            if len(part) > len(best):
                best, best_c = part, c
        pieces.append(GaugePiece(best_c, best))
        used = set(best)
        options = tuple(x for x in options if x not in used)
    return tuple(pieces)


def partition_radius_one(support):
    """Disjoint covering by balls; minimum piece count for at most 3 options.

    On larger supports this polynomial greedy rule need not minimize branches.
    A ternary nonfit has two pieces if some pair is at distance <=2, else three.
    """
    return _partition(_read_groups([support])[0])


def _selector_space(columns, target):
    """Return (rank, particular selector or None, independent kernel vectors)."""
    rows, kernel = {}, []
    for i, col in enumerate(columns):
        coeff = 1 << i
        while col:
            p = col.bit_length() - 1
            hit = rows.get(p)
            if hit is None:
                rows[p] = col, coeff
                break
            col ^= hit[0]
            coeff ^= hit[1]
        if not col:
            # Its highest selector bit i is fresh. These independent relations
            # number len(columns)-rank, so they span the complete kernel.
            kernel.append(coeff)
    particular = 0
    while target:
        hit = rows.get(target.bit_length() - 1)
        if hit is None:
            return len(rows), None, kernel
        target ^= hit[0]
        particular ^= hit[1]
    return len(rows), particular, kernel


def decide_with_gauge_matching(supports, rhs, *, max_matching_calls=None,
                               max_outer_branches=None):
    """Exact decision with optional independent limits on matching and outer work.

    ``branches_total`` is the raw product of piece counts BEFORE projection.
    Nonfit two-option groups become binary selectors. An outer branch chooses
    a piece per *other* split group. Reduce the required binary-selector sum
    modulo all differences available inside this branch's matching groups.
    Only a solution of this linear system can be completed. Each such selector
    assignment is tested by exact matching, then lifted to the original masks.

    ``max_matching_calls`` bounds only blossom calls: it does not bound the
    number of outer branches that fail a linear test. ``max_outer_branches``
    bounds those outer visits independently. Neither caps preprocessing time,
    graph size, or total memory. A cap yields UNKNOWN if a necessary subproblem
    remains unchecked. Calls and identified compatible branches are distinct:
    the latter counts all projected assignments for every outer branch visited,
    even when early SAT or a budget means not every such assignment was tried.
    """
    if type(rhs) is not int or rhs < 0:
        raise ValueError('rhs must be a nonnegative integer mask.')
    for v in (max_matching_calls, max_outer_branches):
        if v is not None and (type(v) is not int or v < 0):
            raise ValueError('Each budget must be None or a nonnegative integer.')
    groups = _read_groups(supports)  # Validate every raw input, even after an empty support.
    parts = [_partition(g) for g in groups]
    counts = [len(ps) for ps in parts]
    binary = [i for i, ps in enumerate(parts) if len(ps) > 1 and len(groups[i]) == 2]
    nonlinear = [i for i, ps in enumerate(parts) if len(ps) > 1 and len(groups[i]) > 2]
    matched = [i for i, ps in enumerate(parts) if len(ps) == 1 or len(groups[i]) > 2]
    out = dict(status='UNKNOWN', reason=None, witness=None, centers=None, translated_rhs=None,
               translated_witness=None, groups=len(groups), defect_groups=len(binary)+len(nonlinear),
               binary_defects=len(binary), nonbinary_defects=len(nonlinear), pieces_per_group=counts,
               branches_total=prod(counts), outer_branches_total=prod(counts[i] for i in nonlinear),
               outer_branches_checked=0, outer_branches_inconsistent=0, raw_branches_ruled_out=0,
               compatible_branches_identified=0, min_binary_rank=None, max_binary_rank=None,
               matching_calls=0, graph_vertices_peak=0, graph_edges_peak=0,
               total_blossom_contractions=0, total_scanned_adjacencies=0,
               max_matching_calls=max_matching_calls, max_outer_branches=max_outer_branches)
    if any(not g for g in groups):
        out.update(status='UNSAT', reason='empty_support', outer_branches_total=0)
        return out
    if not groups:
        if rhs:
            out.update(status='UNSAT', reason='empty_xor_mismatch')
        else:
            out.update(status='SAT', reason='empty_xor_witness', witness=[], centers=[],
                       translated_rhs=0, translated_witness=[])
        return out

    chosen = {i: ps[0] for i, ps in enumerate(parts) if len(ps) == 1}
    for picks in product(*(parts[i] for i in nonlinear)):
        if max_outer_branches is not None and out['outer_branches_checked'] >= max_outer_branches:
            out['reason'] = 'outer_branch_budget_exhausted'
            return out
        out['outer_branches_checked'] += 1
        chosen.update(zip(nonlinear, picks))
        span = _Basis()
        residual = rhs
        center_xor = 0
        unit_groups = []
        for i in matched:
            piece = chosen[i]
            anchor = piece.options[0]
            residual ^= anchor
            center_xor ^= piece.center
            unit_groups.append(tuple(v ^ piece.center for v in piece.options))
            for v in piece.options[1:]:
                span.add(v ^ anchor)
        cols = []
        for i in binary:
            a, b = groups[i]
            residual ^= a
            cols.append(span.normal(a ^ b))
        rank, first, kernel = _selector_space(cols, span.normal(residual))
        for key, fn in [('min_binary_rank', min), ('max_binary_rank', max)]:
            old = out[key]
            out[key] = rank if old is None else fn(old, rank)
        possible = (1 << len(kernel)) if first is not None else 0
        out['raw_branches_ruled_out'] += (1 << len(binary))-possible
        out['compatible_branches_identified'] += possible
        if first is None:
            out['outer_branches_inconsistent'] += 1
            continue
        selector = first
        for j in range(possible):
            if max_matching_calls is not None and out['matching_calls'] >= max_matching_calls:
                out['reason'] = 'matching_call_budget_exhausted'
                return out
            if j:  # reflected Gray order on coefficients of the kernel basis
                selector ^= kernel[(j & -j).bit_length() - 1]
            fixed = [groups[i][(selector >> k) & 1] for k, i in enumerate(binary)]
            unit_rhs = rhs ^ center_xor ^ reduce(xor, fixed, 0)
            leaf = decide_unit_supports(unit_groups, unit_rhs)
            out['matching_calls'] += 1
            out['graph_vertices_peak'] = max(out['graph_vertices_peak'], leaf['graph_vertices'])
            out['graph_edges_peak'] = max(out['graph_edges_peak'], leaf['graph_edges'])
            out['total_blossom_contractions'] += leaf['blossom_contractions']
            out['total_scanned_adjacencies'] += leaf['scanned_adjacencies']
            if leaf['status'] == 'SAT':
                # Fold the fixed binary choices back in as translated zero singletons.
                witness, centers, units = ([0] * len(groups) for _ in range(3))
                for i, v in zip(binary, fixed):
                    witness[i] = centers[i] = v
                for i, unit in zip(matched, leaf['witness']):
                    centers[i] = chosen[i].center
                    units[i] = unit
                    witness[i] = unit ^ centers[i]
                if (any(v not in g for v, g in zip(witness, groups)) or reduce(xor, witness, 0) != rhs
                        or reduce(xor, units, 0) != unit_rhs or any(v.bit_count() > 1 for v in units)):
                    raise AssertionError('Recovered gauge witness fails the original problem.')
                out.update(status='SAT', reason='checked_original_witness', witness=witness,
                           centers=centers, translated_witness=units, translated_rhs=unit_rhs)
                return out
    out.update(status='UNSAT', reason='all_branches_excluded')
    return out
