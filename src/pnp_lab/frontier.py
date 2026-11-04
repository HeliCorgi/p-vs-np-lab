"""Decide whether one mask from each finite support can XOR to a target.

This procedure deliberately ignores multiplicities. It absorbs exact affine
cosets, then explores only prefix sums compatible with the remaining affine
hull. Neither the number of residual choices nor the cut ranks have a
universal logarithmic bound. No general polynomial running time is claimed.
"""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass
from functools import reduce
from operator import xor
from typing import Any


class _Basis:
    """Insertion-only GF(2) echelon basis, with access to all earlier spans."""

    def __init__(self) -> None:
        # A row never changes. Its birth rank identifies every prefix of
        # insertions for which it is available as an elimination rule.
        self.rows: dict[int, tuple[int, int]] = {}

    def normal(self, mask: int, rank: int | None = None) -> int:
        """Linear canonical representative of mask modulo the indicated span."""
        remainder = 0
        while mask:
            pivot = mask.bit_length() - 1
            row = self.rows.get(pivot)
            if row is None or (rank is not None and row[1] >= rank):
                bit = 1 << pivot
                remainder ^= bit
                mask ^= bit
            else:
                mask ^= row[0]
        return remainder

    def add(self, mask: int) -> None:
        row = self.normal(mask)
        if row:
            self.rows[row.bit_length() - 1] = (row, len(self.rows))

    def __len__(self) -> int:
        return len(self.rows)


def _read_groups(supports: Iterable[Iterable[int]]) -> list[tuple[int, ...]]:
    result = []
    try:
        if isinstance(supports, (str, bytes)):
            raise ValueError("Expected an iterable of finite mask supports.")
        for support in supports:
            if isinstance(support, (str, bytes)):
                raise ValueError("A support must contain nonnegative integer masks.")
            values: set[int] = set()
            for mask in support:
                if type(mask) is not int or mask < 0:
                    raise ValueError("A support must contain nonnegative integer masks.")
                values.add(mask)
            result.append(tuple(sorted(values)))
    except TypeError as e:
        raise ValueError("Expected an iterable of finite mask supports.") from e
    return result


@dataclass
class AffineCore:
    """A quotient instance and the data needed to lift any residual solution."""
    groups: list
    rhs: int
    basis: _Basis
    anchor_sum: int
    absorbed: list
    residual: list
    rounds: list[int]
    projection_visits: int

    @property
    def target(self):
        return self.basis.normal(self.rhs ^ self.anchor_sum)

    @property
    def supports(self):
        return [tuple(image) for _,image in self.residual]

    def lift(self, choices):
        choices = tuple(choices)
        if (len(choices) != len(self.residual) or
                any(type(x) is not int or x not in im for x,(_,im) in zip(choices,self.residual)) or
                reduce(xor,choices,0) != self.target):
            raise ValueError('Not a feasible choice in the affine quotient.')
        witness = [0] * len(self.groups)
        error = self.rhs ^ self.anchor_sum
        for x,(i,image) in zip(choices,self.residual):
            witness[i] = image[x]
            error ^= witness[i]
        # A reverse step realizes exactly the required image, leaving the
        # correction in the smaller pre-absorption space (birth rank).
        for i, old_rank, anchor, raw_anchor, image in reversed(self.absorbed):
            chosen = image[anchor ^ self.basis.normal(error, old_rank)]
            witness[i] = chosen
            error ^= raw_anchor ^ chosen
        if (error or reduce(xor,witness,0) != self.rhs or
                any(x not in g for x,g in zip(witness,self.groups))):
            raise AssertionError('Recovered choices failed original masks or XOR.')
        return witness


def affine_core(supports, rhs):
    """Preserve exact feasibility while extracting full affine cosets.

    Empty supports are retained as an immediate contradiction; the quotient
    need not be built on such inputs. Maps use normalized distinct options.
    """
    if type(rhs) is not int or rhs < 0:
        raise ValueError('rhs must be a nonnegative integer mask.')
    groups = _read_groups(supports)
    return _affine_core(groups,rhs)


def _affine_core(groups, rhs):
    if any(not g for g in groups):
        return AffineCore(groups,rhs,_Basis(),0,[],[(i,{v:v for v in g}) for i,g in enumerate(groups)],[],0)
    visits = 0
    rounds = []
    # At every stage, choices from the absorbed groups realize *all* sums
    # in anchor_sum + U. Group i can enlarge this coset whenever its image
    # modulo U is itself an exact affine coset. Original options need not
    # be an affine set: an earlier group may supply the missing correction.
    u = _Basis()
    anchor_sum = 0
    absorbed: list[tuple[int, int, int, int, dict[int, int]]] = []
    active = list(range(len(groups)))
    residual: list[tuple[int, dict[int, int]]] = []
    while active:
        survivors = []
        residual = []
        removed = 0
        for i in active:
            image: dict[int, int] = {}
            for original in groups[i]:
                image.setdefault(u.normal(original), original)
            visits += len(groups[i])
            anchor = next(iter(image))
            # Since the image is a subset of its affine hull, equal
            # cardinalities are sufficient. No ambient cube is enumerated.
            size = len(image)
            affine = size & (size - 1) == 0
            if affine:
                local = _Basis()
                for option in image:
                    local.add(option ^ anchor)
                affine = len(local) == size.bit_length() - 1
            if not affine:
                survivors.append(i)
                residual.append((i, image))
                continue
            raw_anchor = image[anchor]
            absorbed.append((i, len(u), anchor, raw_anchor, image))
            anchor_sum ^= raw_anchor
            for option in image:
                u.add(option ^ anchor)
            removed += 1
        if not removed:
            break  # All residual images use the same final quotient.
        rounds.append(removed)
        active = survivors  # Reproject survivors if this sweep enlarged U.
    return AffineCore(groups,rhs,u,anchor_sum,absorbed,residual,rounds,visits)


def decide_signature_supports(
    supports: Iterable[Iterable[int]], rhs: int, *, max_transitions: int | None = None,
) -> dict[str, Any]:
    """Return SAT and original chosen masks, UNSAT, or budget-limited UNKNOWN.

    Integers encode bit vectors (duplicates in a group do not matter).
    The budget counts attempted residual prefix/option pairs only. Reading
    the explicit input, exact affine elimination, polynomial rank/hull checks
    in preprocessing, and witness recovery are not charged to that counter.
    A witness is not a full assignment of an underlying CNF: it is one
    member of *each input support*, in the original group order.

    peak_states is the largest single retained layer, including a partial
    layer. Parents for earlier layers are held for recovery, so this is not a
    memory measurement. state_counts records closed layers (a SAT witness
    closes the terminal layer immediately); partial_states is separate.
    """
    if type(rhs) is not int or rhs < 0:
        raise ValueError("rhs must be a nonnegative integer mask.")
    if max_transitions is not None and (type(max_transitions) is not int or max_transitions < 0):
        raise ValueError("max_transitions must be None or a nonnegative integer.")
    groups = _read_groups(supports)  # Validate even after an empty group.
    result: dict[str, Any] = {
        "status": "UNKNOWN", "reason": None, "witness": None, "transitions": 0,
        "max_transitions": max_transitions, "peak_states": 0, "partial_states": 0,
        "state_counts": [], "state_merges": 0, "suffix_pruned": 0, "suffix_checks": 0,
        "affine_groups": 0, "affine_rank": 0, "elimination_rounds": 0,
        "affine_groups_by_round": [], "projection_visits": 0,
        "residual_groups": len(groups), "residual_indices": list(range(len(groups))),
        "cut_ranks": [], "peak_cut_rank": 0, "input_groups": len(groups),
        "input_distinct_options": sum(map(len, groups)),
    }
    if any(not s for s in groups):
        result.update(status="UNSAT", reason="empty_support")
        return result

    core = _affine_core(groups, rhs)
    residual = core.residual
    result.update(affine_groups=len(core.absorbed), affine_rank=len(core.basis),
                  elimination_rounds=len(core.rounds), affine_groups_by_round=core.rounds,
                  projection_visits=core.projection_visits, residual_groups=len(residual),
                  residual_indices=[i for i, _ in residual])
    target = core.target
    n = len(residual)

    # For suffix j..n, the affine hull is suffix_anchor[j] + V_j.
    # Insertion timestamps let one basis describe *all* suffix subspaces.
    suffix = _Basis()
    suffix_anchor = [0] * (n + 1)
    suffix_rank = [0] * (n + 1)
    for j in reversed(range(n)):
        options = residual[j][1]
        anchor = next(iter(options))
        suffix_anchor[j] = suffix_anchor[j + 1] ^ anchor
        for option in options:
            suffix.add(option ^ anchor)
        suffix_rank[j] = len(suffix)
    prefix = _Basis()
    cut_ranks = [0]
    for j, (_, options) in enumerate(residual):
        anchor = next(iter(options))
        for option in options:
            prefix.add(option ^ anchor)
        # dim(P_j intersect V_j) since P_j + V_j is the full difference span.
        cut_ranks.append(len(prefix) + suffix_rank[j + 1] - len(suffix))
    result.update(cut_ranks=cut_ranks, peak_cut_rank=max(cut_ranks))
    result["suffix_checks"] += 1
    if suffix.normal(target ^ suffix_anchor[0]):
        result.update(status="UNSAT", reason="outside_affine_hull")
        return result

    # Store parents only for states that pass the necessary suffix test.
    # Every feasible completion passes that test. Equal prefix sums have
    # exactly the same possible continuations, so one parent is enough.
    layers: list[dict[int, tuple[int, int] | None]] = [{0: None}]
    result.update(peak_states=1, state_counts=[1])
    for j, (_, options) in enumerate(residual):
        joined: dict[int, tuple[int, int] | None] = {}
        for previous in layers[-1]:
            for projected in options:
                if max_transitions is not None and result["transitions"] >= max_transitions:
                    result.update(reason="transition_budget_exhausted", partial_states=len(joined))
                    return result
                result["transitions"] += 1
                value = previous ^ projected
                result["suffix_checks"] += 1
                if suffix.normal(target ^ value ^ suffix_anchor[j + 1], suffix_rank[j + 1]):
                    result["suffix_pruned"] += 1
                elif value in joined:
                    result["state_merges"] += 1
                else:
                    joined[value] = (previous, projected)
                    result["peak_states"] = max(result["peak_states"], len(joined))
                    if j + 1 == n:
                        break  # One positive terminal state decides SAT.
            if j + 1 == n and joined:
                break
        layers.append(joined)
        result["state_counts"].append(len(joined))
        if not joined:
            result.update(status="UNSAT", reason="empty_frontier")
            return result

    choices = [0] * n
    value = target
    for j in reversed(range(n)):
        edge = layers[j + 1][value]
        if edge is None:
            raise AssertionError('Missing residual parent.')
        value, choices[j] = edge
    witness = core.lift(choices)
    result.update(status="SAT", reason="checked_original_witness", witness=witness)
    return result
