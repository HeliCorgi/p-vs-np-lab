"""A decision-preserving reduction from width-at-most-three CNF to XOR supports.

Choose one member of each explicit group so their XOR is zero. A group has
at most THREE options. Use two fresh bit positions per literal occurrence:
V_j carries its variable value and C_j records whether its clause selected
that occurrence. A variable broadcasts its value, a clause chooses one
occurrence, and the local support allows exactly the implication
"selected -> this literal is true". No multiplicity or SAT count is preserved.
"""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass
from functools import reduce
from operator import xor
from typing import Any

from .frontier import decide_signature_supports


def _source_holds(clauses: tuple[tuple[int, ...], ...], mask: int) -> bool:
    return all(any(bool(mask & (1 << (abs(lit) - 1))) == (lit > 0) for lit in clause)
               for clause in clauses)


def _checked_choices(groups, rhs, choices: Iterable[int]) -> tuple[int, ...]:
    if isinstance(choices, (str, bytes)):
        raise ValueError("Expected one integer mask per support.")
    try:
        chosen = tuple(choices)
    except TypeError as exc:
        raise ValueError("Expected one integer mask per support.") from exc
    if len(chosen) != len(groups) or any(type(x) is not int or x not in group
                                         for x, group in zip(chosen, groups)):
        raise ValueError("Expected a legal integer option from each support, in order.")
    if reduce(xor, chosen, 0) != rhs:
        raise ValueError("Choices do not satisfy the target XOR.")
    return chosen


@dataclass(frozen=True)
class TernarySupportReduction:
    """Immutable output of three_cnf_to_ternary_supports.

    Original variable columns and flattened occurrence IDs are zero-based;
    literals in original_cnf are signed, nonzero, one-based DIMACS indices.
    Group sections are, in order: variable broadcasts, clause choices, and
    local implications. An unused variable contributes the singleton {0}.
    """

    original_variables: tuple[str, ...]
    original_cnf: tuple[tuple[int, ...], ...]
    clause_occurrences: tuple[tuple[int, ...], ...]
    variable_masks: tuple[int, ...]
    supports: tuple[tuple[int, ...], ...]
    rhs: int = 0

    def lift_witness(self, source_mask: int) -> tuple[int, ...]:
        """Choose the first true occurrence per clause and return raw support members."""
        n = len(self.original_variables)
        if type(source_mask) is not int or not 0 <= source_mask < 1 << n:
            raise ValueError("Source assignment mask must fit the explicitly named scope.")
        broadcasts = [v if source_mask >> i & 1 else 0 for i, v in enumerate(self.variable_masks)]
        selectors = []
        local = []
        for ids, clause in zip(self.clause_occurrences, self.original_cnf):
            values = [bool(source_mask & (1 << (abs(lit) - 1))) for lit in clause]
            picked = next((j for j, val, lit in zip(ids, values, clause) if val == (lit > 0)), None)
            if picked is None:
                raise ValueError("Source assignment fails a clause.")
            selectors.append(1 << (2 * picked + 1))
            for j, val in zip(ids, values):
                v = 1 << (2 * j)
                local.append((v if val else 0) | ((v << 1) if j == picked else 0))
        choices = tuple(broadcasts + selectors + local)
        # Unused variables carry no information; projection sets them false.
        active = sum(1 << i for i, v in enumerate(self.variable_masks) if v)
        if self.project_witness(choices) != source_mask & active:
            raise AssertionError("Lifted witness failed on an active original variable.")
        return choices

    def project_witness(self, choices: Iterable[int]) -> int:
        """Check every raw choice and the target XOR, decode, then check the original CNF."""
        chosen = _checked_choices(self.supports, self.rhs, choices)
        mask = sum(1 << i for i, v in enumerate(self.variable_masks) if v and chosen[i] == v)
        if not _source_holds(self.original_cnf, mask):
            raise AssertionError("A zero-XOR support witness failed direct source verification.")
        return mask


def three_cnf_to_ternary_supports(
    variables: Iterable[str], clauses: Iterable[Iterable[int]],
) -> TernarySupportReduction:
    """Compile explicit width <= 3 clauses with no padding or occurrence collapse.

    For n named variables, m clauses and t literal occurrences, emit n+m+t
    supports on 2t coordinates. Each port is touched by just two groups.
    Only the variable broadcast can have large Hamming weight. Count the bit
    length of masks when charging the construction; it is polynomial even
    when the masks are stored as dense integers. Empty clauses become empty
    supports (UNSAT); an empty conjunction needs no selection of a literal.
    """
    if isinstance(variables, (str, bytes)) or isinstance(clauses, (str, bytes)):
        raise ValueError("Expected iterables of variable names and clauses.")
    try:
        names = tuple(variables)
        raw = []
        for clause in clauses:
            if isinstance(clause, (str, bytes)):
                raise ValueError("Expected a clause of signed integer literals.")
            raw.append(tuple(clause))
    except TypeError as exc:
        raise ValueError("Expected iterables of variable names and clauses.") from exc
    if any(not isinstance(v, str) or not v for v in names) or len(set(names)) != len(names):
        raise ValueError("Variable names must be nonempty distinct strings.")
    cnf = tuple(raw)
    n = len(names)
    broadcasts = [0] * n
    occurrences = []
    selectors = []
    local = []
    for clause in cnf:
        if len(clause) > 3:
            raise ValueError("Source clauses must have width at most three.")
        ids = tuple(range(len(local), len(local) + len(clause)))
        occurrences.append(ids)
        options = []
        for j, lit in zip(ids, clause):
            if type(lit) is not int or lit == 0 or abs(lit) > n:
                raise ValueError("Source literals must be nonzero integer indices in scope.")
            v = 1 << (2 * j)
            c = v << 1
            broadcasts[abs(lit) - 1] |= v
            options.append(c)
            local.append((0, v, v | c) if lit > 0 else (0, v, c))
        selectors.append(tuple(options))
    groups = tuple((0, v) if v else (0,) for v in broadcasts) + tuple(selectors) + tuple(local)
    return TernarySupportReduction(names, cnf, tuple(occurrences), tuple(broadcasts), groups)


@dataclass(frozen=True)
class WeightTwoTernaryReduction:
    """The same source SAT problem using options of Hamming weight at most two.

    The first t groups are occurrence copies (false = V_j; true = copy_one_masks[j]).
    Next are m selectors followed by t translated local implications. All
    equality ports are above the original 2t positions. No unused-variable
    groups are needed; the original explicit scope is still retained in direct.
    """

    direct: TernarySupportReduction
    occurrence_variables: tuple[int, ...]
    copy_one_masks: tuple[int, ...]
    n_coordinates: int
    supports: tuple[tuple[int, ...], ...]
    rhs: int = 0

    @property
    def original_variables(self):
        return self.direct.original_variables

    @property
    def original_cnf(self):
        return self.direct.original_cnf

    def lift_witness(self, source_mask: int) -> tuple[int, ...]:
        raw = self.direct.lift_witness(source_mask)
        n, m = len(self.original_variables), len(self.original_cnf)
        copies = tuple(one if source_mask >> v & 1 else 1 << (2*j)
                       for j, (v, one) in enumerate(zip(self.occurrence_variables, self.copy_one_masks)))
        shifted = tuple(x ^ (1 << (2*j)) for j, x in enumerate(raw[n+m:]))
        chosen = copies + raw[n:n+m] + shifted
        if self.project_witness(chosen) != self.direct.project_witness(raw):
            raise AssertionError("Bounded-weight lift failed.")
        return chosen

    def project_witness(self, choices: Iterable[int]) -> int:
        chosen = _checked_choices(self.supports, self.rhs, choices)
        t, m = len(self.occurrence_variables), len(self.original_cnf)
        seen: dict[int, bool] = {}
        for j, v in enumerate(self.occurrence_variables):
            bit = chosen[j] == self.copy_one_masks[j]
            if v in seen and seen[v] != bit:
                raise AssertionError("A zero-XOR copy cycle gave unequal occurrence values.")
            seen[v] = bit
        broadcasts = tuple(mask if seen.get(i, False) else 0
                           for i, mask in enumerate(self.direct.variable_masks))
        local = tuple(x ^ (1 << (2*j)) for j, x in enumerate(chosen[t+m:]))
        return self.direct.project_witness(broadcasts + chosen[t:t+m] + local)


def three_cnf_to_weight_two_supports(
    variables: Iterable[str], clauses: Iterable[Iterable[int]],
) -> WeightTwoTernaryReduction:
    """Compile maximum group size 3 AND maximum option weight 2, on <=3t bits.

    Split each variable broadcast among occurrence copies. An equality port
    shared by each pair of cyclic successors enforces equal copy bits when
    XOR is zero. Two occurrences have two distinct parallel equality ports;
    singletons need none. Without a translation the true copy option could
    touch three ports (value, incoming, outgoing). Translate its binary
    support and the attached local implication support by the same V_j;
    the two shifts cancel globally, and copy options become V_j or the two
    equality ports. This is a bijection of complete direct and bounded-weight
    support witnesses, not a claim that the original CNF counts are preserved.
    """
    direct = three_cnf_to_ternary_supports(variables, clauses)
    owners = tuple(abs(lit)-1 for clause in direct.original_cnf for lit in clause)
    by_variable = [[] for _ in direct.original_variables]
    for j, v in enumerate(owners):
        by_variable[v].append(j)
    one_masks = [0] * len(owners)
    fresh = 2*len(owners)
    for occurrences in by_variable:
        if len(occurrences) < 2:
            continue
        ports = [1 << k for k in range(fresh, fresh+len(occurrences))]
        fresh += len(occurrences)
        for a, j in enumerate(occurrences):
            one_masks[j] = ports[a-1] | ports[a]
    n, m = len(direct.original_variables), len(direct.original_cnf)
    copies = tuple((1 << (2*j), one) for j, one in enumerate(one_masks))
    shifted = tuple(tuple(x ^ (1 << (2*j)) for x in group)
                    for j, group in enumerate(direct.supports[n+m:]))
    groups = copies + direct.supports[n:n+m] + shifted
    return WeightTwoTernaryReduction(direct, owners, tuple(one_masks), fresh, groups)


def decide_ternary_reduction(
    reduction: TernarySupportReduction | WeightTwoTernaryReduction, *,
    max_transitions: int | None = None,
) -> dict[str, Any]:
    """Run the support decider and attach a directly verified source mask on SAT."""
    result = decide_signature_supports(reduction.supports, reduction.rhs,
                                       max_transitions=max_transitions)
    result["source_witness_mask"] = (reduction.project_witness(result["witness"])
                                     if result["status"] == "SAT" else None)
    return result
