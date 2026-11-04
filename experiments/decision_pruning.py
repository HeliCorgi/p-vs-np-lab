"""Independent finite audits of decision-label obstructions on unrestricted 3-CNF."""
import argparse
import json
from itertools import combinations_with_replacement
from pathlib import Path

from pnp_lab.residual_controls import (comparator_cnf, majority, modular_collision,
                                       predicted_residual_count, residual_cnf, satisfies)


def require(value, msg):
    if not value:
        raise AssertionError(msg)


def run():
    small = []
    for k in range(1, 5):
        # One literal-by-literal pass over the full original CNF. In contrast
        # to summing t+1, this enumerates gate valuations, including bad ones.
        original = comparator_cnf(k)
        models = [word for word in range(1 << (3*k)) if satisfies(original, word)]
        mask = (1 << k)-1
        source_pairs = [(word & mask, (word >> k) & mask) for word in models]
        expected_pairs = {(t, u) for t in range(1 << k) for u in range(t+1)}
        require(set(source_pairs) == expected_pairs and len(source_pairs) == len(expected_pairs),
                "comparison or uniqueness of the gate extension failed")
        for d in range(k+1):
            r = k-d
            sets = []
            for a in range(1 << d):
                n, h = residual_cnf(k, d, a)
                actual = {word for word in range(1 << n) if satisfies(h, word)}
                projected = {(word & ((1 << r)-1)) | ((word >> k) << r)
                             for word in models if ((word & mask) >> r) == a}
                require(actual == projected, "incorrect restrictions or gate coordinate scope")
                require(len(actual) == predicted_residual_count(k, d, a), "incorrect full model count")
                sets.append(actual)
            require(all(sets[0] <= h for h in sets), "false anchor containment")
            unions = [len(sets[0] | h) for h in sets[1:]]
            require(len(set(unions)) == (1 << d)-1 and all(unions), "yes-label diversity")
            small.append(dict(k=k, depth=d, original_variables=3*k,
                              residuals=len(sets), anchored_pairs=len(unions),
                              anchored_union_counts=unions))
    mods = []
    for m in (1, 2, 3, 4, 5, 7, 8, 9, 13, 16, 17):
        n, anchor, pos, neg = modular_collision(m)
        # Check the actual OR of functions on the same coordinates, without
        # counting branch or disjunction selectors as extra witnesses.
        yes, no = (sum(satisfies(anchor, w) or satisfies(h, w) for w in range(1 << n))
                   for h in (pos, neg))
        require(yes == m and no == 0 and yes % m == no % m, "modular obstruction")
        mods.append(dict(modulus=m, residual_variables=n, actual_counts=[yes, no],
                         residues=[yes % m, no % m]))
    # Enumerate every possible relation on a triple that avoids 000. This
    # checks the one-block bound independent of how a 2-CNF might present it.
    max_units = accepted = 0
    for mask in range(128):
        rel = {j+1 for j in range(7) if mask & (1 << j)}
        if all(majority(a, b, c) in rel for a, b, c in combinations_with_replacement(rel, 3)):
            accepted += 1
            max_units = max(max_units, len(rel & {1, 2, 4}))
    require(max_units == 2, "a majority-closed satisfying block contained all three unit vectors")
    large = []
    for k in (8, 32, 128, 512):
        # Materialize just the polynomial input clauses, not their models or residual list.
        cs = comparator_cnf(k)
        require(len(cs) == 6*k-2 and max(map(len, cs)) == 3, "input shape")
        large.append(dict(k=k, variables=3*k, clauses=len(cs), max_width=3,
                          predicted_positive_anchor_partners=(1 << k)-1))
    return dict(schema_version=1, all_checks_passed=True, exhaustive_comparator_levels=small,
                measured_modular_controls=mods, symbolic_comparator_levels=large,
                majority_closed_nonzero_relations=accepted, max_one_hot_in_one_block=max_units,
                summary=dict(exhaustive_comparator_max_k=4, exhaustive_levels=len(small),
                             exhaustive_raw_cnf_assignments=sum(1 << (3*k) for k in range(1,5)),
                             modular_examples=len(mods), majority_relations_tested=128,
                             largest_symbolic_comparator_k=large[-1]['k']),
                scope="Large counts are symbolic. These barriers target specified label/cover representations; no general SAT lower bound.")


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--out-dir', type=Path, required=True)
    out = p.parse_args().out_dir
    out.mkdir(parents=True, exist_ok=True)
    data = run()
    (out/'decision_pruning.json').write_text(json.dumps(data, sort_keys=True, indent=2)+'\n')
    print(data['summary'])
