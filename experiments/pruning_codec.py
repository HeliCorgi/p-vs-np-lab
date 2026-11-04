"""Exercise the actual affine/explicit-syntax labels and complete pruning driver."""
import argparse
import json
from pathlib import Path

from pnp_lab.decision_labels import or_cnf, residual_label
from pnp_lab.decision_pruning import solve_pruned
from pnp_lab.label_controls import coupled_core, marked_model, prefix_restriction, tagged_xor
from pnp_lab.residual_controls import satisfies


def require(ok, detail):
    if not ok:
        raise AssertionError(detail)


def core(k):
    return coupled_core(k) if k >= 3 else ([(1, 2)] if k == 2 else [])


def run():
    levels = []
    pairs_checked = 0
    for k in range(1, 5):
        n, pos = tagged_xor(k, core(k))
        m, neg = tagged_xor(k, core(k), marked=True)
        for t in range(1 << k):
            w = marked_model(k, t)
            require(satisfies(neg, w) and satisfies(pos, w & ((1 << n)-1)),
                    "independent raw witness on both twins")
        for d in range(k+1):
            inputs = [prefix_restriction(neg, d, a) for a in range(1 << d)]
            pos_keys = {residual_label(n, prefix_restriction(pos, d, a)) for a in range(1 << d)}
            neg_keys = {residual_label(m, h) for h in inputs}
            require(len(pos_keys) == 1 and len(neg_keys) == 1 << d and
                    all(key[0] == 'CORE' for key in neg_keys), "unexpected individual key counts")
            # Distribution of OR is symmetric; compute each unordered pair once,
            # check the distinct-partner property separately around EVERY anchor.
            by_anchor = [set() for _ in inputs]
            for a in range(len(inputs)):
                for b in range(a):
                    h = or_cnf(m, inputs[a], inputs[b])
                    lab = residual_label(m, h)
                    require(lab[0] == 'CORE', "anchored OR should retain markers")
                    by_anchor[a].add(lab)
                    by_anchor[b].add(lab)
                    pairs_checked += 1
            require(all(len(entries) == (1 << d)-1 for entries in by_anchor), "anchor collision")
            levels.append(dict(k=k, depth=d, positive_keys=len(pos_keys),
                               marked_individual_keys=len(neg_keys), anchors_checked=len(by_anchor),
                               marked_distinct_partners_per_anchor=len(by_anchor[0])))
    runs = []
    k=4
    for marked, mode in ((False, 'syntax'), (False, 'affine'), (True, 'affine')):
        n, h = tagged_xor(k, core(k), marked=marked)
        r = solve_pruned(n, h, order=range(n), max_width=4, label_mode=mode)
        ought = ['SAT', [1,1,1,1,1]] if not marked and mode == 'affine' else ['UNKNOWN', [1,2,4,8]]
        require(r['status'] == ought[0] and r['widths'][:len(ought[1])] == ought[1], "driver disagrees")
        runs.append(dict(marked=marked, n=n, clauses=len(h), **r))
    return dict(schema_version=1, all_checks_passed=True, exhaustive_tag_levels=levels,
                equal_budget_driver=runs,
                summary=dict(max_k_exhaustive=4, levels=len(levels), distinct_pair_queries=pairs_checked,
                             driver_cap=4, unmarked_affine=runs[1]['status'],
                             marked_affine=runs[2]['status'], marked_widths=runs[2]['widths']),
                scope="Both coupled controls are SAT and existentially equivalent on the original variables. This is a fixed-order barrier to the actual present codec and driver, not to all decision keys.")


if __name__ == '__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--out-dir',type=Path,required=True)
    out=p.parse_args().out_dir
    out.mkdir(parents=True,exist_ok=True)
    r=run()
    (out/'pruning_codec.json').write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
    print(r['summary'])
