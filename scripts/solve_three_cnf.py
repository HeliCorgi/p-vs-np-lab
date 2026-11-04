#!/usr/bin/env python3
"""Decide JSON width-three CNF via the affine frontier; 0=decided, 2=UNKNOWN."""
import argparse
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'src'))
from pnp_lab.frontier_sat import decide_three_cnf
from pnp_lab.ternary_support import three_cnf_to_weight_two_supports
from pnp_lab.support_solver import decide_xor_choices


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('input', help='JSON file with variables, clauses, and optional group_order; - for stdin')
    p.add_argument('--encoding', choices=('blocks', 'sparse'), default='blocks',
                   help='Five-state blocks or three-option, weight-two XOR supports')
    p.add_argument('--max-transitions', type=int, help='Residual prefix-option attempts; preprocessing is separate')
    p.add_argument('--method', choices=('auto','frontier','gauge','graphic','cmr','holes','project','refute','lattice'), default='auto',
                   help='Backend for --encoding sparse. Optional cmr uses a trusted local executable.')
    p.add_argument('--max-matching-calls', type=int, help='Leaf matching budget for --method gauge')
    p.add_argument('--max-outer-branches', type=int, help='Outer piece-combination budget for --method gauge')
    p.add_argument('--max-tree-trials', type=int, default=3, help='Candidate trees for graphic recognition')
    p.add_argument('--cmr-executable', default='cmr-graphic')
    p.add_argument('--max-pairs', type=int, help='Cross-slice pairs in project; auto also caps this at 128')
    p.add_argument('--max-intersections', type=int, help='Lattice intersection tests')
    p.add_argument('--condition-on', nargs='+', type=int, help='Lattice cutset: parity masks in the generated kernel-parameter coordinates')
    p.add_argument('--max-slices', type=int, help='Limit on enumerated lattice cutset slices (default 256)')
    p.add_argument('--degree', type=int, help='Static indicator refutation degree (default 4)')
    p.add_argument('--max-rows', type=int, help='Generated indicator multiples in refute')
    a = p.parse_args()
    try:
        obj = json.loads(sys.stdin.read() if a.input == '-' else Path(a.input).read_text())
        if (not isinstance(obj, dict) or not isinstance(obj.get('variables'), list)
                or not isinstance(obj.get('clauses'), list)
                or not all(isinstance(c, list) for c in obj['clauses'])
                or ('group_order' in obj and not isinstance(obj['group_order'], list))):
            raise ValueError('Expected arrays variables and clauses, with an optional group_order array.')
        if a.method != 'gauge' and (a.max_matching_calls is not None or a.max_outer_branches is not None):
            raise ValueError('Matching-call/outer-branch budgets require --method gauge.')
        if a.max_pairs is not None and (a.encoding!='sparse' or a.method not in ('project','auto')):
            raise ValueError('--max-pairs requires --encoding sparse and --method project or auto.')
        if (a.degree is not None or a.max_rows is not None) and a.method!='refute':
            raise ValueError('--degree/--max-rows require --method refute.')
        if any(v is not None for v in (a.max_intersections,a.condition_on,a.max_slices)) and a.method!='lattice':
            raise ValueError('Lattice budgets and cutsets require --method lattice.')
        if a.encoding == 'blocks':
            if a.method != 'auto' or a.max_tree_trials != 3 or a.cmr_executable != 'cmr-graphic':
                raise ValueError('Support method options require --encoding sparse.')
            result = decide_three_cnf(obj['variables'], obj['clauses'], group_order=obj.get('group_order'),
                                      max_transitions=a.max_transitions)
        else:
            if 'group_order' in obj:
                raise ValueError('group_order addresses groups in the blocks encoding only.')
            red = three_cnf_to_weight_two_supports(obj['variables'], obj['clauses'])
            result = decide_xor_choices(red.supports, red.rhs, max_transitions=a.max_transitions,
                                        method=a.method, max_matching_calls=a.max_matching_calls,
                                        max_outer_branches=a.max_outer_branches,
                                        max_tree_trials=a.max_tree_trials, cmr_executable=a.cmr_executable,
                                        max_pairs=a.max_pairs, max_rows=a.max_rows,
                                        degree=4 if a.degree is None else a.degree,
                                        max_intersections=a.max_intersections, condition_on=a.condition_on or (),
                                        max_slices=256 if a.max_slices is None else a.max_slices)
            model = red.project_witness(result['witness']) if result['status'] == 'SAT' else None
            result.update(source_witness_mask=model, source_witness=(None if model is None else
                          {v: bool(model & (1 << i)) for i, v in enumerate(red.original_variables)}))
        result['encoding'] = a.encoding
    except (ValueError, OSError, TypeError) as err:
        print(f'Input error: {err}', file=sys.stderr)
        return 1
    print(json.dumps(result, indent=2, ensure_ascii=False))
    return 2 if result['status'] == 'UNKNOWN' else 0


if __name__ == '__main__':
    raise SystemExit(main())
