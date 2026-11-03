#!/usr/bin/env python3
"""Decide JSON width-three CNF via the affine frontier; 0=decided, 2=UNKNOWN."""
import argparse
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'src'))
from pnp_lab.frontier_sat import decide_three_cnf


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('input', help='JSON file with variables, clauses, and optional group_order; - for stdin')
    p.add_argument('--max-transitions', type=int, help='Residual prefix-option attempts; preprocessing is separate')
    a = p.parse_args()
    try:
        obj = json.loads(sys.stdin.read() if a.input == '-' else Path(a.input).read_text())
        if (not isinstance(obj, dict) or not isinstance(obj.get('variables'), list)
                or not isinstance(obj.get('clauses'), list)
                or not all(isinstance(c, list) for c in obj['clauses'])
                or ('group_order' in obj and not isinstance(obj['group_order'], list))):
            raise ValueError('Expected arrays variables and clauses, with an optional group_order array.')
        result = decide_three_cnf(obj['variables'], obj['clauses'], group_order=obj.get('group_order'),
                                  max_transitions=a.max_transitions)
    except (ValueError, OSError, TypeError) as err:
        print(f'Input error: {err}', file=sys.stderr)
        return 1
    print(json.dumps(result, indent=2, ensure_ascii=False))
    return 2 if result['status'] == 'UNKNOWN' else 0


if __name__ == '__main__':
    raise SystemExit(main())
