#!/usr/bin/env python3
"""Solve a JSON CNF with explicit budgets; exit codes SAT=10, UNSAT=20, UNKNOWN=0."""
import argparse
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'src'))
from pnp_lab.shared_dag_sat import solve_cnf


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', help='JSON object with clauses and optional order; - for stdin')
    parser.add_argument('--max-states', type=int, default=100_000)
    parser.add_argument('--max-nodes', type=int, default=200_000)
    parser.add_argument('--max-work', type=int, default=5_000_000)
    args = parser.parse_args()
    try:
        data = json.loads(sys.stdin.read() if args.input == '-' else
                          Path(args.input).read_text(encoding='utf-8'))
        result = solve_cnf(data['clauses'], order=data.get('order'),
                           max_states=args.max_states, max_nodes=args.max_nodes,
                           max_work=args.max_work)
    except (ValueError, TypeError, KeyError, OSError) as exc:
        parser.error(str(exc))
    print(json.dumps(result, indent=2, sort_keys=True))
    return {'SAT': 10, 'UNSAT': 20, 'UNKNOWN': 0}[result['status']]


if __name__ == '__main__':
    sys.exit(main())
