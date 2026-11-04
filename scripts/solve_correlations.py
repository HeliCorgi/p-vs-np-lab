#!/usr/bin/env python3
"""Discover or independently check nonlinear proof traces for a JSON 3-CNF."""
import argparse
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'src'))
from pnp_lab.correlation import check_correlation_report, solve_correlations


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument('input')
    cli.add_argument('--method', choices=('relations', 'resolution', 'polynomial', 'marginals'),
                     default='relations')
    cli.add_argument('--width', type=int, default=4)
    cli.add_argument('--max-rows', type=int, default=50000)
    cli.add_argument('--max-pairs', type=int, default=1000000)
    cli.add_argument('--max-subsets', type=int, default=5000000)
    cli.add_argument('--max-union-width', type=int, default=12)
    cli.add_argument('--max-degree', type=int)
    cli.add_argument('--check', metavar='REPORT', help='Replay a report; - reads it from stdin')
    args = cli.parse_args()
    try:
        source = json.loads(Path(args.input).read_text())
        vs, cs = source['variables'], source['clauses']
        if (not isinstance(vs, list) or not all(type(v) is str and v for v in vs)
                or len(set(vs)) != len(vs) or not isinstance(cs, list)):
            raise ValueError('expected distinct variable names and a clause list')
        if args.check:
            report = json.loads(sys.stdin.read() if args.check == '-' else Path(args.check).read_text())
            statement = check_correlation_report(len(vs), cs, report)
            print('VERIFIED: ' + statement if statement else 'REJECTED')
            return 0 if statement else 1
        result = solve_correlations(len(vs), cs, method=args.method, width=args.width,
                                    max_rows=args.max_rows, max_pairs=args.max_pairs,
                                    max_subsets=args.max_subsets,
                                    max_union_width=args.max_union_width,
                                    max_degree=args.max_degree)
        print(json.dumps(result, indent=2))
        return 0 if result['status'] == 'UNSAT' else 2
    except (OSError, KeyError, TypeError, ValueError) as exc:
        print('Invalid input:', exc, file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
