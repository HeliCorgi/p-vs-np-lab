#!/usr/bin/env python3
"""Solve a raw JSON 3-CNF with checked implication-to-arithmetic feedback."""
import argparse
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'src'))
from pnp_lab.feedback_witness import check_feedback_witness, feedback_witness
from pnp_lab.integer_feedback import check_integer_feedback, integer_feedback_refute
from pnp_lab.field_split import KIND as SPLIT_KIND, check_field_split, field_split_refute
from pnp_lab.modular_hull import _input


def decide(n, cs, *, method='auto', max_edges=None, family_budget=False):
    if method not in ('auto', 'witness', 'refute', 'split'):
        raise ValueError('unknown method')
    cs = _input(n, cs)
    if method == 'split':
        if max_edges is not None:
            raise ValueError('--max-edges is for the path solver, not the separator search')
        return field_split_refute(n, cs, max_candidates=n if family_budget else 32)
    m = len(cs)
    limits = dict(max_edges=(2*m if family_budget else 1000000) if max_edges is None else max_edges)
    model_limits = {}
    if family_budget:
        limits.update(max_lemmas=m,max_path_steps=m)
        model_limits.update(max_active=n,max_word_bits=n,max_clauses=m)
    if method in ('auto', 'witness'):
        initial = feedback_witness(n, cs, **model_limits, **limits)
        if initial['status'] == 'SAT':
            initial['witness_hex'] = hex(initial.pop('witness'))
            return initial
        if method == 'witness':
            return initial
    ans = integer_feedback_refute(n, cs, **limits)
    if method == 'auto':
        ans['stats']['preceding_witness_attempt'] = initial['stats']
        ans['stats']['preceding_witness_reason'] = initial['reason']
    return ans


def verify(n, cs, report):
    if not isinstance(report, dict):
        return False
    if report.get('status') == 'UNSAT':
        cert = report.get('certificate')
        if isinstance(cert, dict) and cert.get('kind') == SPLIT_KIND:
            return check_field_split(n, cs, cert)
        return check_integer_feedback(n, cs, report.get('certificate'))
    word = report.get('witness_hex')
    if (report.get('status') == 'SAT' and isinstance(word, str)
            and word.startswith('0x') and 0 < len(word)-2 <= max(1, (n+3)//4)
            and all(c in '0123456789abcdef' for c in word[2:])):
        return check_feedback_witness(n, cs, int(word[2:], 16))
    return False


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    parser.add_argument('--method', choices=['auto','witness','refute','split'], default='auto')
    parser.add_argument('--max-edges', type=int, help='override the edge-visit budget per stage')
    parser.add_argument('--family-budget', action='store_true',
                        help='scale path and witness limits to the input as in the shielded Tseitin theorem')
    parser.add_argument('--check', metavar='REPORT', help='independent replay; - reads stdin')
    args = parser.parse_args()
    try:
        data = json.loads(args.input.read_text())
        names, cs = data['variables'], data['clauses']
        if (not isinstance(names, list) or not all(type(v) is str and v for v in names)
                or len(set(names)) != len(names) or not isinstance(cs, list)):
            raise ValueError('expected distinct variable names and a clause list')
        if args.check:
            report = json.loads(sys.stdin.read() if args.check == '-' else Path(args.check).read_text())
            if verify(len(names), cs, report):
                print('VERIFIED: original CNF is ' + report['status'])
                return 0
            print('REJECTED')
            return 1
        report = decide(len(names), cs, method=args.method, max_edges=args.max_edges,
                        family_budget=args.family_budget)
        print(json.dumps(report, indent=2))
        return 2 if report['status'] == 'UNKNOWN' else 0
    except (KeyError, OSError, ValueError, TypeError) as exc:
        print('Invalid input:', exc, file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
