#!/usr/bin/env python3
"""Replay a root parity UNSAT proof against the named original JSON input."""
import argparse
import json
from pathlib import Path
import sys

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'src'))
from pnp_lab.case_parity import check_case_parity
from pnp_lab.recovered_parity import check_recovered_parity
from pnp_lab.private_resolution import check_private_parity
from pnp_lab.split_parity import check_split_parity


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('input');p.add_argument('report',help="solve_pruned JSON output; - reads stdin")
    args=p.parse_args()
    try:
        src=json.loads(Path(args.input).read_text())
        report=json.loads(sys.stdin.read() if args.report=='-' else Path(args.report).read_text())
        which,checker=next((key,func) for key,func in [('root_private_parity',check_private_parity),
            ('root_recovered_parity',check_recovered_parity),('root_case_parity',check_case_parity),('root_split_parity',check_split_parity)] if key in report)
        ok=report['status']=='UNSAT' and checker(len(src['variables']),src['clauses'],report[which]['certificate'])
    except (StopIteration,AttributeError,ValueError,OSError,TypeError,KeyError) as e:
        print('Invalid input:',e,file=sys.stderr);return 1
    print('VERIFIED: original CNF is UNSAT' if ok else 'REJECTED')
    return 0 if ok else 1

if __name__=='__main__':sys.exit(main())
