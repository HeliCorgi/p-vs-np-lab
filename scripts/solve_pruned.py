#!/usr/bin/env python3
"""Decide a signed 3-CNF using the global frontier; 0 decided, 2 UNKNOWN, 1 error."""
import argparse
import json
from pathlib import Path
import sys

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'src'))
from pnp_lab.decision_pruning import solve_pruned


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('input',help="JSON with variables/clauses, or '-' for stdin")
    p.add_argument('--label',choices=('affine','syntax','blocked'),default='affine')
    p.add_argument('--transport',action='store_true',help='Prune by checked directed witness maps')
    p.add_argument('--transport-trace',action='store_true',help='Include maps and both residuals (requires --transport)')
    p.add_argument('--max-transport-checks',type=int,help='Total directed finder attempts; exhaustion keeps both branches')
    p.add_argument('--derived-depth',type=int,choices=range(4),help='Verify witness maps using propagation and at most this many nested decisions')
    p.add_argument('--max-proof-nodes',type=int,help='Total propagation nodes across all map searches')
    p.add_argument('--max-proof-queries',type=int,help='Total nonsyntactic clause queries across all map searches')
    root=p.add_mutually_exclusive_group()
    root.add_argument('--case-parity',action='store_true',help='Try both values of one pivot using private resolution and parity in each case')
    root.add_argument('--recover-case-parity',action='store_true',help='Certify a reduced core, then try both parity cases there')
    root.add_argument('--recover-parity',action='store_true',help='First certify a reduced core and try its root parity refutation')
    root.add_argument('--private-parity',action='store_true',help='Add short private-pivot resolvents before seeking a root parity refutation')
    root.add_argument('--split-parity',action='store_true',help='First seek a checked common-parity contradiction at the root')
    g=p.add_mutually_exclusive_group()
    g.add_argument('--max-width',type=int,default=64)
    g.add_argument('--unbounded',action='store_true')
    args=p.parse_args()
    try:
        data=json.loads(sys.stdin.read() if args.input=='-' else Path(args.input).read_text())
        vs,cs=data['variables'],data['clauses']
        if (not isinstance(vs,list) or not isinstance(cs,list) or
                not all(type(v) is str and v for v in vs) or len(set(vs))!=len(vs)):
            raise ValueError('Expected distinct variable names and a clause list.')
        out=solve_pruned(len(vs),cs,max_width=None if args.unbounded else args.max_width,
                         label_mode=args.label,transport=args.transport,transport_trace=args.transport_trace,
                         max_transport_checks=args.max_transport_checks,split_parity=args.split_parity,private_parity=args.private_parity,
                         derived_depth=args.derived_depth,max_proof_nodes=args.max_proof_nodes,
                         max_proof_queries=args.max_proof_queries,recover_parity=args.recover_parity,
                         case_parity=args.case_parity,recover_case_parity=args.recover_case_parity)
    except (ValueError,TypeError,KeyError,OSError) as e:
        print('Input error:',e,file=sys.stderr);return 1
    print(json.dumps(out,indent=2))
    return 2 if out['status']=='UNKNOWN' else 0

if __name__=='__main__':sys.exit(main())
