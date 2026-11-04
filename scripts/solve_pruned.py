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
                         label_mode=args.label)
    except (ValueError,TypeError,KeyError,OSError) as e:
        print('Input error:',e,file=sys.stderr);return 1
    print(json.dumps(out,indent=2))
    return 2 if out['status']=='UNKNOWN' else 0

if __name__=='__main__':sys.exit(main())
