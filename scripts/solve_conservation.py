#!/usr/bin/env python3
"""Solve or independently replay a conservation certificate against the original JSON 3-CNF."""
import argparse,json,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'src'))
from pnp_lab.conservation import solve_conservation,check_conservation
from pnp_lab.local_torsion import scan_local_torsion
from pnp_lab.prime_spectrum import discover_prime_spectrum


def main():
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument('input')
    cli.add_argument('--method',choices=('auto','hull2','hull3','mixed','trit','cyclic4','integer','integer-probe','spectrum','torsion'),default='auto')
    cli.add_argument('--bridge-width',type=int,choices=range(5),default=3)
    cli.add_argument('--max-probes',type=int,help='Cap signature probes of mixed inference only')
    cli.add_argument('--max-short-rows',type=int,help='Cap short-row visits of mixed inference only')
    cli.add_argument('--integer-call-cap',type=int,default=32,
                     help='Cap integer-oracle calls for --method integer-probe (default: 32)')
    cli.add_argument('--check',metavar='REPORT',help='Replay a SAT/UNSAT report; - means read report from stdin')
    args=cli.parse_args()
    try:
        src=json.loads(Path(args.input).read_text());vs,cs=src['variables'],src['clauses']
        if not isinstance(vs,list) or not all(type(v) is str and v for v in vs) or len(set(vs))!=len(vs) or not isinstance(cs,list):
            raise ValueError('expected distinct variable names and a clause list')
        if args.check:
            r=json.loads(sys.stdin.read() if args.check=='-' else Path(args.check).read_text())
            ok=check_conservation(len(vs),cs,r)
            print('VERIFIED: original CNF is '+r['status'] if ok else 'REJECTED')
            return 0 if ok else 1
        if args.method in ('spectrum','torsion'):
            scan=discover_prime_spectrum if args.method=='spectrum' else scan_local_torsion
            print(json.dumps(scan(len(vs),cs),indent=2));return 0
        r=solve_conservation(len(vs),cs,method=args.method,bridge_width=args.bridge_width,
                             max_probes=args.max_probes,max_short_rows=args.max_short_rows,
                             max_integer_calls=args.integer_call_cap)
        print(json.dumps(r,indent=2));return 2 if r['status']=='UNKNOWN' else 0
    except (OSError,KeyError,TypeError,ValueError) as exc:
        print('Invalid input:',exc,file=sys.stderr);return 1
if __name__=='__main__': sys.exit(main())
