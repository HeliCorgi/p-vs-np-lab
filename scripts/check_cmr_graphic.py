#!/usr/bin/env python3
"""Run named integration checks against a real cmr-graphic executable."""
import argparse
from functools import reduce
import json
from operator import xor
from pathlib import Path
import sys

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'src'))
from pnp_lab.cmr_graphic import CMR_COMMIT, decide_with_cmr
from pnp_lab.graphic_support import verify_graphic_certificate
from pnp_lab.ternary_support import three_cnf_to_weight_two_supports


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--executable',required=True)
    a=p.parse_args()
    report=[]
    def case(name,groups,rhs,status,reason=None):
        r=decide_with_cmr(groups,rhs,executable=a.executable)
        if r['status'] != status or (reason and r['reason'] != reason):
            raise RuntimeError(f'{name}: wanted {status}/{reason}, got {r}')
        if status!='UNKNOWN':
            verify_graphic_certificate(groups,r['certificate'])
        if status=='SAT' and (reduce(xor,r['witness'],0)!=rhs or
                              any(v not in g for v,g in zip(r['witness'],groups))):
            raise RuntimeError('Bad original-mask witness')
        report.append(dict(case=name,status=status,reason=r['reason'],cmr=r['cmr']))
        return r
    # A dense invertible embedding of all pair differences of 5 points, with
    # affine offsets; a disconnected direct summand is also present.
    points=(0,7,56,448,3584)
    groups=[tuple((1<<20)^points[k] for k in (i,j,l))
            for i in range(5) for j in range(i+1,5) for l in range(j+1,5)]
    groups.append((0,1<<21))
    rhs=reduce(xor,(s[-1] for s in groups),0)
    case('dense K5 and a coloop',groups,rhs,'SAT')
    case('triangle: target inside hull but not a choice',[(0,7,56)],63,'UNSAT')
    # Fano plus an independent coloop, so simple global edge count does not exclude it.
    case('Fano restriction: failure of recognition is not UNSAT',[(0,i) for i in range(1,9)],
         0,'UNKNOWN','cmr_reports_nongraphic')
    signed = three_cnf_to_weight_two_supports(('a','b','c'),[(-1,2,-3)])
    valid = case('signed 3SAT encoding',signed.supports,0,'SAT')
    source = signed.project_witness(valid['witness'])
    if not (not (source&1) or source&2 or not (source&4)):
        raise RuntimeError('Signed source witness failed')
    # Actual 3SAT image whose direct difference system has a Fano minor.
    obstruction=three_cnf_to_weight_two_supports(('x',),[(1,1,1)])
    case('satisfiable sparse source with nongraphic differences',obstruction.supports,0,
         'UNKNOWN','cmr_reports_nongraphic')
    print(json.dumps(dict(compatibility_commit=CMR_COMMIT,checks=report,passed=True),indent=2))
    print(f'PASS {len(report)} CMR integration cases')

if __name__=='__main__':
    main()
