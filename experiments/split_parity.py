"""Common affine consequences from two cases, and a whole 3-SAT image invisible to this pass."""
import argparse
import json
from pathlib import Path
from pnp_lab.split_parity import split_parity_refute,check_split_parity
from pnp_lab.transport_obstruction import switch_tseitin
from pnp_lab.private_resolution import private_parity_refute
from pnp_lab.simple_support import simple_support_image,forcing_models


def run():
    controls=[]
    for k in (1,2,4,16,64,128):
        for odd in (True,False):
            n,cs=switch_tseitin(k,odd=odd)
            r=split_parity_refute(n,cs)
            assert r['status']==('UNSAT' if odd else 'UNKNOWN')
            if odd: assert check_split_parity(n,cs,r['certificate'])
            c=dict(k=k,variables=n,clauses=len(cs),odd=odd,status=r['status'],
                   terms=len((r['certificate'] or {}).get('terms',[])),stats=r['stats'])
            # Raw JSON proof for the smallest hard case; regenerate larger ones via the API.
            if k==1 and odd:c['certificate']=r['certificate']
            controls.append(c)
    blind=[]
    for k in (1,2,4):
        for odd in (True,False):
            n,cs=switch_tseitin(k,odd=odd)
            m,qs,_=simple_support_image(n,cs)
            r=split_parity_refute(m,qs)
            assert len({frozenset(map(abs,c)) for c in qs})==len(qs)
            assert r['status']=='UNKNOWN' and r['stats']['base_rows']==r['stats']['common_rows']==0
            p=private_parity_refute(m,qs)
            assert p['status']=='UNKNOWN' and p['stats']['resolvents_added']==0
            blind.append(dict(k=k,odd=odd,n=m,clauses=len(qs),stats=r['stats'],status=r['status'],
                              private_resolvents_added=p['stats']['resolvents_added']))
    last=next(c for c in controls if c['k']==128 and c['odd'])
    return dict(schema_version=1,all_checks_passed=True,ordinary=controls,simple_support_images=blind,
                summary=dict(largest_k=128,largest_variables=last['variables'],largest_clauses=last['clauses'],
                             largest_checked_certificate_terms=last['terms'],simple_support_controls=len(blind),
                             forcing_models=forcing_models()),
                scope='A polynomial one-pass UNSAT refuter; absence of discovered rows is not SAT.')


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--out-dir',type=Path,required=True)
    out=p.parse_args().out_dir;out.mkdir(exist_ok=True,parents=True)
    data=run()
    (out/'split_parity.json').write_text(json.dumps(data,sort_keys=True,indent=2)+'\n')
    print(data['summary'])
