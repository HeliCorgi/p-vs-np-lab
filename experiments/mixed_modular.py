"""Shared Boolean ports: exact cross-field refutations, and independently lifted controls."""
import argparse,json
from pathlib import Path
from itertools import product
from pnp_lab.ternary_flow import mixed_port_flow,mixed_port_witness,mixed_half_witness,scramble
from pnp_lab.four_ports import four_port_flow,four_port_word,alternating_flow
from pnp_lab.mixed_modular import mixed_modular_refute,check_field_bridge
from pnp_lab.modular_hull import modular_hull_refute


def holds(f,x):
    return all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in c) for c in f)


def run():
    cases=[];products=[];sample=None
    for w in (3,4):
        for k in (4,7,12):
            for bad in (False,True):
                rhs=2 if bad else 1
                if w==3:
                    n,f,ports,meta=mixed_port_flow(k,ternary_rhs=rhs)
                    witness=mixed_port_witness(k,(1,0,0),ternary_rhs=rhs)
                else:
                    n,f,meta=four_port_flow(k,ternary_rhs=rhs)
                    witness=four_port_word(k,(1,0,0,0),ternary_rhs=rhs)
                raw,word=scramble(n,f,witness,1403197+k*w)
                if not bad:assert word is not None and holds(raw,word)
                singles=[modular_hull_refute(n,raw,prime=p)['status'] for p in (2,3)]
                assert singles==['UNKNOWN','UNKNOWN']
                small=mixed_modular_refute(n,raw,bridge_width=w-1)
                wide=mixed_modular_refute(n,raw,bridge_width=w)
                assert small['status']=='UNKNOWN'
                assert wide['status']==('UNSAT' if bad else 'UNKNOWN')
                if bad:
                    assert check_field_bridge(n,raw,wide['certificate'])
                    if w==3 and k==4:sample=wide['certificate']
                stats=wide['stats'];cert=wide['certificate'] or {}
                cases.append(dict(ports=w,k=k,variables=n,clauses=len(raw),bad=bad,fields=singles,
                    checked_sat_word=not bad,smaller_width=w-1,smaller_pass=small['status'],
                    bridge=wide['status'],transfers=stats['transfer_widths'],nodes=len(cert.get('nodes',[])),
                    short_rows_checked=stats['short_rows_checked']))
    for bits in product(range(2),repeat=3):
        k=4;n,f,ports,meta=mixed_port_flow(k)
        vals=[]
        for p,r,name in ((2,1,'binary'),(3,2,'ternary')):
            model=mixed_half_witness(k,bits,prime=p,rhs=r)
            if model is not None:assert holds(meta[name],model)
            vals.append(model is not None)
        assert vals==[sum(bits)%2==1,sum(bits)%3==2] and not all(vals)
        products.append(dict(bits=bits,binary=vals[0],ternary=vals[1]))
    alternating=[]
    for demand in (0,1):
        n,f,word=alternating_flow(5,total=demand);f,word=scramble(n,f,word,144819)
        r=mixed_modular_refute(n,f)
        assert r['status']==('UNSAT' if demand else 'UNKNOWN')
        if demand:
            assert check_field_bridge(n,f,r['certificate']) and r['stats']['rounds']>=2
            forms=set()
            tags=[a['p'] for a in r['certificate']['nodes']]
            for node in r['certificate']['nodes']:
                if node['op']=='boolean':forms.add((tags[node['from']],node['p']))
            assert forms=={(2,3),(3,2)}
        else:assert word is not None and holds(f,word)
        alternating.append(dict(total=demand,variables=n,clauses=len(f),status=r['status'],
            checked_sat_word=not demand,rounds=r['stats']['rounds'],
            proof_nodes=len((r['certificate'] or {}).get('nodes',[])),transfers=r['stats']['transfer_widths']))
    return dict(schema_version=1,all_checks_passed=True,controls=cases,port_table=products,alternating=alternating,
            sample_certificate=sample,sample_input='mixed_port_flow(4), ternary_rhs=2; scramble seed 1403209',
            summary=dict(cases=len(cases),refutations=sum(c['bridge']=='UNSAT' for c in cases),
                         checked_positive_controls=sum(c['checked_sat_word'] for c in cases),
                         single_field_runs=2*len(cases),largest_k=12,bridge_widths=[3,4],alternating_unsat_rounds=alternating[-1]['rounds']),
            scope='Short-row widths are not input size. Matching witnesses are checked on the raw scrambled CNF; UNKNOWN alone does not certify SAT.')

if __name__=='__main__':
    a=argparse.ArgumentParser();a.add_argument('--out-dir',type=Path,required=True)
    out=a.parse_args().out_dir;out.mkdir(exist_ok=True,parents=True)
    r=run();(out/'mixed_modular.json').write_text(json.dumps(r,sort_keys=True,indent=2)+'\n');print(r['summary'])
