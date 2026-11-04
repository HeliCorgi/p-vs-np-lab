"""Recover rank-drop primes from the original clauses, including an unanticipated 5."""
import argparse,json
from itertools import combinations,product
from pathlib import Path
from pnp_lab.prime_spectrum import check_local_spectrum,discover_prime_spectrum,spectrum_table
from pnp_lab.ternary_flow import prism_flow,scramble
from pnp_lab.modular_hull import modular_hull_refute,check_modular_hull


def odd_inequalities(k):
    return tuple(c for i in range(k) for c in ((i+1,(i+1)%k+1),(-i-1,-((i+1)%k+1))))


def five_fixture():
    d=7;words=(1,6,26,39,61,72,83,112);cs=[]
    for vs in combinations(range(d),3):
        permitted={tuple(w>>j&1 for j in vs) for w in words}
        for pat in product((0,1),repeat=3):
            if pat not in permitted:cs.append(tuple((j+1)*(-1 if bit else 1) for j,bit in zip(vs,pat)))
    return d,tuple(cs),words


def run():
    cases=[]
    for p in (2,3):
        for k in (3,16,64):
            for bad in (False,True):
                n,cs,w=prism_flow(k,bad,modulus=p)
                raw,_=scramble(n,cs,w,1417+k)
                z=discover_prime_spectrum(n,raw)
                assert z['primes']==[p] and not z['empty_scopes'] and z['complete_for_scopes']
                cert=z['examples'][str(p)]
                assert check_local_spectrum(n,raw,cert['scope'],cert['profile'])
                # Detect before running the backend. Its UNSAT proof is entirely
                # separate from the positive rank witness on a single local set.
                h=modular_hull_refute(n,raw,prime=z['primes'][0])
                assert h['status']==('UNSAT' if bad else 'UNKNOWN')
                if bad:assert check_modular_hull(n,raw,h['certificate'])
                row=dict(k=k,variables=n,clauses=len(raw),unbalanced=bad,observed_primes=z['primes'],
                         rank_drop_scopes=z['exceptional_scope_counts'][str(p)],total_scopes=z['scanned_scopes'],
                         subsequent_status=h['status'])
                if k==3:row['example']=cert
                cases.append(row)
    k=11;cs=odd_inequalities(k)
    cycle=discover_prime_spectrum(k,cs)
    h=modular_hull_refute(k,cs,prime=2)
    assert cycle['primes']==[] and h['status']=='UNSAT' and check_modular_hull(k,cs,h['certificate'])
    n,f,words=five_fixture(); prof=spectrum_table(n,sum(1<<w for w in words))
    assert check_local_spectrum(n,f,list(range(1,n+1)),prof)
    z=discover_prime_spectrum(n,f)
    assert z['primes']==prof['exceptional_primes']==[2,5]
    spur=spectrum_table(3,(1<<3)|(1<<5)|(1<<6))
    assert spur['rational']['minor']==-2 and spur['modular']['2']['minor']==-1 and not spur['exceptional_primes']
    return dict(schema_version=1,all_checks_passed=True,prism=cases,odd_cycle=dict(length=k,
                    discovered=cycle['primes'],fallback_status=h['status'],scopes=cycle['scanned_scopes']),
                five_fixture=dict(variables=n,clauses=len(f),word_set=list(words),profile=prof),
                spurious_minor_control=spur,
                summary=dict(scrambled_field_controls=len(cases),largest_prism=k_max(cases),
                        highest_recovered_test_prime=5,odd_cycle_length=k,
                        largest_scanned_scopes=max(q['total_scopes'] for q in cases)),
                scope='Exact exceptional characteristics per scanned local relation. Not a complete list of global refutation characteristics or a SAT inference.')


def k_max(cases):return max(q['k'] for q in cases)


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--out-dir',type=Path,required=True)
    d=p.parse_args().out_dir;d.mkdir(parents=True,exist_ok=True);q=run()
    (d/'prime_spectrum.json').write_text(json.dumps(q,sort_keys=True,indent=2)+'\n')
    print(q['summary'])
