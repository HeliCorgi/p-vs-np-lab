#!/usr/bin/env python3
"""Reproduce upper and lower static degrees for the strict selector cube cover."""
import argparse
from functools import reduce
from itertools import combinations, product
import json
from operator import xor
from pathlib import Path
import random

from pnp_lab.overlap_lattice import solve_affine_arrangement
from pnp_lab.overlap_refutation import refute_affine_cover, verify_cover_certificate
from pnp_lab.selector_events import (CompactEncoding, ParsimoniousEncoding, compile_compact_events,
                                     compile_parsimonious_events, compile_selector_events)


def require(ok, label):
    if not ok:
        raise AssertionError(label)


def _models(n, clauses):
    return [s for s in range(1<<n)
            if all(any(((s>>(abs(k)-1))&1)==(k>0) for k in cl) for cl in clauses)]


def _weighted(s, enc):
    """Independent local combinatorics: t one-hot vs 2^(t-1) odd selections."""
    total=1
    for cl in enc.padded_cnf:
        t=sum(((s>>(abs(k)-1))&1)==(k>0) for k in cl)
        if t==0: return 0
        if isinstance(enc,CompactEncoding):
            # Both z bits are free iff neither of the first two gates fires.
            total*=1+int(all(((s>>(abs(k)-1))&1)==(k>0) for k in cl[:2]))
        elif not isinstance(enc,ParsimoniousEncoding):
            total*=t if enc.strict else 1<<(t-1)
    return total


def _prod(a,b):
    p=set()
    for x in a:
        for y in b:
            p.symmetric_difference_update((x|y,))
    return p


def _raw_indicator(event):
    p={0}
    for mask, rhs in event:
        bits={1<<i for i in range(mask.bit_length()) if mask & (1<<i)}
        if not rhs: bits.add(0)
        p=_prod(p,bits)
    return p


def _falsity(lit):
    var=1<<(abs(lit)-1)
    return {var,0} if lit>0 else {var}


def explicit_cube_proof(enc):
    """sum_C L_C=1; expand f_j f_k times each raw occurrence indicator."""
    terms=[]
    for cl,ids in zip(enc.padded_cnf,enc.occurrence_event_ids):
        for j,e in enumerate(ids):
            h=_prod(_falsity(cl[(j+1)%3]),_falsity(cl[(j+2)%3]))
            terms.extend([e,mon] for mon in sorted(h))
    cert={'kind':'gf2-affine-cover-static-v1','n':enc.n_parameters,'degree':4,'terms':terms}
    verify_cover_certificate(enc.n_parameters,enc.events,cert,max_degree=4)
    return cert


def _cubic_rows(enc):
    # Every cube event uses exactly two independent rows, so the ONLY static
    # multipliers in degree <=3 are 1 and the n coordinate bits.
    for ev in enc.events:
        require(len(ev)==2 and ev[0][0]!=ev[1][0] and all(m for m,b in ev),'rank-two premise')
        indicator=_raw_indicator(ev)
        for m in (0,*(1<<i for i in range(enc.n_parameters))):
            yield _prod({m},indicator)


def cubic_separator(enc):
    # Produce the dual independently of the refutation generator. Use fixed
    # graded columns, not the detector's on-demand monomial ordering.
    n=enc.n_parameters
    mons=[sum(1<<i for i in a) for k in range(4) for a in combinations(range(n),k)]
    pos={m:i for i,m in enumerate(mons)}
    echelon={}
    for row in _cubic_rows(enc):
        v=sum(1<<pos[m] for m in row)
        while v:
            j=v.bit_length()-1
            if j not in echelon:
                echelon[j]=v;break
            v^=echelon[j]
    require(0 not in echelon,'constant missing from degree-three row span')
    f=1
    for j,v in sorted(echelon.items()):
        if (v&f).bit_count()%2:f|=1<<j
    return {'kind':'gf2-static-cube-dual-degree3-v1','n':n,'degree':3,
            'ones':[m for j,m in enumerate(mons) if f & (1<<j)],'row_rank':len(echelon)}


def verify_cubic_separator(enc, separator):
    # The preceding elimination (including claimed rank) is not needed by
    # this check. L(1)=1 and L(row)=0 for all candidate rows is sufficient.
    ones=set(separator['ones']);n=enc.n_parameters
    if (0 not in ones or len(ones)!=len(separator['ones']) or separator['degree']!=3
            or separator['n']!=n or any(type(m) is not int or not 0<=m<1<<n or m.bit_count()>3 for m in ones)):
        raise ValueError('Invalid degree-three separator')
    tested=0
    for row in _cubic_rows(enc):
        if len(ones & row)%2: raise ValueError('Separator fails an allowed multiplier row')
        tested+=1
    return tested


def arrangement_record(enc):
    n=len(enc.original_variables)
    a=solve_affine_arrangement(enc.n_parameters,enc.events,condition_on=tuple(1<<i for i in range(n)),
                               max_intersections=100000,max_slices=1<<n)
    models=_models(n,enc.original_cnf)
    mass=sum(_weighted(s,enc) for s in range(1<<n))
    require(a['survivor_count']==mass and a['status']==('SAT' if models else 'UNSAT'),'slice oracle')
    source_witness=None if a['witness'] is None else enc.project_witness(a['witness'])
    require((not models and source_witness is None) or source_witness in models,'projected witness')
    return {'source_model_count':len(models),'parameter_survivors':mass,'parameter_bits':enc.n_parameters,
            'parameter_witness':a['witness'],'source_witness':source_witness,'conditioned_source_bits':n,
            **{k:a[k] for k in ('status','slices_total','slices_completed','intersections_tested','peak_terms')}}


def small_oracle():
    rng=random.Random(943065)
    cases=[(0,()),(0,((),)),(1,((1,),)),(1,((1,),(-1,))), (3,((1,-1),(-2,2))),
           (3,((3,-2,3),(-3,2,-1))),(3,((1,1,1),)),(3,((),(1,2,3)))]
    for _ in range(32):
        n=rng.randrange(1,4)
        clauses=[tuple(rng.choice((-1,1))*rng.randrange(1,n+1) for _ in range(rng.randrange(1,4)))
                 for _ in range(rng.randrange(1,4))]
        cases.append((n,tuple(clauses)))
    raw_points=lifts=0
    for n,cs in cases:
        ns=tuple(map(str,range(n)))
        for enc in (compile_selector_events(ns,cs,strict=True),compile_selector_events(ns,cs,strict=False),
                    compile_compact_events(ns,cs),compile_parsimonious_events(ns,cs)):
            masses=[0]*(1<<n)
            for s in range(1<<enc.n_parameters):
                if not any(all(((s&m).bit_count()&1)==r for m,r in evt) for evt in enc.events):
                    masses[enc.project_witness(s)]+=1
            raw_points+=1<<enc.n_parameters
            require(masses==[_weighted(i,enc) for i in range(1<<n)],'per-source multiplicities')
            models=_models(n,cs)
            for s in models:
                require(enc.project_witness(enc.lift_witness(s))==s,'lift/project')
            lifts+=len(models)
            got=arrangement_record(enc)
            require(got['parameter_survivors']==sum(masses),'raw arrangement')
    return {'formulas':len(cases),'modes_per_formula':4,'raw_parameter_assignments_checked':raw_points,
            'source_model_roundtrips_across_modes':lifts}


def run_experiment():
    cube=tuple(tuple((j+1)*z for j,z in enumerate(s)) for s in product((-1,1),repeat=3))
    names=('x','y','z');modes={}
    for strict in (True,False):
        e=compile_selector_events(names,cube,strict=strict);near=compile_selector_events(names,cube[:-1],strict=strict)
        lower=cubic_separator(e);rows=verify_cubic_separator(e,lower);explicit=explicit_cube_proof(e)
        found=[]
        for d in (2,3,4):
            out=refute_affine_cover(e.n_parameters,e.events,degree=d)
            require(out['status']==('UNSAT' if d==4 else 'UNKNOWN'),'cube static degree')
            found.append({k:out[k] for k in ('degree_limit','status','rows_generated','basis_rank','columns_seen')})
            if out['certificate'] is not None:
                verify_cover_certificate(e.n_parameters,e.events,out['certificate'])
                found[-1]['terms_in_discovered_proof']=len(out['certificate']['terms'])
        nr=arrangement_record(near);cr=arrangement_record(e)
        require(nr['source_model_count']==1 and nr['parameter_survivors']==(24 if strict else 32),'near miss counts')
        # A SAT witness forbids every degree refutation. A capped search's
        # UNKNOWN alone is not used to classify this control as SAT.
        no=refute_affine_cover(near.n_parameters,near.events,degree=4,max_rows=80)
        require(no['status']=='UNKNOWN','SAT control not refuted')
        modes['strict' if strict else 'relaxed']={'cube':cr,'near_miss':nr,'events_in_cube':len(e.events),
            'bounded_search':found,'dual_separator':lower,'separator_rows_checked':rows,
            'explicit_certificate':explicit,'explicit_certificate_utf8_bytes':len(json.dumps(explicit,separators=(',',':')).encode()),
            'occurrence_terms_in_explicit_proof':len(explicit['terms'])}
    aux_modes={}
    for mode,compiler in [('two_event',compile_compact_events),('parsimonious',compile_parsimonious_events)]:
        enc=compiler(names,cube);near=compiler(names,cube[:-1]);terms=[]
        for cl,ids in zip(enc.padded_cnf,enc.per_clause_event_ids):
            if mode=='two_event':
                polys=(_falsity(cl[1]),_falsity(cl[0]))
            else:
                polys=(_falsity(cl[2]),_falsity(cl[2]),{0})
            for i,poly in zip(ids,polys):terms.extend([i,x] for x in sorted(poly))
        cert={'kind':'gf2-affine-cover-static-v1','n':enc.n_parameters,'degree':3,'terms':terms}
        verify_cover_certificate(enc.n_parameters,enc.events,cert,max_degree=3)
        degrees=[]
        for d in (2,3):
            rr=refute_affine_cover(enc.n_parameters,enc.events,degree=d)
            require(rr['status']==('UNSAT' if d==3 else 'UNKNOWN'),'one-auxiliary degree')
            degrees.append({k:rr[k] for k in ('status','rows_generated','basis_rank','degree_limit')})
        cc=arrangement_record(enc);nn=arrangement_record(near)
        require(nn['parameter_survivors']==(4 if mode=='two_event' else 1),'compact near miss')
        aux_modes[mode]={'cube':cc,'near_miss':nn,'explicit_certificate':cert,'events_in_cube':len(enc.events),
                         'minimal_static_degree_on_cube':3,'bounded_search':degrees,
                         'explicit_certificate_utf8_bytes':len(json.dumps(cert,separators=(',',':')).encode())}
    controls=small_oracle()
    return {'schema_version':1,'all_checks_passed':True,'source_variables':names,'cube_source_cnf':cube,
            'near_miss':'remove last (+++) clause; the unique source model is mask zero',
            'modes':modes,'one_auxiliary_modes':aux_modes,'controls':controls,'scope':'Static degree uses rank(event)+squarefree multiplier weight. Counts are parameter witnesses; no general polynomial decider is claimed. Timings are not mixed into deterministic work counters.',
            'summary':{'cube_parameter_bits':19,'cube_parameter_survivors':0,'minimal_static_degree':4,
                       'explicit_certificate_terms':len(modes['strict']['explicit_certificate']['terms']),
                       'degree_three_dual_nonzeros':len(modes['strict']['dual_separator']['ones']),
                       'degree_three_rows_checked':modes['strict']['separator_rows_checked'],
                       'near_miss_strict_survivors':24,'near_miss_relaxed_survivors':32,
                       'near_miss_two_event_survivors':4,'near_miss_parsimonious_survivors':1,
                       'two_event_cube_bits':11,'two_event_cube_events':16,'two_event_cube_min_static_degree':3,
                       'two_event_cube_certificate_terms':24,'parsimonious_cube_certificate_terms':32,**controls}}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--out-dir',type=Path,required=True)
    out=p.parse_args().out_dir;out.mkdir(parents=True,exist_ok=True)
    report=run_experiment()
    (out/'selector_overlap.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(json.dumps(report['summary'],sort_keys=True))


if __name__=='__main__':main()
