"""Exact complement of a union of affine subspaces of F_2^n.

An event is a conjunction of (linear mask, parity) rows. An empty event
forbids everything. Counts/witnesses concern the original n-bit parameters.
The signed dictionary is exact, but may grow exponentially.
"""
from __future__ import annotations


def _rref(rows):
    """Canonical equations, with RHS packed in bit zero; None = inconsistent."""
    pivots = {}
    for x in rows:
        while x > 1:
            p = x.bit_length()-1
            if p not in pivots:
                pivots[p] = x
                break
            x ^= pivots[p]
        if x == 1:
            return None
    order = sorted(pivots)
    for j,p in enumerate(order):
        for q in order[j+1:]:
            if pivots[q] >> p & 1:
                pivots[q] ^= pivots[p]
    return tuple(pivots[p] for p in reversed(order))


def _reduce(x, equations):
    for row in equations:  # high pivots first
        if x >> (row.bit_length()-1) & 1:
            x ^= row
    return x


def _mass(n, terms):
    return sum(c << (n-len(system)) for system,c in terms.items())


def _point(system):
    # Free parameters zero. RREF ensures no other pivot appears in a row.
    return sum(1 << (r.bit_length()-2) for r in system if r & 1)


def _trim(events):
    # In an increasing-rank ordering, a later affine flat can only be a
    # strict subset, not a strict superset, of an earlier one.
    result = []
    for s in sorted(set(events), key=lambda v:(len(v),v)):
        if not any(all(_reduce(row,s)==0 for row in larger) for larger in result):
            result.append(s)
    return result


def _independent_masks(vectors):
    rows = {}; originals = []; codes = {}
    for m in sorted(set(vectors),key=lambda x:(x.bit_count(), x)):
        x,code=m,0
        while x:
            p=x.bit_length()-1
            if p not in rows:
                new=1 << len(originals)
                rows[p]=(x,code^new); originals.append(m); code=new
                break
            row,tag=rows[p];x^=row;code^=tag
        codes[m]=code
    return originals,codes


def _indices(bits):
    while bits:
        b=bits&-bits;yield b.bit_length()-1;bits^=b


def _components(events):
    # Coordinates are values of independent LINEAR OBSERVATIONS, not
    # necessarily individual original bits. Join all basis indices that
    # affect a single event; resulting observation blocks are independent.
    originals,codes=_independent_masks(row>>1 for e in events for row in e)
    parent=list(range(len(originals)))
    def find(a):
        while a!=parent[a]:
            parent[a]=parent[parent[a]];a=parent[a]
        return a
    indexed=[]
    for e in events:
        rows=[(codes[row>>1], row&1) for row in e]
        used=0
        for code,_ in rows:used|=code
        ids=list(_indices(used)); pivot=find(ids[0])
        for i in ids[1:]:parent[find(i)]=pivot
        indexed.append((ids[0],rows))
    blocks={}
    for i in range(len(originals)):
        blocks.setdefault(find(i),[]).append(i)
    remap={i:loc for ids in blocks.values() for loc,i in enumerate(ids)}
    by_block={root:[] for root in blocks}
    for i,eqs in indexed:
        rows=[(sum(1<<remap[k] for k in _indices(code))<<1)|rhs for code,rhs in eqs]
        by_block[find(i)].append(_rref(rows))
    return [([originals[i] for i in ids], by_block[root]) for root,ids in blocks.items()]


def _restrict(terms, row, metrics):
    result={}
    for flat,c in terms.items():
        metrics['witness_restrictions']+=1
        cut=_rref((*flat,row))
        if cut is not None:result[cut]=result.get(cut,0)+c
    return {flat:c for flat,c in result.items() if c}


def _block(n,events,metrics,limit,record):
    terms={():1}; mass=1<<n
    record.update(rank=n,events=len(events),peak_terms=1,intersections_tested=0)
    metrics['peak_terms']=max(1,metrics['peak_terms'])
    for event in events:
        changes={}; lost=0
        for flat,c in terms.items():
            if limit is not None and metrics['intersections_tested']>=limit:
                return None,None
            metrics['intersections_tested']+=1;record['intersections_tested']+=1
            cut=_rref((*flat,*event))
            if cut is not None:
                changes[cut]=changes.get(cut,0)-c
                lost+=c << (n-len(cut))
        if not 0<=lost<=mass:raise AssertionError('Signed restriction mass outside prior complement.')
        mass-=lost
        for cut,c in changes.items():
            c+=terms.get(cut,0)
            if c:terms[cut]=c
            else:terms.pop(cut,None)
        record['peak_terms']=max(len(terms),record['peak_terms'])
        metrics['peak_terms']=max(len(terms),metrics['peak_terms'])
        if not mass:break
    record['survivor_count']=mass
    if mass==0:return 0,None
    # Condition the completed signed indicator, never recursively re-run IE.
    y=0
    for j in range(n):
        bit=1<<(j+1)
        zero=_restrict(terms,bit,metrics); m0=_mass(n,zero)
        if not 0<=m0<=mass:raise AssertionError('Invalid zero-slice count.')
        if m0:terms=zero;mass=m0
        else:terms=_restrict(terms,bit|1,metrics);y|=1<<j
    if _mass(n,terms)!=1:raise AssertionError('Recovered singleton has wrong mass.')
    return record['survivor_count'],y


def _slice(n,events,base,metrics,limit,record):
    base=_rref(base)
    while True:
        kept=[]; forced=[]
        for event in events:
            reduced=_rref(_reduce(r,base) for r in event)
            if reduced is None:continue
            if not reduced:return 0,None
            if len(reduced)==1:forced.append(reduced[0]^1)
            else:kept.append(reduced)
        events=kept
        if not forced:break
        old=len(base);base=_rref((*base,*forced))
        if base is None:return 0,None
        metrics['forced_rank_added']+=len(base)-old
    events=_trim(events)
    blocks=_components(events)
    metrics['component_count']+=len(blocks)
    metrics['max_components_per_slice']=max(len(blocks), metrics['max_components_per_slice'])
    rank=sum(len(basis) for basis,_ in blocks)
    mass=1<<(n-len(base)-rank);witness_rows=list(base)
    for basis,ev in blocks:
        info={};record.append(info)
        cnt,y=_block(len(basis),ev,metrics,limit,info)
        if cnt is None:return None,None
        if cnt==0:return 0,None
        mass*=cnt
        witness_rows.extend((a<<1)|((y>>j)&1) for j,a in enumerate(basis))
    final=_rref(witness_rows)
    if final is None:raise AssertionError('Independent block witnesses did not combine.')
    return mass,_point(final)


def solve_affine_arrangement(n,events,*,max_intersections=None,condition_on=(),max_slices=256):
    """Count n-bit points lying in *none* of the forbidden affine events.

    ``condition_on`` gives optional homogeneous linear observations to fix.
    Independent observations are enumerated (default max_slices=256; explicit
    None permits unbounded slices). ``max_intersections`` bounds globally the
    signed-table update probes, not RREF preprocessing or witness recovery.
    An exhausted budget with unfinished slices/updates yields UNKNOWN, no
    exact count and no witness. Completed SAT counts include all free bits.
    """
    if type(n) is not int or n<0:raise ValueError('Expected a nonnegative explicit dimension.')
    for v in (max_intersections,max_slices):
        if v is not None and (type(v) is not int or v<0):raise ValueError('Invalid work limit.')
    def mask(v):
        if type(v) is not int or v<0 or v.bit_length()>n:raise ValueError('Mask outside parameter scope.')
        return v
    if isinstance(events,(str,bytes)) or isinstance(condition_on,(str,bytes)):
        raise ValueError('Expected iterables of affine events and linear observations.')
    raw=[]; canonical=[]
    try:
        observations,_=_independent_masks(mask(a) for a in condition_on)
        for ev in events:
            if isinstance(ev,(str,bytes)):raise ValueError('Expected rows in each event.')
            rows=[]
            for a,b in ev:
                if type(b) is not int or b not in (0,1):raise ValueError('Expected an integer parity bit.')
                rows.append((mask(a)<<1)|b)
            raw.append(tuple(rows));canonical.append(_rref(rows))
    except TypeError as e:raise ValueError('Expected finite affine events and observations.') from e
    possible=[e for e in canonical if e is not None]
    minimal=_trim(possible)
    metrics=dict(intersections_tested=0,peak_terms=0,component_count=0,max_components_per_slice=0,
                 witness_restrictions=0,forced_rank_added=0)
    out=dict(status='UNKNOWN',reason=None,survivor_count=None,witness=None,input_events=len(raw),
             impossible_events=len(raw)-len(possible),duplicate_events=len(possible)-len(set(possible)),
             contained_events=len(set(possible))-len(minimal),remaining_events=len(minimal),
             condition_rank=len(observations),condition_masks=observations,slices_total=1<<len(observations),
             slices_completed=0,work_samples=[],max_intersections=max_intersections,max_slices=max_slices)
    def finish(reason,count=None,witness=None):
        if count is not None and count>0:
            if witness is None or any(all(((witness & (t>>1)).bit_count()&1)==(t&1) for t in ev) for ev in raw):
                raise AssertionError('Recovered parameter satisfies a forbidden original event.')
        out.update(metrics,reason=reason,survivor_count=count,witness=witness,
                   status='UNKNOWN' if count is None else ('SAT' if count else 'UNSAT'))
        return out
    if () in minimal:return finish('universal_event',0)
    if not minimal:return finish('no_possible_events',1<<n,0)
    mass=0;witness=None
    for i in range(out['slices_total']):
        if max_slices is not None and i>=max_slices:return finish('slice_budget_exhausted')
        records=[]
        cnt,x=_slice(n,minimal,[(v<<1)|((i>>j)&1) for j,v in enumerate(observations)],
                     metrics,max_intersections,records)
        if len(out['work_samples'])<16:out['work_samples'].append({'slice':i,'components':records})
        if cnt is None:return finish('intersection_budget_exhausted')
        out['slices_completed']+=1;mass+=cnt
        if cnt and witness is None:witness=x
    return finish('exact_complement',mass,witness)
