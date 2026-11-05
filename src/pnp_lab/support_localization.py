"""Finite semantic audit for resolution support localization; not a SAT solver.

Compute *all* minimum-cardinality raw supports of the lines in a finite
width closure by exhaustive Boolean entailment. Pool their raw clauses on
requested scopes and look for full unit edges and two-coordinate faces.
No expander theorem, matching oracle, or other lab search backend is used
to infer that these finite witnesses exist.
"""
from fractions import Fraction
from itertools import combinations

from .modular_hull import _input


class _Budget(Exception):
    pass


def _indices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length()-1
        mask -= bit


def _canonical(row):
    return tuple(sorted(row, key=abs))


def _fraction(f):
    return [f.numerator, f.denominator] if f is not None else None


def support_audit(n, clauses, scopes, *, width, s, delta=(1, 1),
                  max_table_bits=16000000, max_rows=512, max_work=500000):
    """Exhaustive finite checks; caps return UNVERIFIED with no partial claims.

    Numeric word masks returned in face witnesses use compact coordinates in
    the order reported under labels. Raw clause IDs are zero based. The
    table-bit cap is for the subset-by-word truth table, not total RAM.
    """
    cs = _input(n, clauses)
    if any(not c or len({abs(l) for l in c}) != len(c) for c in cs):
        raise ValueError('expected nonempty proper raw clauses of width <=3')
    if any(type(v) is not int or v < 0 for v in
           (width,s,max_table_bits,max_rows,max_work)) or not s:
        raise ValueError('invalid bound')
    if (not isinstance(delta, (list,tuple)) or len(delta)!=2 or
            any(type(x) is not int or x<=0 for x in delta)):
        raise ValueError('expected a positive rational expansion factor')
    rate = Fraction(*delta)
    scopes = tuple(tuple(scope) for scope in scopes)
    if any(any(type(v) is not int or not 1<=v<=n for v in scope)
           or len(set(scope))!=len(scope) for scope in scopes):
        raise ValueError('invalid scope')
    labels=tuple(sorted({abs(l) for c in cs for l in c} |
                        {v for scope in scopes for v in scope}))
    m, k = len(cs), len(labels)
    if m+k >= max_table_bits.bit_length():
        return dict(status='UNVERIFIED', reason='subset-word table cap')
    subsets, words = 1 << m, 1 << k
    if subsets*words > max_table_bits or subsets-1 > max_work:
        return dict(status='UNVERIFIED', reason='subset-word table or work cap')
    pos={v:i for i,v in enumerate(labels)}
    full=(1<<words)-1
    columns={}
    for v,i in pos.items():
        step=1<<i
        columns[v]=(((1<<step)-1)<<step)*(full//((1<<(2*step))-1))

    def truth(c):
        value=0
        for l in c:
            col=columns[abs(l)]
            value |= col if l>0 else full^col
        return value

    counts=dict(raw_subsets=subsets, explicit_cube_words=words,
                subset_word_table_bits=subsets*words, work=0, subset_profiles=0,
                resolution_pairs=0, entailment_checks=0, pooled_support_visits=0,
                common_support_checks=0,
                unit_edges_checked=0, square_faces_checked=0)

    def charge(name, count=1):
        if counts['work']+count > max_work:
            raise _Budget('work cap')
        counts['work']+=count
        counts[name]+=count

    try:
        raw_bits=list(map(truth,cs))
        models=[full]
        raw_vars=[{abs(l) for l in c} for c in cs]
        boundary=[frozenset()]
        min_boundary_ratio=min_surplus=None
        for mask in range(1,subsets):
            charge('subset_profiles')
            bit=mask & -mask
            models.append(models[mask^bit] & raw_bits[bit.bit_length()-1])
            seen,shared=set(),set()
            for j in _indices(mask):
                shared.update(seen & raw_vars[j])
                seen.update(raw_vars[j])
            boundary.append(frozenset(seen-shared))
            t=mask.bit_count()
            if t<=s:
                ratio=Fraction(len(boundary[-1]),t)
                surplus=len(seen)-t
                min_boundary_ratio=ratio if min_boundary_ratio is None else min(ratio,min_boundary_ratio)
                min_surplus=surplus if min_surplus is None else min(surplus,min_surplus)

        # Full set-valued ordinary binary-resolution closure: no weakening,
        # no heuristic deletion, and no reads from other experiment reports.
        rows=[]
        known=set()
        def add(row):
            if len(row)<=width and row not in known:
                if len(rows)>=max_rows:
                    raise _Budget('width-closure row cap')
                known.add(row)
                rows.append(row)
        for c in cs:
            add(frozenset(c))
        inputs=len(rows)
        i=0
        while i<len(rows):
            left=rows[i]
            for j in range(i):
                charge('resolution_pairs')
                right=rows[j]
                cross={l for l in left if -l in right}
                if len(cross)==1:
                    l,=cross
                    add((left-{l}) | (right-{-l}))
            i+=1

        by_size=sorted(range(subsets),key=lambda z:(z.bit_count(),z))
        line_data=[]
        witnesses=[]
        for line in rows:
            rejected=full ^ truth(line)
            best=None
            ties=[]
            for mask in by_size:
                t=mask.bit_count()
                if best is not None and t>best:
                    break
                charge('entailment_checks')
                if not (models[mask] & rejected):
                    assert boundary[mask] <= set(map(abs,line))
                    best=t
                    ties.append(mask)
            assert ties                        # every line follows from F
            witnesses.append(ties)
            line_data.append(dict(clause=list(_canonical(line)),minimum_support_size=best,
                                  minimum_raw_supports=[list(_indices(z)) for z in ties]))

        # For a face, find one complete word with the chosen axes zero for
        # which turning on EACH subset of those axes leaves a model.
        def face(allowed,axes):
            base=allowed
            for v in axes:
                base &= full ^ columns[v]
            jumps=[1<<pos[v] for v in axes]
            offsets=[sum(jumps[j] for j in _indices(i)) for i in range(1<<len(axes))]
            for offset in offsets[1:]:
                base &= allowed >> offset
            if not base:
                return None
            word=(base & -base).bit_length()-1
            return dict(axes=list(axes),base=word)

        pools=[]
        for scope in scopes:
            named=set(scope)
            selected=[i for i,line in enumerate(rows) if all(abs(l) in named for l in line)]
            union=0
            prefix_sizes=[]
            for i in selected:
                for mask in witnesses[i]:
                    charge('pooled_support_visits')
                    union |= mask
                    if not prefix_sizes or union.bit_count()!=prefix_sizes[-1]:
                        prefix_sizes.append(union.bit_count())
                    assert boundary[union]<=named
            structural=0
            for mask in range(subsets):
                if mask.bit_count()<=s:
                    charge('common_support_checks')
                    if boundary[mask]<=named:
                        structural |= mask
            allowed=models[structural]
            learned=full
            for i in selected:
                learned &= truth(rows[i])
            assert not (models[union] & ~learned)
            edges=[]
            squares=[]
            for r, dest, key in ((1,edges,'unit_edges_checked'),(2,squares,'square_faces_checked')):
                for axes in combinations(scope,r):
                    charge(key)
                    f=face(allowed,axes)
                    if f is not None:
                        dest.append(f)
            pools.append(dict(scope=list(scope),lines=selected,derived=sum(i>=inputs for i in selected),
                              pooled_raw_ids=list(_indices(union)),prefix_sizes=prefix_sizes,
                              common_raw_ids=list(_indices(structural)),
                              common_entails=not(allowed & ~learned),
                              unit_edges=edges,square_faces=squares,
                              all_unit_edges=len(edges)==len(scope),
                              all_square_faces=len(squares)==len(scope)*(len(scope)-1)//2))
    except _Budget as exc:
        return dict(status='UNVERIFIED',reason=str(exc),counts=counts)
    return dict(status='CHECKED',labels=list(labels),counts=counts,width=width,
                s=s,delta=_fraction(rate),min_boundary_ratio=_fraction(min_boundary_ratio),
                boundary_condition=(min_boundary_ratio is None or min_boundary_ratio>=rate),
                min_neighborhood_surplus=min_surplus,proper_ternary=all(len(c)==3 for c in cs),
                raw_input_lines=inputs,closure_lines=len(rows),lines=line_data,scopes=pools,
                width_window=(2*(width//rate)<=s),
                scope_window=all(2*(len(scope)//rate)<=s for scope in scopes))
