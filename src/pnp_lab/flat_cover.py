"""Avoid one missing point per affine flat on a joint XOR fiber.

An input flat is (anchor, independent direction masks, hole), with hole
None for a full flat or one absolute point of the flat to exclude. This
polynomial partial decision procedure does not list flat points or a kernel
fiber. A sufficient cover inequality can construct a satisfying witness;
a failed sufficient test never certifies UNSAT. Coordinate maps and ranks
are over GF(2), in the explicit bit-vector input model.
"""
from __future__ import annotations

from .frontier import _Basis


class _Tagged:
    """Column echelon reduction with coefficients in an explicit generator list."""
    def __init__(self):
        self.rows = {}

    def reduce(self, v, tag=0):
        while v:
            row = self.rows.get(v.bit_length()-1)
            if row is None:
                break
            v ^= row[0]
            tag ^= row[1]
        return v, tag

    def add(self, v, tag):
        r, z = self.reduce(v, tag)
        if r:
            self.rows[r.bit_length()-1] = (r,z)
            return None
        return z


def _vec(v):
    if type(v) is not int or v < 0:
        raise ValueError('Masks must be nonnegative integers.')
    return v


def _parse(flats):
    if isinstance(flats, (str,bytes)):
        raise ValueError('Expected triples of anchor, directions, and optional hole.')
    parsed=[]
    try:
        for item in flats:
            a, dirs, h = item
            _vec(a)
            if isinstance(dirs,(str,bytes)):
                raise ValueError('Expected a finite direction basis.')
            ds=tuple(_vec(d) for d in dirs)
            loc=_Tagged()
            for j,d in enumerate(ds):
                if loc.add(d,1<<j) is not None:
                    raise ValueError('The directions of each flat must be independent.')
            hc=None
            if h is not None:
                rem,hc=loc.reduce(_vec(h)^a)
                if rem:
                    raise ValueError('The hole must be an absolute point of the flat.')
            parsed.append((a,ds,h,hc,loc))
    except TypeError as exc:
        raise ValueError('Expected triples of anchor, directions, and optional hole.') from exc
    return parsed


def solve_hole_cover(flats, target):
    """Choose one allowed point from each flat with XOR ``target``, or report UNKNOWN.

    First solve the joint affine system. Its 2**q decompositions are a
    particular coefficient vector plus q independent kernel vectors. For
    hole i, the equation fixing local i to that point has 0 or 2**(q-rho_i)
    parameter solutions, where rho_i is the rank of the corresponding local
    projection of the joint kernel. Its image in ambient coordinates is
    P_i intersect sum_{j != i} P_j, for direction spaces P_j: a change can
    be compensated in the other flats exactly for elements of this intersection.

    A strict sum of bad counts below 2**q implies SAT by union bound. At each
    parameter bit the zero/one slices split both capacity and every bad count;
    at least one child inherits the strict inequality. Select such a child
    until a witness is fixed. In particular sum_{holes i} 2**(-rho_i) < 1
    suffices uniformly for every target inside the joint hull. Where bounds
    are inconclusive a checked particular witness still proves SAT.

    projection_ranks lists one rank per punctured flat (None for a full flat).
    Counts use O(q+log(number_of_flats+1)) bits. The implementation makes at
    most q conditional steps, using precomputed suffix-echelon ranks. No
    factor 2**q in the number of work steps or stored parameter assignments.
    """
    target=_vec(target)
    parsed=_parse(flats)
    rows=_Tagged(); kernel=[]; width=0; delta=target
    for a,ds,*_ in parsed:
        delta ^= a
        for d in ds:
            dep=rows.add(d,1<<width)
            if dep is not None:
                # Its coefficient on this new column is one. These kernel
                # vectors are independent and their number is the nullity.
                kernel.append(dep)
            width+=1
    rem,part=rows.reduce(delta)
    q=len(kernel)
    out=dict(status='UNKNOWN',reason=None,witness=None,nullity=q,hull_rank=len(rows.rows),
             total_decompositions=0,bad_counts=[],exclusion_sum=None,projection_ranks=[],
             uniform_exclusion_bound=None,uniform_strict=None,parameter_steps=0,
             conditional_rank_tests=0)
    if rem:
        out.update(status='UNSAT',reason='outside_joint_affine_hull')
        return out
    size=1<<q
    out['total_decompositions']=size

    # Track hole equations in local coefficient coordinates. The supplied
    # local bases are independent, so coefficient equality is point equality.
    tracks=[]; offset=0; worst=0
    for _,ds,_,hc,_ in parsed:
        mask=(1<<len(ds))-1
        if hc is None:
            out['bad_counts'].append(0);out['projection_ranks'].append(None)
        else:
            b=hc ^ ((part>>offset)&mask)
            cols=tuple((k>>offset)&mask for k in kernel)
            suffix=_Basis(); ranks=[0]*(q+1)
            for j in reversed(range(q)):
                suffix.add(cols[j]);ranks[j]=len(suffix)
            extent=1<<(q-ranks[0]);worst+=extent
            count=0 if suffix.normal(b) else extent
            out['bad_counts'].append(count);out['projection_ranks'].append(ranks[0])
            if count:
                tracks.append([b,cols,suffix,ranks])
        offset+=len(ds)
    bad=sum(out['bad_counts'])
    out.update(exclusion_sum=bad,uniform_exclusion_bound=worst,uniform_strict=worst<size)
    if any(n==size for n in out['bad_counts']):
        out.update(status='UNSAT',reason='one_hole_covers_entire_fiber')
        return out

    def values(code):
        points=[]; i=0
        for a,ds,*_ in parsed:
            v=a
            for d in ds:
                if code>>i&1:v^=d
                i+=1
            points.append(v)
        return points

    def checked(points,reason):
        z=0
        for v,(a,_,h,_,loc) in zip(points,parsed):
            if v==h or loc.reduce(v^a)[0]:
                raise AssertionError('Recovered point is not in its punctured flat.')
            z^=v
        if z!=target or len(points)!=len(parsed):
            raise AssertionError('Recovered flat values fail to realize the target.')
        out.update(status='SAT',reason=reason,witness=points)
        return out

    pts=values(part)
    if all(v!=f[2] for v,f in zip(pts,parsed)):
        return checked(pts,'checked_particular_witness')
    if bad>=size:
        out['reason']='union_bound_inconclusive'
        return out
    code=part
    for j in range(q):
        cap=1<<(q-j-1)
        zero_bad=0
        for b,_,suffix,ranks in tracks:
            r=ranks[j+1]
            out['conditional_rank_tests']+=1
            if not suffix.normal(b,r):
                zero_bad+=1<<(q-j-1-r)
        if zero_bad<cap:
            bad=zero_bad
        else:
            code^=kernel[j]
            bad-=zero_bad
            for t in tracks:t[0]^=t[1][j]
        if not 0<=bad<cap:
            raise AssertionError('Conditional count lost its strict upper bound.')
        out['parameter_steps']+=1
    return checked(values(code),'conditional_cover_witness')
