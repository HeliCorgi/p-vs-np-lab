"""Compile the *actual* holes of a sum fiber to affine events on its kernel bits.

Counting points in this parameter space counts admissible decompositions of
the listed flats, not the number of source 3SAT models or pre-merge witnesses.
"""
from dataclasses import dataclass
from functools import reduce
from operator import xor

from .flat_cover import _parse, _Tagged, _vec


@dataclass(frozen=True)
class FiberArrangement:
    target: int
    flats: tuple
    rank: int
    particular: int | None
    kernel: tuple[int, ...]
    events: tuple
    event_flat_indices: tuple[int, ...]

    @property
    def dimension(self):
        return len(self.kernel)

    def decode(self, point):
        if self.particular is None:
            raise ValueError('The target is outside the affine hull.')
        if type(point) is not int or point<0 or point.bit_length()>self.dimension:
            raise ValueError('Invalid kernel parameter.')
        code=self.particular
        p=point
        while p:
            bit=p & -p
            code ^= self.kernel[bit.bit_length()-1]
            p ^= bit
        vals=[]
        for a,ds,h in self.flats:
            v=a
            for d in ds:
                if code&1:v^=d
                code>>=1
            if h is not None and v==h: raise ValueError('Parameter point hits a forbidden flat point.')
            vals.append(v)
        if reduce(xor,vals,0)!=self.target:raise AssertionError('Incorrect lifted fiber sum.')
        return vals


def compile_flat_arrangement(flats, target):
    """All affine decompositions are a particular vector plus a kernel basis.

    A hole is an AND of affine bit-equations in kernel coordinates. Independent
    local direction bases make local coefficient equality exactly point equality.
    """
    target=_vec(target); parsed=_parse(flats)
    rows=_Tagged(); kernel=[]; width=0; delta=target
    for a,ds,h,hc,_ in parsed:
        delta ^= a
        for d in ds:
            k=rows.add(d,1<<width)
            if k is not None: kernel.append(k)
            width+=1
    rem,part=rows.reduce(delta)
    known=tuple((a,ds,h) for a,ds,h,_,_ in parsed)
    events=[];ids=[];at=0
    if not rem:
        for i,(_,ds,_,hc,_) in enumerate(parsed):
            if hc is not None:
                eq=[]
                for j in range(len(ds)):
                    form=sum(((k>>(at+j))&1)<<s for s,k in enumerate(kernel))
                    eq.append((form,((hc>>j)^(part>>(at+j)))&1))
                events.append(tuple(eq));ids.append(i)
            at+=len(ds)
    return FiberArrangement(target,known,len(rows.rows),None if rem else part,tuple(kernel),tuple(events),tuple(ids))


def solve_flat_arrangement(flats,target,*,method='project',max_pairs=None,max_intersections=None,
                           degree=4,max_rows=None,condition_on=(),max_slices=256,order=None):
    f=compile_flat_arrangement(flats,target)
    if method not in ('project','lattice','refute'): raise ValueError('Unknown affine overlap method.')
    if f.particular is None:
        return dict(status='UNSAT',reason='outside_joint_affine_hull',witness=None,
                    parameter_witness=None,fiber_dimension=f.dimension,event_count=0)
    if method=='project':
        from .event_projection import project_affine_events
        r=project_affine_events(f.dimension,f.events,order=order,max_pairs=max_pairs)
    elif method=='lattice':
        from .overlap_lattice import solve_affine_arrangement
        r=solve_affine_arrangement(f.dimension,f.events,max_intersections=max_intersections,
                                   condition_on=condition_on,max_slices=max_slices)
    else:
        from .overlap_refutation import refute_affine_cover
        r=refute_affine_cover(f.dimension,f.events,degree=degree,max_rows=max_rows)
    p=r.get('witness')
    return dict(status=r['status'],reason=r.get('reason'),witness=f.decode(p) if r['status']=='SAT' else None,
                parameter_witness=p,fiber_dimension=f.dimension,event_count=len(f.events),
                event_flat_indices=list(f.event_flat_indices),parameter_result=r)
