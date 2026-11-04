"""Compile labelled binary columns into a minor of a sparse 3SAT bridge image.

This concerns the representation of pair differences, not the hardness of the
source formula (all its clauses are positive). Column labels, including loops
and parallel elements, are retained; equality of ranks alone would not suffice.
"""
from dataclasses import dataclass
from itertools import combinations

from .fano_minor import quotient_binary_groups, relabel_difference
from .ternary_support import three_cnf_to_weight_two_supports


def _columns(values):
    if isinstance(values,(str,bytes)):
        raise ValueError('expected nonnegative integer columns')
    try:
        v=tuple(values)
    except TypeError as exc:
        raise ValueError('expected an iterable of columns') from exc
    if any(type(x) is not int or x<0 for x in v):
        raise ValueError('expected nonnegative integer columns')
    return v


def _bits(x):
    while x:
        bit=x&-x
        yield bit.bit_length()-1
        x ^= bit


def _dependencies(columns):
    """Canonical kernel basis w.r.t. the first independent labelled columns."""
    pivots={}; deps=[]; chosen=[]
    for j,x in enumerate(columns):
        indices=1<<j
        while x:
            k=x.bit_length()-1
            if k not in pivots:
                pivots[k]=(x,indices);chosen.append(j);break
            row,trace=pivots[k];x ^= row;indices ^= trace
        if not x:
            deps.append(indices)
    return tuple(chosen),tuple(deps)


class _Span:
    def __init__(self):
        self.rows={}

    def add(self,x):
        while x:
            k=x.bit_length()-1
            if k not in self.rows:
                self.rows[k]=x;return True
            x ^= self.rows[k]
        return False

    def remainders(self,xs):
        rows=sorted(self.rows.items(),reverse=True)
        vals=[]
        for x in xs:
            for i,row in rows:
                if (x>>i)&1: x ^= row
            vals.append(x)
        return tuple(vals)


def verify_binary_minor(supports,columns,certificate):
    """Independently certify a minor AFTER contracting all binary group differences.

    Label (group,a,b) uses positions in the original, unsorted option lists.
    No input-matrix realization, SAT solver or graph recognition is assumed.
    """
    target=_columns(columns)
    projected,stage=quotient_binary_groups(supports)
    if not stage['fixed_point']:
        raise ValueError('additional affine absorption possible')
    if not isinstance(certificate,dict): raise ValueError('expected minor certificate')
    seen=set(); used_vectors=set()
    def read(key):
        refs=certificate.get(key)
        if not isinstance(refs,(list,tuple)): raise ValueError('expected list of labels')
        vals=[]
        for ref in refs:
            if not isinstance(ref,(tuple,list)) or len(ref)!=3 or any(type(x) is not int for x in ref):
                raise ValueError('expected integer group/option label')
            g,i,j=ref
            if not (0<=g<len(projected) and 0<=i<j<len(projected[g])) or tuple(ref) in seen:
                raise ValueError('invalid or reused original column reference')
            v=projected[g][i]^projected[g][j]
            # D is the set of distinct nonzero differences of residual groups.
            # Parallel elements / loops of the TARGET can still emerge after
            # the later contractions, but cannot be fabricated as raw labels.
            if not v or v in used_vectors:
                raise ValueError('absent or reused projected difference column')
            seen.add(tuple(ref));used_vectors.add(v);vals.append(v)
        return vals
    contracts=read('contract'); keep=read('keep')
    if len(keep)!=len(target): raise ValueError('one retained label required per target column')
    span=_Span()
    if any(not span.add(x) for x in contracts): raise ValueError('dependent contraction list')
    q=span.remainders(keep)
    basis,dep=_dependencies(q)
    if (basis,dep)!=_dependencies(target):
        raise ValueError('labelled retained dependencies differ from target')
    return dict(verified=True, presolve=stage, further_contraction_rank=len(contracts),
                columns=len(q),rank=len(basis),nullity=len(dep),basis_indices=list(basis),
                kernel_basis=list(dep),loops=sum(x==0 for x in q))


@dataclass(frozen=True)
class BinaryMinorInstance:
    columns: tuple[int,...]
    variables: tuple[str,...]
    clauses: tuple[tuple[int,...],...]
    designated_clauses: tuple[int,...]
    supports: tuple[tuple[int,...],...]
    certificate: dict


def build_binary_minor(columns):
    """Construct a positive 3-CNF and original-column minor certificate.

    Every clause has three distinct source variables; each source variable
    has 2 or 3 occurrences. With an empty target one can use the empty CNF.
    All data are explicit; construction and verification take polynomial bit
    time in the input. A loop can be encoded by two extra fresh generators.
    """
    bs=_columns(columns); n=len(bs); ng=n; checks=[]
    # Presentation of image(B) by generators (column labels) and relators
    # (kernel generators). A three-term splitter has a unique extension
    # through its new prefix generator, so no extra original relation appears.
    for rel in _dependencies(bs)[1]:
        terms=list(_bits(rel))
        if len(terms)==1:
            p,q=ng,ng+1;ng+=2
            checks.extend(((p,q),(terms[0],p,q)))
        else:
            while len(terms)>3:
                z=ng;ng+=1;checks.append((terms[0],terms[1],z))
                terms=[z]+terms[2:]
            checks.append(tuple(terms))
    # An unused generator (e.g. a coloop) also needs at least two incidences.
    for i in range(n):
        twin=ng;ng+=1;checks.append((i,twin))
    checks=checks+checks
    # A clause represents one occurrence-copy of a presentation generator.
    # Payload and equality equations become named variables of the source CNF.
    occ=[[] for _ in range(ng)]; clauses=[]
    for i,eq in enumerate(checks):
        for q in eq:
            occ[q].append(len(clauses));clauses.append([i+1])
    nv=len(checks)
    for copies in occ:
        if len(copies)<2:raise AssertionError('generator needs at least two copies')
        for i,j in enumerate(copies):
            nv+=1;clauses[j].append(nv);clauses[copies[(i+1)%len(copies)]].append(nv)
    names=tuple(f'p{i+1}' for i in range(nv));cs=tuple(map(tuple,clauses))
    red=three_cnf_to_weight_two_supports(names,cs)
    supports=red.supports; projected,stage=quotient_binary_groups(supports)
    m=len(cs);t=3*m
    if stage['contracted_rank']!=t or not stage['fixed_point']:
        raise AssertionError('sparse bridge did not retain the required nonaffine residual')
    # Contract local V_j+C_j, then differences joining the C ports in each
    # clause; contracted columns rendered dependent by earlier contractions
    # are omitted. All references identify pairs of ACTUAL input options.
    chosen=[]; span=_Span()
    def add(g,v):
        ref=relabel_difference(supports,g,v);_,a,b=ref
        if span.add(projected[g][a]^projected[g][b]):chosen.append(ref)
    for j in range(t):add(t+m+j,3<<(2*j))
    for ci in range(m):
        first=1<<(6*ci+1)
        for j in (1,2):add(t+ci,first^(first<<(2*j)))
    designated=tuple(occ[i][0] for i in range(n));keep=[]
    for ci in designated:
        j=3*ci
        keep.append(relabel_difference(supports,t+m+j,1<<(2*j+1)))
    cert={'contract':chosen,'keep':keep}
    return BinaryMinorInstance(bs,names,cs,designated,supports,cert)
