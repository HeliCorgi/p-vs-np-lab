"""Represent a signed width-three CNF as affine forbidden events over GF(2).

Coordinates 0..n-1 are the explicitly supplied source bits. Clause c uses
coordinates n+2c,n+2c+1 for u,v; the third selector is 1 XOR u XOR v.
An event is the conjunction of its parity equations. A witness avoids every
event. The optional fourth event per clause enforces exactly one selection.
"""
from dataclasses import dataclass


def _fits(mask, dim):
    return type(mask) is int and 0 <= mask < (1 << dim)


def _literal_true(lit, mask):
    return bool(mask & (1 << (abs(lit)-1))) == (lit > 0)


def _project(enc, parameter_mask):
    if not _fits(parameter_mask,enc.n_parameters):
        raise ValueError('Parameter assignment must fit its explicit scope.')
    if any(all((parameter_mask & mask).bit_count()%2 == rhs for mask,rhs in event)
           for event in enc.events):
        raise ValueError('The parameter assignment hits a forbidden event.')
    raw = parameter_mask & ((1<<len(enc.original_variables))-1)
    if not all(any(_literal_true(lit,raw) for lit in clause) for clause in enc.original_cnf):
        raise AssertionError('Avoiding assignment failed the source CNF.')
    return raw


@dataclass(frozen=True)
class SelectorEncoding:
    original_variables: tuple
    original_cnf: tuple
    padded_cnf: tuple
    events: tuple
    occurrence_event_ids: tuple
    selector_event_ids: tuple
    n_parameters: int
    strict: bool

    def project_witness(self, parameter_mask):
        """Check each raw parity event, then validate decoded bits against the unpadded CNF."""
        return _project(self,parameter_mask)

    def lift_witness(self, source_mask):
        """Select one true occurrence in each clause, including in relaxed mode."""
        n=len(self.original_variables)
        if not _fits(source_mask,n):
            raise ValueError('Source assignment must fit its explicit scope.')
        par=source_mask
        for c,clause in enumerate(self.padded_cnf):
            k=next((j for j,lit in enumerate(clause) if _literal_true(lit,source_mask)),None)
            if k is None:
                raise ValueError('Source assignment does not satisfy the formula.')
            if k<2:
                par |= 1 << (n+2*c+k)
        if self.project_witness(par)!=source_mask:
            raise AssertionError('Selector witness roundtrip failed.')
        return par


def _source(variables, clauses):
    if isinstance(variables,(str,bytes)) or isinstance(clauses,(str,bytes)):
        raise ValueError('Expected variable names and a sequence of clauses.')
    try:
        names=tuple(variables)
        cs=[]
        for clause in clauses:
            if isinstance(clause,(str,bytes)):
                raise ValueError('Expected signed integer literals.')
            cs.append(tuple(clause))
    except TypeError as exc:
        raise ValueError('Expected a sequence of names and clauses.') from exc
    if any(type(x) is not str or not x for x in names) or len(set(names))!=len(names):
        raise ValueError('Expected distinct, nonempty variable names.')
    n=len(names)
    if any(len(c)>3 or any(type(x) is not int or x==0 or abs(x)>n for x in c) for c in cs):
        raise ValueError('Width must be at most three and literal indices must belong to the source.')
    return names,tuple(cs)


def compile_selector_events(variables, clauses, *, strict=True):
    """Compile up to four events per clause, each with at most two sparse rows.

    A conjunction of zero equations is the entire space: an empty clause
    therefore covers every parameter assignment immediately. Short clauses
    are padded with repeats before selector bits are assigned, which preserves
    their truth but can alter witness multiplicities. Every explicit source
    variable (including unused ones) retains its original coordinate.
    """
    if type(strict) is not bool:
        raise ValueError('strict must be a Boolean.')
    names,cs = _source(variables,clauses)
    n=len(names)
    padded=[]; events=[]; occurrences=[]; selectors=[]
    for c,clause in enumerate(cs):
        if not clause:
            padded.append(());occurrences.append(());selectors.append(None);events.append(())
            continue
        ls=clause+(clause[-1],)*(3-len(clause));padded.append(ls)
        u=1<<(n+2*c);v=u<<1
        indices=[]
        for lit,select in zip(ls,((u,1),(v,1),(u^v,0))):
            indices.append(len(events));events.append(((1<<(abs(lit)-1),int(lit<0)),select))
        occurrences.append(tuple(indices))
        selectors.append(len(events) if strict else None)
        if strict:
            events.append(((u,1),(v,1)))
    return SelectorEncoding(names,tuple(cs),tuple(padded),tuple(events),tuple(occurrences),
                            tuple(selectors),n+2*len(cs),strict)


@dataclass(frozen=True)
class CompactEncoding:
    """Two bad events and one private bit for each nonempty clause."""
    original_variables: tuple
    original_cnf: tuple
    padded_cnf: tuple
    events: tuple
    pair_event_ids: tuple
    n_parameters: int

    @property
    def per_clause_event_ids(self):
        return self.pair_event_ids

    def project_witness(self, parameter_mask):
        return _project(self,parameter_mask)

    def lift_witness(self, source_mask):
        n=len(self.original_variables)
        if not _fits(source_mask,n):
            raise ValueError('Source assignment must fit its explicit scope.')
        word=source_mask
        for i,clause in enumerate(self.padded_cnf):
            if not clause or not any(_literal_true(lit,source_mask) for lit in clause):
                raise ValueError('Source assignment does not satisfy the formula.')
            # z = 1 + (1+f1)*f3. At these bits the two indicators are 0, f1*f2*f3.
            z=1^(int(_literal_true(clause[0],source_mask)) * int(not _literal_true(clause[2],source_mask)))
            word |= z << (n+i)
        if self.project_witness(word)!=source_mask:
            raise AssertionError('Compact witness roundtrip failed.')
        return word


def compile_compact_events(variables, clauses):
    """Exclude (f1=1,z=0) and (f2=1,z=f3), where f_i=1 iff literal i is false.

    For fixed source bits, both possible z are prohibited iff all literals
    are false. Each nonempty clause emits exactly two rank-two affine events;
    each first row has weight one, each second row has weight at most two.
    """
    names,cs=_source(variables,clauses)
    n=len(names);padded=[];ev=[];ids=[]
    for ci,cl in enumerate(cs):
        if not cl:
            ids.append((len(ev),));ev.append(());padded.append(());continue
        ls=cl+(cl[-1],)*(3-len(cl));padded.append(ls)
        a,b,c=ls;z=1<<(n+ci);i=len(ev)
        ev.append(((1<<(abs(a)-1),int(a<0)),(z,0)))
        ev.append(((1<<(abs(b)-1),int(b<0)),(z^(1<<(abs(c)-1)),int(c>0))))
        ids.append((i,i+1))
    return CompactEncoding(names,cs,tuple(padded),tuple(ev),tuple(ids),n+len(cs))


@dataclass(frozen=True)
class ParsimoniousEncoding:
    """Three rank-two flats per nonempty clause, with one uniquely determined private bit."""
    original_variables: tuple
    original_cnf: tuple
    padded_cnf: tuple
    events: tuple
    per_clause_event_ids: tuple
    n_parameters: int

    def project_witness(self, parameter_mask):
        return _project(self,parameter_mask)

    def lift_witness(self, source_mask):
        n=len(self.original_variables)
        if not _fits(source_mask,n):
            raise ValueError('Source assignment must fit its explicit scope.')
        word=source_mask
        for i,clause in enumerate(self.padded_cnf):
            if not clause or not any(_literal_true(lit,source_mask) for lit in clause):
                raise ValueError('Source assignment does not satisfy the formula.')
            z=not any(_literal_true(lit,source_mask) for lit in clause[:2])
            word|=int(z)<<(n+i)
        if self.project_witness(word)!=source_mask:
            raise AssertionError('Parsimonious witness roundtrip failed.')
        return word


def compile_parsimonious_events(variables, clauses):
    """Use two bad flats to force z=f1*f2; a third excludes z=f3=1.

    Each satisfying source assignment (on the entire explicit scope) has
    exactly one surviving parameter assignment. Nonmodels have none.
    """
    names,cs=_source(variables,clauses)
    n=len(names);padded=[];ev=[];ids=[]
    for ci,cl in enumerate(cs):
        if not cl:
            ids.append((len(ev),));ev.append(());padded.append(());continue
        ls=cl+(cl[-1],)*(3-len(cl));padded.append(ls)
        a,b,c=ls;z=1<<(n+ci);i=len(ev)
        # z differs from f2 iff z+x_b = 1 + constant(f2).
        ev.append(((1<<(abs(a)-1),int(a>0)),(z,1)))
        ev.append(((1<<(abs(a)-1),int(a<0)),(z^(1<<(abs(b)-1)),int(b<0))))
        ev.append(((1<<(abs(c)-1),int(c<0)),(z,1)))
        ids.append((i,i+1,i+2))
    return ParsimoniousEncoding(names,cs,tuple(padded),tuple(ev),tuple(ids),n+len(cs))
