"""Matched SAT/UNSAT controls for rank-deficient parity-feasibility queries.

This is a constructive family, not a solver or recognizer for arbitrary 2-CNF.
A selected option is a matching edge. The syndrome is the set of occupied
left vertices, encoded as a mask. See docs/parity_shadow.md for the theorem.
"""
from dataclasses import dataclass
from itertools import combinations
from .affine import AffineRelation


@dataclass(frozen=True)
class ShadowMatching:
    k: int
    opened: bool = False  # move exactly one option to a previously unused resource

    def __post_init__(self):
        if type(self.k) is not int or self.k < 2 or type(self.opened) is not bool:
            raise ValueError('Expected k >= 2 and a Boolean twin selector.')

    @property
    def target(self):
        return (1 << self.k) - 1

    def _resource(self, row, col):
        if self.opened and (row,col) == (self.k-1,self.k-2):
            return self.k-1
        return col

    def binary_clauses(self):
        """Explicit all-negative 2-CNF, signed one-based option numbers."""
        width=self.k-1
        buckets=[[] for _ in range(self.k)]
        for i in range(self.k):
            row=[-(1+i*width+j) for j in range(width)]
            yield from combinations(row,2)
            for j,v in enumerate(row):
                buckets[self._resource(i,j)].append(v)
        for col in buckets:
            yield from combinations(col,2)

    def syndrome_of_matching(self, options):
        """Return the row syndrome, or None if the option mask violates a binary clause."""
        k=self.k; width=k-1
        if type(options) is not int or not 0 <= options < (1 << (k*width)):
            raise ValueError('Invalid option mask.')
        syndrome=used=0
        for i in range(k):
            row=options & ((1 << width)-1)
            options >>= width
            if not row:
                continue
            if row & (row-1):
                return None
            bit=1 << self._resource(i,row.bit_length()-1)
            if bit & used:
                return None
            used |= bit
            syndrome |= 1 << i
        return syndrome

    def lift(self, syndrome):
        """Construct a matching with exactly these rows, or None for the closed full target."""
        if type(syndrome) is not int or not 0 <= syndrome <= self.target:
            raise ValueError('Invalid row syndrome.')
        if not self.opened and syndrome==self.target:
            return None
        mask=0
        for pos,i in enumerate(i for i in range(self.k) if syndrome >> i & 1):
            # Submatch the fixed perfect matching in the open twin. In the
            # closed twin inject the demanded rows into consecutive resources.
            j=min(i,self.k-2) if self.opened else pos
            mask |= 1 << (i*(self.k-1)+j)
        if self.syndrome_of_matching(mask) != syndrome:
            raise AssertionError('Invalid lifted assignment.')
        return mask

    def verify_hall_cut(self, syndrome, cut):
        """Check the stated neighborhood on labelled resources and demanded rows."""
        if type(syndrome) is not int or not 0 <= syndrome <= self.target:
            return False
        if not isinstance(cut,dict):
            return False
        rows,resources=cut.get('rows'),cut.get('resources')
        if not isinstance(rows,(tuple,list)) or not isinstance(resources,(tuple,list)):
            return False
        if any(type(v) is not int or not 0 <= v < self.k for v in (*rows,*resources)):
            return False
        if len(set(rows))!=len(rows) or len(set(resources))!=len(resources):
            return False
        if any(not (syndrome >> i & 1) for i in rows):
            return False
        actual={self._resource(i,j) for i in rows for j in range(self.k-1)}
        return actual==set(resources) and len(actual)<len(rows)

    def query(self, equations):
        """Decide existence under H*s=b. Only valid on this explicitly generated family."""
        r=AffineRelation(tuple(f'r{i}' for i in range(self.k)),tuple(equations))
        if not r.is_consistent:
            return dict(status='UNSAT',reason='inconsistent_equations',witness=None,syndrome=None,cut=None)
        # RREF pivots on the least set bit of each row; setting free variables
        # to zero guarantees a proper syndrome on EVERY consistent rank<k system.
        s=sum(mask & -mask for mask,rhs in r.equations if rhs)
        if not r.holds_mask(s):
            raise AssertionError('Invalid particular syndrome.')
        model=self.lift(s)
        if model is not None:
            return dict(status='SAT',reason='matching',witness=model,syndrome=s,cut=None)
        cut=dict(rows=list(range(self.k)),resources=list(range(self.k-1)))
        if len(r.equations)!=self.k or not self.verify_hall_cut(s,cut):
            raise AssertionError('Cannot exclude the queried syndromes.')
        return dict(status='UNSAT',reason='unique_syndrome_hall_cut',witness=None,syndrome=s,cut=cut)
