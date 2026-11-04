"""Check a labelled Fano minor of the pair differences, independently of discovery.

The result rejects a particular class of coordinate changes. It makes no
SAT/UNSAT decision. Labels index original option lists before sorting.
"""
from itertools import combinations


def _rows(vectors):
    pivots = {}
    for x in vectors:
        while x:
            bit = x & -x
            if bit not in pivots:
                pivots[bit] = x
                break
            x ^= pivots[bit]
    return tuple(sorted(pivots.items()))


def _remainder(x, rows):
    for bit, v in rows:
        if x & bit:
            x ^= v
    return x


def _groups(supports):
    gs = tuple(tuple(group) for group in supports)
    if any(type(x) is not int or x < 0 for group in gs for x in group):
        raise ValueError('Expected nonnegative integer masks.')
    return gs


def quotient_binary_groups(supports):
    """Project into the quotient by all two-point groups; preserve raw labels.

    This is a representation analysis, NOT a SAT reduction without an offset.
    'fixed_point' certifies that no projected nonconstant support is a full
    affine coset, hence that additional affine absorption would add no rank.
    """
    gs = _groups(supports)
    distinct = [tuple(dict.fromkeys(g)) for g in gs]
    basis = _rows(a ^ b for g in distinct if len(g) == 2 for a, b in [g])
    projected = tuple(tuple(_remainder(v, basis) for v in g) for g in gs)
    adds_span = False
    for g in projected:
        pts = tuple(set(g))
        if len(pts) > 1 and len(pts).bit_count() == 1:
            adds_span |= len(_rows(x ^ pts[0] for x in pts)) == len(pts).bit_length()-1
    return projected, {'binary_groups':sum(len(g)==2 for g in distinct),
                       'contracted_rank':len(basis),'fixed_point':not adds_span}


def relabel_difference(supports, group, value):
    """Find an original pair label for a desired column (construction helper)."""
    for i,j in combinations(range(len(supports[group])),2):
        if supports[group][i] ^ supports[group][j] == value:
            return [group, i, j]
    raise ValueError('Column absent in the specified group.')


def verify_fano_minor(supports, certificate):
    """Verify contraction independence and seven distinct nonzero rank-three points.

    Contracting independent columns means taking a linear quotient by them.
    The seven retained labels in the quotient must exhaust F_2^3 minus zero.
    This uses low-pivot elimination; it does not call the tree recognizer,
    frontier solver, or matching solver. Malformed certificates raise ValueError.
    """
    if not isinstance(certificate,dict):
        raise ValueError('Expected a certificate object.')
    gs = _groups(supports)
    def labels(key):
        raw = certificate.get(key)
        if not isinstance(raw,(tuple,list)):
            raise ValueError(f'{key}: expected a list of column references')
        refs=[]; values=[]
        for ref in raw:
            if not isinstance(ref,(list,tuple)) or len(ref)!=3 or any(type(x) is not int for x in ref):
                raise ValueError('Invalid reference format.')
            g,a,b=ref
            if not (0<=g<len(gs) and 0<=a<b<len(gs[g])):
                raise ValueError('Invalid original group or option index.')
            refs.append((g,a,b));values.append(gs[g][a]^gs[g][b])
        return refs,values
    contracts,c = labels('contract'); keeps,k = labels('keep')
    if len(k)!=7 or len(set(contracts+keeps))!=len(contracts)+7:
        raise ValueError('Need seven retained labels disjoint from independent contractions.')
    basis = _rows(c)
    if len(basis)!=len(c):
        raise ValueError('Dependent contraction list; supply an independent list.')
    q = tuple(_remainder(x,basis) for x in k)
    if 0 in q or len(set(q))!=7 or len(_rows(q))!=3:
        raise ValueError('The quotient restriction is not seven distinct nonzero points of rank three.')
    indices = certificate.get('quotient_basis_keep_indices', [0,1,3])
    if not isinstance(indices,(tuple,list)) or len(indices)!=3 or any(type(i) is not int or not 0<=i<7 for i in indices):
        raise ValueError('Invalid quotient basis indices.')
    a,b,d=(q[i] for i in indices)
    coords={ (a if j&1 else 0) ^ (b if j&2 else 0) ^ (d if j&4 else 0):j for j in range(8)}
    if len(coords)!=8:
        raise ValueError('Claimed quotient basis is dependent.')
    actual=[coords[x] for x in q]
    claims={'expected_contracted_rank':len(c),'expected_minor_rank':3,'expected_quotient_coordinates':actual}
    for key,val in claims.items():
        if key in certificate and certificate[key]!=val:
            raise ValueError(f'False expected value: {key}')
    return {'verified':True,'minor':'F7','contraction_rank':len(c),'minor_rank':3,
            'quotient_coordinates':actual,'groups_used':sorted({g for g,_,_ in contracts+keeps})}
