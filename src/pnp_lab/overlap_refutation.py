"""Checked static GF(2) refutations of a cover by forbidden affine subspaces.

Events are conjunctions of parity equations (nonnegative bit mask, 0/1).
UNSAT means no parameter vector avoids all events. UNKNOWN is inconclusive.
Multilinear monomials are variable-subset masks, combined by bitwise OR when
multiplied in F_2[x]/(x_i^2-x_i). No truth table is needed.
"""
from itertools import combinations


_KIND = 'gf2-affine-cover-static-v1'


def _nonnegative(x):
    return type(x) is int and x >= 0


def _input(n, events):
    if not _nonnegative(n):
        raise ValueError('n must be a nonnegative integer')
    ans = []
    try:
        if isinstance(events, (str, bytes)):
            raise ValueError('expected a list of affine events')
        for event in events:
            if isinstance(event, (str, bytes)):
                raise ValueError('expected a conjunction of parity equations')
            eqs = []
            for eq in event:
                m, b = eq
                if not _nonnegative(m) or m.bit_length() > n or type(b) is not int or b not in (0, 1):
                    raise ValueError('expected an in-scope mask and integer parity 0 or 1')
                eqs.append((m, b))
            ans.append(tuple(eqs))
    except (TypeError, OverflowError) as exc:
        raise ValueError('expected finite lists of (mask, parity) equations') from exc
    return tuple(ans)


def _independent(eqs):
    """An equivalent independent list, or None for an impossible event."""
    basis = {}
    for m, b in eqs:
        while m:
            p = m.bit_length() - 1
            if p not in basis:
                basis[p] = m, b
                break
            v, c = basis[p]
            m ^= v
            b ^= c
        if not m and b:
            return None
    return tuple(basis.values())


def _bits(word):
    while word:
        b = word & -word
        yield b
        word ^= b


def _indicator(eqs):
    p = {0}
    for m, b in eqs:
        # Indicator of <m,x>=b is 1+b+<m,x>.
        z = p.copy() if b == 0 else set()
        for bit in _bits(m):
            for t in p:
                v = t | bit
                if v in z:
                    z.remove(v)
                else:
                    z.add(v)
        p = z
    return p


def _validate_certificate(n, raw, certificate, max_degree):
    if not isinstance(certificate, dict) or certificate.get('kind') != _KIND:
        raise ValueError('unrecognized certificate format')
    d = certificate.get('degree')
    if (not _nonnegative(d) or type(certificate.get('n')) is not int or certificate['n'] != n
            or (max_degree is not None and (not _nonnegative(max_degree) or d > max_degree))):
        raise ValueError('invalid dimension or degree claim/budget')
    terms = certificate.get('terms')
    if not isinstance(terms, (list, tuple)) or not terms:
        raise ValueError('expected nonempty list of [event, multiplier] terms')
    seen, ranks = set(), {}
    actual = 0
    for item in terms:
        if not isinstance(item, (list, tuple)) or len(item) != 2:
            raise ValueError('invalid term format')
        i, z = item
        if not _nonnegative(i) or i >= len(raw) or not _nonnegative(z) or z.bit_length() > n or (i,z) in seen:
            raise ValueError('bad event index, monomial, or duplicate term')
        seen.add((i,z))
        if i not in ranks:
            rows = _independent(raw[i])
            if rows is None:
                raise ValueError('zero indicator need not occur in a certificate')
            ranks[i] = len(rows)
        actual = max(actual, ranks[i] + z.bit_count())
    if actual != d:
        raise ValueError('certificate does not state its actual static degree')
    return seen


def verify_cover_certificate(n, events, certificate, *, max_degree=None):
    """Expand original event equations term-by-term; never trust search row IDs.

    Raises ValueError on a malformed or false identity. Independent of the
    generator's polynomial expander and span search. With a fixed max_degree,
    only consistent original events of bounded rank can reach expansion.
    """
    raw = _input(n, events)
    pairs = _validate_certificate(n, raw, certificate, max_degree)
    # Group original monomials by event to avoid repeatedly expanding the
    # same raw parity conjunction. Symmetric difference is addition mod 2.
    multipliers = {}
    for i,z in pairs:
        multipliers.setdefault(i, []).append(z)
    total = set()
    for i,zs in multipliers.items():
        value = {0}
        for linear, rhs in raw[i]:
            factors = list(_bits(linear))
            if not rhs:
                factors.append(0)
            out = set()
            for mon in value:
                for f in factors:
                    out.symmetric_difference_update((mon | f,))
            value = out
        for z in zs:
            for t in value:
                total.symmetric_difference_update((t | z,))
    if total != {0}:
        raise ValueError('sum is not the constant polynomial 1')
    return True


def refute_affine_cover(n, events, *, degree=3, max_rows=None):
    """Search for a bounded static Boolean Nullstellensatz identity.

    For consistent event i of rank r, generate its indicator times each
    squarefree monomial of size at most degree-r, even when Boolean
    reduction of the product happens to drop its degree. Constant 1 in
    their GF(2)-span certifies coverage; absence is NOT a survival witness.
    max_rows bounds tested rows, not preprocessing, expansion, or all time.
    """
    raw = _input(n, events)
    if not _nonnegative(degree) or (max_rows is not None and not _nonnegative(max_rows)):
        raise ValueError('expected nonnegative degree and row budget')
    eligible, bits, impossible, too_high = [], 0, 0, 0
    for i, eqs in enumerate(raw):
        rows = _independent(eqs)
        if rows is None:
            impossible += 1
        elif len(rows) > degree:
            too_high += 1
        else:
            for m, _ in rows:
                bits |= m
            eligible.append((i, len(rows), rows))
    active = tuple(_bits(bits))
    out = dict(status='UNKNOWN', reason='constant_not_in_bounded_span', certificate=None,
               n=n, degree_limit=degree, max_rows=max_rows, events=len(raw),
               impossible_events=impossible, events_above_degree=too_high,
               eligible_events=len(eligible), active_variables=len(active), rows_generated=0,
               basis_rank=0, columns_seen=0)
    if not eligible:
        return out
    # Compact live-column IDs, never a bit at the (possibly huge) monomial
    # mask's numerical index. Reserve bit 0 for the constant monomial.
    ids, pivots, provenance, terms = {0:0}, {}, {}, []
    polynomials = {}
    max_size = min(len(active), degree-min(r for _,r,_ in eligible))
    for weight in range(max_size+1):
        for i, rank, eqs in eligible:
            if rank+weight > degree:
                continue
            for combo in combinations(active, weight):
                if max_rows is not None and len(terms) >= max_rows:
                    out.update(reason='row_budget_exhausted', columns_seen=len(ids))
                    return out
                if i not in polynomials:
                    polynomials[i] = _indicator(eqs)
                multiplier = sum(combo)
                row = 0
                for m in sorted(polynomials[i]):
                    mon = m | multiplier
                    col = ids.setdefault(mon, len(ids))
                    row ^= 1 << col
                tag = 1 << len(terms)
                terms.append((i,multiplier,rank+weight)); out['rows_generated'] += 1
                while row and row != 1:
                    p = row.bit_length()-1
                    if p not in pivots:
                        pivots[p] = row
                        provenance[p] = tag
                        out['basis_rank'] += 1
                        break
                    row ^= pivots[p]
                    tag ^= provenance[p]
                if row == 1:
                    chosen = [terms[b.bit_length()-1] for b in _bits(tag)]
                    cert = dict(kind=_KIND,n=n,degree=max(v[2] for v in chosen),
                                terms=[[j,z] for j,z,_ in chosen])
                    verify_cover_certificate(n, raw, cert, max_degree=degree)
                    out.update(status='UNSAT', reason='checked_constant_identity',
                               certificate=cert, columns_seen=len(ids), basis_rank=len(pivots)+1)
                    return out
    out['columns_seen'] = len(ids)
    return out
