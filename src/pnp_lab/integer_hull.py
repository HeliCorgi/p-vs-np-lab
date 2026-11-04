"""Compose local Boolean integer affine hulls without choosing a modulus.

The integer relaxation is only necessary for a Boolean model.  Its feasibility
is UNKNOWN for SAT.  Refutations are independently checked local truth-table
laws and one weighted sum; neither Smith traces nor global elimination belong
to that certificate's trust boundary.
"""
from collections import Counter
from itertools import combinations
from math import gcd

from .modular_hull import _input, _index, discover_scopes
from .cyclic_four import _columns, _domains, _index as _four_index
from .local_torsion import (MAX_D, MAX_MODELS, MAX_OPS as LOCAL_OPS,
                            MAX_BITS, torsion_table, check_local_torsion)

KIND = 'boolean-integer-hull-v1'


def _limit(value, name, ceiling=None):
    if type(value) is not int or value < 0 or (ceiling is not None and value > ceiling):
        raise ValueError('invalid ' + name)


def _named_scope(n, scope):
    if not isinstance(scope, (tuple, list)):
        raise ValueError('invalid local scope')
    s = tuple(scope)
    if (len(s) > MAX_D or any(type(v) is not int or not 1 <= v <= n for v in s)
            or len(set(s)) != len(s)):
        raise ValueError('invalid local scope')
    return tuple(sorted(s))


def integer_scopes(n, clauses):
    """Fixed-width raw scopes, plus proposed four-domain stars of width <=15.

    A candidate is merely a set of original variables: its actual relation is
    always read back from the original clauses.  No group labels are input.
    """
    cs = _input(n, clauses)
    scopes = set(discover_scopes(n, cs))
    signed, occ = _four_index(cs)
    blocks, owners = _domains(signed, occ)
    if blocks is not None:
        for c in signed:
            if not c or any(abs(l) not in owners for l in c):
                continue
            group = {owners[abs(l)] for l in c}
            if len(group) != 3:
                continue
            s = tuple(sorted(v for j in group
                             for v in (*map(abs, blocks[j][0]), blocks[j][1])))
            if len(s) <= MAX_D:
                scopes.add(s)
    return sorted(scopes, key=lambda s: (len(s), s))


def _local_table(idx, scope):
    cols = _columns(len(scope))
    full = (1 << (1 << len(scope))) - 1
    words = full
    pos = {v: j for j, v in enumerate(scope)}
    ids = []
    for d in range(min(3, len(scope)) + 1):
        for support in combinations(scope, d):
            for clause, ix in idx.get(support, {}).items():
                yes = 0
                for lit in clause:
                    col = cols[pos[abs(lit)]]
                    yes |= col if lit > 0 else full ^ col
                words &= yes
                ids.append(ix)
    return words, sorted(ids)


def _characters(cert, max_bits=MAX_BITS):
    """All exact and congruence rows from a verified local Smith trace."""
    n = cert['width'] + 1
    if max_bits < 1:
        raise OverflowError('local character bit cap')
    v = [[int(i == j) for j in range(n)] for i in range(n)]
    for op in cert['ops']:
        if op[0] == 'C':
            i, j = op[1:]
            for row in v:
                row[i], row[j] = row[j], row[i]
        elif op[0] == 'c':
            i, j, a = op[1:]
            for row in v:
                row[i] += a * row[j]
                if row[i].bit_length() > max_bits:
                    raise OverflowError('local character bit cap')
    diagonal = cert['diagonal']
    for j in range(n):
        d = diagonal[j] if j < len(diagonal) else 0
        if d != 1:
            yield [row[j] for row in v[:-1]], -v[-1][j], d


def _canonical(coeff, rhs, modulus):
    """Reduce common factors and the unimportant choice of sign."""
    g = modulus
    for x in (*coeff, rhs):
        g = gcd(g, x)
    if g > 1:
        coeff = [x // g for x in coeff]
        rhs //= g
        modulus //= g
    if modulus:
        if modulus == 1:
            return None
        coeff = [x % modulus for x in coeff]
        rhs %= modulus
        other = [(-x) % modulus for x in coeff]
        if (*other, (-rhs) % modulus) < (*coeff, rhs):
            coeff, rhs = other, (-rhs) % modulus
    else:
        first = next((x for x in (*coeff, rhs) if x), 0)
        if first < 0:
            coeff, rhs = [-x for x in coeff], -rhs
    if not rhs and not any(coeff):
        return None
    return coeff, rhs, modulus


def collect_integer_rows(n, clauses, *, scopes=None, max_scopes=None,
                         max_rows=2048, max_models=MAX_MODELS,
                         max_local_ops=LOCAL_OPS, max_bits=MAX_BITS):
    """Return checked necessary local integer laws and discovery statistics.

    ``scopes`` optionally fixes which raw-variable subsets to inspect.  Omitted
    means ``integer_scopes``.  A capped or skipped table supplies no assertion
    about the absence of further equations.
    """
    cs = _input(n, clauses)
    if max_scopes is not None:
        _limit(max_scopes, 'scope cap')
    _limit(max_rows, 'row cap')
    _limit(max_models, 'model cap', MAX_MODELS)
    _limit(max_local_ops, 'local operation cap', LOCAL_OPS)
    _limit(max_bits, 'integer bit cap', MAX_BITS)
    if scopes is None:
        todo = integer_scopes(n, cs)
    else:
        todo = sorted({_named_scope(n, s) for s in scopes}, key=lambda s: (len(s), s))
    stats = dict(scopes_available=len(todo), scopes_examined=0, scopes_profiled=0,
                 skipped_scopes=0, max_scope_size=0, local_assignments=0,
                 local_models=0, local_operations=0, exact_rows=0,
                 congruence_rows=0, duplicate_rows=0, local_rows=0,
                 max_local_law_bits=0,
                 local_torsion_histogram={}, skipped_reasons={},
                 scope_complete=True, budget_limited=False, stop_reason=None)
    profiles = Counter()
    skipped = Counter()
    idx = _index(cs)
    out = []
    seen = set()
    for scope in todo:
        if max_scopes is not None and stats['scopes_examined'] >= max_scopes:
            stats.update(budget_limited=True, scope_complete=False, stop_reason='scope cap')
            break
        stats['scopes_examined'] += 1
        stats['max_scope_size'] = max(stats['max_scope_size'], len(scope))
        stats['local_assignments'] += 1 << len(scope)
        words, ids = _local_table(idx, scope)
        p = torsion_table(len(scope), words, max_models=max_models,
                          max_ops=max_local_ops, max_bits=max_bits)
        stats['local_models'] += p['models']
        stats['local_operations'] += p['operations']
        if p['status'] == 'UNKNOWN':
            stats['skipped_scopes'] += 1
            stats.update(scope_complete=False, budget_limited=True)
            skipped[p['reason']] += 1
            continue
        # The local transform is checked against a separate raw evaluator.  It
        # is not required in the final proof: leaves are checked directly there.
        if not check_local_torsion(n, [cs[i] for i in ids], scope, p['certificate']):
            raise AssertionError('local integer trace failed independent replay')
        try:
            laws = list(_characters(p['certificate'], max_bits))
        except OverflowError:
            stats['skipped_scopes'] += 1
            stats.update(scope_complete=False, budget_limited=True)
            skipped['local character bit cap'] += 1
            continue
        stats['scopes_profiled'] += 1
        profiles[tuple(p['torsion'])] += 1
        for coeff, rhs, modulus in laws:
            law = _canonical(coeff, rhs, modulus)
            if law is None:
                continue
            coeff, rhs, modulus = law
            stats['max_local_law_bits'] = max(stats['max_local_law_bits'],
                                              *(x.bit_length() for x in (*coeff, rhs, modulus)))
            key = (tuple((v, a) for v, a in zip(scope, coeff) if a), rhs, modulus)
            if key in seen:
                stats['duplicate_rows'] += 1
                continue
            if len(out) >= max_rows:
                stats.update(scope_complete=False, budget_limited=True, stop_reason='row cap')
                break
            seen.add(key)
            out.append(dict(scope=list(scope), clauses=ids, coeff=coeff,
                            rhs=rhs, modulus=modulus))
            stats['congruence_rows' if modulus else 'exact_rows'] += 1
        if stats['stop_reason'] == 'row cap':
            break
    stats['local_rows'] = len(out)
    stats['local_torsion_histogram'] = {str(list(k)): v for k, v in sorted(profiles.items())}
    stats['skipped_reasons'] = dict(sorted(skipped.items()))
    return out, stats


class _Cap(Exception):
    pass


def _integer_eliminate(equations, *, max_ops=200000, max_bits=MAX_BITS):
    """Integer diagonalization by unimodular operations, with row combinations.

    Columns need not be retained once a pivot is isolated.  The successive
    diagonal entries need not divide one another: diagonal form already decides
    integer feasibility.  For a refuting row its gcd divides its coefficients
    before as well as after every unimodular column operation.
    """
    _limit(max_ops, 'global operation cap')
    _limit(max_bits, 'integer bit cap', MAX_BITS)
    todo = [(dict(a), b, {i: 1}) for i, (a, b) in enumerate(equations)]
    stats = dict(global_operations=0, integer_rank=0, max_coefficient_bits=0,
                 max_combination_bits=0, max_rhs_bits=0, max_diagonal_bits=0)

    def size(a, b, w):
        aa = max((x.bit_length() for x in a.values()), default=0)
        bb = b.bit_length()
        ww = max((x.bit_length() for x in w.values()), default=0)
        stats['max_coefficient_bits'] = max(stats['max_coefficient_bits'], aa)
        stats['max_rhs_bits'] = max(stats['max_rhs_bits'], bb)
        stats['max_combination_bits'] = max(stats['max_combination_bits'], ww)
        if max(aa, bb, ww) > max_bits:
            raise _Cap('global integer bit cap')

    def charge(count=1):
        if stats['global_operations'] + count > max_ops:
            raise _Cap('global operation cap')
        stats['global_operations'] += count

    def plus(a, c, b):
        d = a.copy()
        for j, v in b.items():
            u = d.get(j, 0) + c * v
            if u:
                d[j] = u
            else:
                d.pop(j, None)
        return d

    def subtract(row, q, pivot):
        charge()
        a, b, w = row
        c, d, u = pivot
        a, b, w = plus(a, -q, c), b - q * d, plus(w, -q, u)
        size(a, b, w)
        return a, b, w

    def answer(status, reason, proof=None, modulus=None, rhs=None):
        return dict(status=status, reason=reason, proof=proof,
                    modulus=modulus, residual_rhs=rhs, stats=stats)

    try:
        for row in todo:
            size(*row)
        while todo:
            for a, b, w in todo:
                if not a and b:
                    return answer('INCONSISTENT', 'exact integer contradiction', w, 0, b)
            todo = [row for row in todo if row[0]]
            if not todo:
                break
            # Unit pivots keep graph and local-domain examples sparse.  A
            # smallest available entry makes each nonunit Euclidean phase short.
            choice = next(((i, j) for i, (a, _, _) in enumerate(todo)
                           for j, x in a.items() if abs(x) == 1), None)
            if choice is None:
                _, i, j = min((abs(x), i, j) for i, (a, _, _) in enumerate(todo)
                              for j, x in a.items())
            else:
                i, j = choice
            pivot = todo.pop(i)
            while True:
                d = pivot[0][j]
                restart = False
                for i, row in enumerate(todo):
                    x = row[0].get(j, 0)
                    if not x:
                        continue
                    q, r = divmod(x, d)
                    if q:
                        row = subtract(row, q, pivot)
                        todo[i] = row
                    if r:
                        pivot, todo[i] = row, pivot
                        restart = True
                        break
                if restart:
                    continue
                # Column j is now zero in every other live row.  Therefore a
                # column addition into another live column changes only pivot.
                bad = next((k for k, x in pivot[0].items() if x % d), None)
                if bad is not None:
                    q, r = divmod(pivot[0][bad], d)
                    if q:
                        charge()
                        pivot[0][bad] = r
                    j = bad
                    continue
                g = abs(d)
                stats['max_diagonal_bits'] = max(stats['max_diagonal_bits'], g.bit_length())
                if pivot[1] % g:
                    return answer('INCONSISTENT', 'integer divisibility contradiction',
                                  pivot[2], g, pivot[1] % g)
                # All other pivot entries are integer multiples of d.  Clear
                # them by column additions; no other live row changes.  The
                # isolated equation d*y=b is integrally solvable and is removed.
                charge(len(pivot[0]) - 1)
                stats['integer_rank'] += 1
                break
        return answer('FEASIBLE', 'integer relaxation feasible')
    except _Cap as cap:
        return answer('UNKNOWN', str(cap))


def _checker_words(cs, scope, ids):
    """Independent Boolean enumeration, pruning only cited original clauses."""
    pos = {v: j for j, v in enumerate(scope)}
    ends = [[] for _ in scope]
    for ix in ids:
        c = cs[ix]
        if not c:
            return []
        if any(abs(l) not in pos for l in c):
            raise ValueError('clause outside local scope')
        row = [(pos[abs(l)], l > 0) for l in c]
        ends[max(j for j, _ in row)].append(row)
    words = [0]
    for j, clauses in enumerate(ends):
        nxt = []
        for x in words:
            for y in (x, x | (1 << j)):
                if all(any(bool(y >> h & 1) == sign for h, sign in c) for c in clauses):
                    nxt.append(y)
        words = nxt
    return words


def _row_data(n, cs, row, cache):
    s = row['scope']
    if not isinstance(s, (list, tuple)):
        raise ValueError('invalid certificate scope')
    # Unlike discovery, preserve the presented order: it names coefficients.
    if (len(s) > MAX_D or any(type(v) is not int or not 1 <= v <= n for v in s)
            or len(set(s)) != len(s)):
        raise ValueError('invalid certificate scope')
    ids, a, b, d = row['clauses'], row['coeff'], row['rhs'], row['modulus']
    if (not isinstance(ids, (tuple, list))
            or any(type(i) is not int or not 0 <= i < len(cs) for i in ids)
            or not isinstance(a, (tuple, list)) or len(a) != len(s)
            or any(type(x) is not int or x.bit_length() > MAX_BITS for x in a)
            or type(b) is not int or b.bit_length() > MAX_BITS
            or type(d) is not int or d < 0 or d == 1 or d.bit_length() > MAX_BITS):
        raise ValueError('invalid integer row')
    key = (tuple(s), tuple(ids))
    if key not in cache:
        cache[key] = _checker_words(cs, s, ids)
    for x in cache[key]:
        residual = sum(v for j, v in enumerate(a) if x >> j & 1) - b
        if (residual % d if d else residual):
            raise ValueError('false local integer law')
    return s, a, b, d


def check_integer_row(n, clauses, row):
    """Check one local affine integer/congruence law from cited raw clauses."""
    try:
        _row_data(n, _input(n, clauses), row, {})
        return True
    except (ValueError, TypeError, KeyError, IndexError, AttributeError):
        return False


def check_integer_hull(n, clauses, cert):
    """Raw-CNF checker; no discovery, Smith algorithm, or solver is called."""
    try:
        cs = _input(n, clauses)
        if not isinstance(cert, dict) or cert.get('kind') != KIND:
            return False
        m, terms = cert['modulus'], cert['terms']
        if (type(m) is not int or m < 0 or m == 1 or m.bit_length() > MAX_BITS
                or not isinstance(terms, list) or not terms):
            return False
        total = {}
        rhs = 0
        cache = {}
        for row in terms:
            s, a, b, d = _row_data(n, cs, row, cache)
            w = row['weight']
            if type(w) is not int or w.bit_length() > MAX_BITS:
                return False
            if (w * d % m if m else w * d):
                return False
            for v, x in zip(s, a):
                total[v] = total.get(v, 0) + w * x
            rhs += w * b
        if m:
            rhs %= m
            if any(x % m for x in total.values()):
                return False
        elif any(total.values()):
            return False
        return rhs != 0 and type(cert['residual_rhs']) is int and rhs == cert['residual_rhs']
    except (ValueError, TypeError, KeyError, IndexError, AttributeError):
        return False


def integer_hull_refute(n, clauses, *, scopes=None, max_scopes=None,
                        max_rows=2048, max_columns=2048, max_ops=200000,
                        max_bits=MAX_BITS, max_models=MAX_MODELS,
                        max_local_ops=LOCAL_OPS):
    """Refute a composed integer affine relaxation, or return UNKNOWN.

    Feasibility is not a Boolean witness.  All output refutations are rechecked
    against the original clauses before being returned.
    """
    cs = _input(n, clauses)
    _limit(max_columns, 'column cap')
    _limit(max_ops, 'global operation cap')
    rows, stats = collect_integer_rows(
        n, cs, scopes=scopes, max_scopes=max_scopes, max_rows=max_rows,
        max_models=max_models, max_local_ops=max_local_ops, max_bits=max_bits)
    equations = []
    cols = set()
    for i, row in enumerate(rows):
        a = {v: c for v, c in zip(row['scope'], row['coeff']) if c}
        if row['modulus']:
            a[-i - 1] = -row['modulus']  # A distinct unrestricted integer slack.
        equations.append((a, row['rhs']))
        cols.update(a)
    stats.update(integer_rows=len(rows), integer_columns=len(cols),
                 integer_slack_columns=sum(bool(r['modulus']) for r in rows),
                 integer_feasible=None, discovered_modulus=None)
    if len(cols) > max_columns:
        stats.update(budget_limited=True)
        return dict(status='UNKNOWN', reason='global column cap', witness=None,
                    certificate=None, stats=stats)
    solved = _integer_eliminate(equations, max_ops=max_ops, max_bits=max_bits)
    stats.update(solved['stats'])
    if solved['status'] != 'INCONSISTENT':
        stats['integer_feasible'] = True if solved['status'] == 'FEASIBLE' else None
        if solved['status'] == 'UNKNOWN':
            stats['budget_limited'] = True
        return dict(status='UNKNOWN', reason=solved['reason'], witness=None,
                    certificate=None, stats=stats)
    m = solved['modulus']
    terms = []
    for i, weight in sorted(solved['proof'].items()):
        if m:
            weight %= m
        if weight:
            terms.append(dict(rows[i], weight=weight))
    rhs = sum(t['weight'] * t['rhs'] for t in terms)
    if m:
        rhs %= m
    cert = dict(kind=KIND, modulus=m, residual_rhs=rhs, terms=terms)
    if not check_integer_hull(n, cs, cert):
        raise AssertionError('global integer proof failed independent raw check')
    stats.update(integer_feasible=False, discovered_modulus=m,
                 certificate_terms=len(terms), residual_rhs=rhs)
    return dict(status='UNSAT', reason=solved['reason'], witness=None,
                certificate=cert, stats=stats)
