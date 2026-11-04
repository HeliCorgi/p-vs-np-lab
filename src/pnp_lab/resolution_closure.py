"""Bounded-width ordinary resolution, with independent proof and closure checks.

A successful proof is pruned to the ancestors of its empty clause.  Exhausting
a width-bounded closure proves only the absence of a proof at that width; it
does not prove SAT.  Discovery receives only the original Boolean CNF.
"""
from collections import Counter, defaultdict
from itertools import combinations
import heapq
import json

from .modular_hull import _input

KIND = 'boolean-resolution-v1'
CLOSURE_KIND = 'bounded-resolution-closure-v1'


class ResolutionReplayLimit(ValueError):
    """A validly shaped proof exceeded a caller's replay resource budget."""


def _nonnegative(value, name, optional=False):
    if optional and value is None:
        return
    if type(value) is not int or value < 0:
        raise ValueError('invalid ' + name)


def replay_resolution(n, clauses, certificate, *, max_nodes=None,
                      max_width=None, max_literal_occurrences=None):
    """Return independently reconstructed clauses, or raise ValueError.

    This verifier uses sets of signed literals, not the finder's integer masks,
    scheduling, subsumption, or candidate-pair indexes.
    """
    cs = _input(n, clauses)
    for value, name in ((max_nodes, 'replay-node cap'), (max_width, 'replay-width cap'),
                        (max_literal_occurrences, 'replay-literal cap')):
        _nonnegative(value, name, optional=True)
    if (not isinstance(certificate, dict) or
            certificate.get('kind') != KIND or
            set(certificate) != {'kind', 'width', 'nodes', 'root'}):
        raise ValueError('invalid resolution certificate')
    width, nodes, root = certificate['width'], certificate['nodes'], certificate['root']
    _nonnegative(width, 'proof width')
    if (not isinstance(nodes, list) or not nodes or type(root) is not int or
            root != len(nodes)-1):
        raise ValueError('invalid resolution root')
    if max_nodes is not None and len(nodes) > max_nodes:
        raise ResolutionReplayLimit('resolution replay node cap')
    rows = []
    literal_occurrences = 0
    for i, node in enumerate(nodes):
        if not isinstance(node, dict):
            raise ValueError('invalid resolution node')
        if node.get('op') == 'input':
            if set(node) != {'op', 'clause'}:
                raise ValueError('invalid input node')
            index = node['clause']
            if type(index) is not int or not 0 <= index < len(cs):
                raise ValueError('invalid original clause index')
            row = frozenset(cs[index])
        elif node.get('op') == 'resolve':
            if set(node) != {'op', 'left', 'right', 'pivot'}:
                raise ValueError('invalid resolution step')
            left, right, pivot = node['left'], node['right'], node['pivot']
            if (type(left) is not int or type(right) is not int or
                    not 0 <= left < i or not 0 <= right < i or
                    type(pivot) is not int or not 1 <= abs(pivot) <= n):
                raise ValueError('invalid resolution parent or pivot')
            a, b = rows[left], rows[right]
            if pivot not in a or -pivot not in b:
                raise ValueError('parents do not contain the specified pivot signs')
            row = (a - {pivot}) | (b - {-pivot})
        else:
            raise ValueError('unknown resolution rule')
        if len(row) > width or any(-l in row for l in row):
            raise ValueError('wide or tautological proof line')
        if max_width is not None and len(row) > max_width:
            raise ResolutionReplayLimit('resolution replay width cap')
        literal_occurrences += len(row)
        if (max_literal_occurrences is not None and
                literal_occurrences > max_literal_occurrences):
            raise ResolutionReplayLimit('resolution replay literal cap')
        rows.append(row)
    if rows[root]:
        raise ValueError('proof does not end with the empty clause')
    return tuple(rows)


def check_resolution(n, clauses, certificate, *, max_nodes=None,
                     max_width=None, max_literal_occurrences=None):
    try:
        replay_resolution(n, clauses, certificate, max_nodes=max_nodes,
                          max_width=max_width, max_literal_occurrences=max_literal_occurrences)
        return True
    except (ValueError, TypeError, KeyError, IndexError, AttributeError):
        return False


def check_width_closure(n, clauses, certificate):
    """Check absence of an ordinary resolution refutation at the claimed width.

    Every usable input axiom must be covered by a stored subclause, and every
    usable resolvent of stored clauses must be so covered.  No empty clause is
    allowed.  This is a bounded-proof obstruction certificate, never a SAT word.
    """
    try:
        cs = _input(n, clauses)
        if (not isinstance(certificate, dict) or
                certificate.get('kind') != CLOSURE_KIND or
                set(certificate) != {'kind', 'width', 'clauses'}):
            return False
        width, supplied = certificate['width'], certificate['clauses']
        _nonnegative(width, 'closure width')
        if not isinstance(supplied, list):
            return False
        rows = []
        for c in supplied:
            if (not isinstance(c, (tuple, list)) or not c or len(c) > width or
                    any(type(l) is not int or not 1 <= abs(l) <= n for l in c) or
                    len(set(c)) != len(c) or any(-l in c for l in c)):
                return False
            rows.append(frozenset(c))
        known = set(rows)
        if len(known) != len(rows):
            return False

        def covered(c):
            # Independent set-valued subset enumeration, with no finder state.
            values = tuple(c)
            return any(frozenset(s) in known for k in range(len(c)+1)
                       for s in combinations(values, k))

        for c in cs:
            c = frozenset(c)
            if len(c) <= width and not any(-l in c for l in c) and not covered(c):
                return False
        positive, negative = defaultdict(list), defaultdict(list)
        for i, c in enumerate(rows):
            for l in c:
                (positive if l > 0 else negative)[abs(l)].append(i)
        for v in positive.keys() & negative.keys():
            for i in positive[v]:
                for j in negative[v]:
                    r = (rows[i] - {v}) | (rows[j] - {-v})
                    if len(r) <= width and not any(-l in r for l in r) and not covered(r):
                        return False
        return True
    except (ValueError, TypeError, KeyError, IndexError, AttributeError):
        return False


class _Budget(Exception):
    pass


def _trim(nodes, root):
    needed, pending = set(), [root]
    while pending:
        i = pending.pop()
        if i in needed:
            continue
        needed.add(i)
        node = nodes[i]
        if node['op'] == 'resolve':
            pending.extend((node['left'], node['right']))
    ordered = sorted(needed)
    names = {old: new for new, old in enumerate(ordered)}
    trimmed = []
    for old in ordered:
        node = dict(nodes[old])
        if node['op'] == 'resolve':
            node['left'], node['right'] = names[node['left']], names[node['right']]
        trimmed.append(node)
    return trimmed, names[root]


def _proof_stats(cert, rows):
    nodes = cert['nodes']
    depths = []
    first = {}
    union_width = 0
    for i, (node, row) in enumerate(zip(nodes, rows)):
        if node['op'] == 'input':
            depths.append(0)
            continue
        a, b = node['left'], node['right']
        depths.append(1 + max(depths[a], depths[b]))
        union_width = max(union_width, len({abs(l) for l in rows[a] | rows[b]}))
        w = len(row)
        if w not in first:
            ancestors, pending = set(), [i]
            while pending:
                j = pending.pop()
                if j in ancestors:
                    continue
                ancestors.add(j)
                t = nodes[j]
                if t['op'] == 'resolve':
                    pending.extend((t['left'], t['right']))
            first[w] = dict(node=i, clause=sorted(row, key=lambda l: (abs(l), l)),
                            ancestor_nodes=len(ancestors),
                            raw_ancestors=sum(nodes[j]['op'] == 'input' for j in ancestors))
    inputs = sum(t['op'] == 'input' for t in nodes)
    return dict(certificate_nodes=len(nodes), certificate_inputs=inputs,
                certificate_resolutions=len(nodes)-inputs,
                certificate_width=max(map(len, rows), default=0),
                certificate_parent_union_width=union_width,
                certificate_depth=max(depths, default=0),
                certificate_bytes=len(json.dumps(cert, sort_keys=True,
                                                separators=(',', ':')).encode()),
                first_retained_derived_by_width={str(w): first[w] for w in sorted(first)})


def resolution_refute(n, clauses, *, width=4, max_rows=50000,
                      max_pairs=1000000, max_subsets=5000000):
    """Find a bounded-width refutation or report an explicit incomplete outcome.

    All caps count search work, not the final pruned proof.  None removes the
    corresponding resource cap.  With fixed width and no caps the finite
    saturation is complete for ordinary resolution of that width, not for SAT.
    """
    cs = _input(n, clauses)
    _nonnegative(width, 'resolution width')
    for value, name in ((max_rows, 'stored-row cap'), (max_pairs, 'pair cap'),
                        (max_subsets, 'subsumption cap')):
        _nonnegative(value, name, optional=True)
    # Compress names: declared but unused variables must not allocate n-bit masks.
    variables = sorted({abs(l) for c in cs for l in c})
    position = {v: i for i, v in enumerate(variables)}
    size = len(variables)
    full = (1 << size)-1
    masks, nodes, known, active = [], [], {}, set()
    occurrences, agenda = defaultdict(set), []
    stats = dict(width=width, source_clauses=len(cs), active_variables=size,
                 source_tautologies=0, source_over_width=0, pairs_checked=0,
                 tautological_pairs=0, width_rejections=0, subsumed_candidates=0,
                 duplicate_candidates=0, superset_checks=0, retired_rows=0,
                 subsumption_probes=0, agenda_pops=0, peak_active=0, peak_agenda=0,
                 budget_limited=False, complete=False)
    root = None
    reason = 'width closure exhausted'

    def literals(mask):
        while mask:
            bit = mask & -mask
            mask -= bit
            j = bit.bit_length()-1
            yield variables[j] if j < size else -variables[j-size]

    def encode(c):
        return sum(1 << (position[abs(l)] + (size if l < 0 else 0)) for l in c)

    def record(mask, node):
        if mask in known:
            stats['duplicate_candidates'] += 1
            return None
        sub = mask
        while True:
            if max_subsets is not None and stats['subsumption_probes'] >= max_subsets:
                raise _Budget('subsumption cap')
            stats['subsumption_probes'] += 1
            if sub in known:
                stats['subsumed_candidates'] += 1
                return None
            if not sub:
                break
            sub = (sub-1) & mask
        if max_rows is not None and len(masks) >= max_rows:
            raise _Budget('stored-row cap')
        i = len(masks)
        known[mask] = i
        masks.append(mask)
        nodes.append(node)
        if mask:
            keys = tuple(literals(mask))
            candidates = min((occurrences[l] for l in keys), key=len)
            stats['superset_checks'] += len(candidates)
            retired = [j for j in candidates if masks[j] & mask == mask]
        else:
            retired = list(active)
        for j in retired:
            active.remove(j)
            for l in literals(masks[j]):
                occurrences[l].remove(j)
        stats['retired_rows'] += len(retired)
        active.add(i)
        for l in literals(mask):
            occurrences[l].add(i)
        heapq.heappush(agenda, (mask.bit_count(), i))
        stats['peak_active'] = max(stats['peak_active'], len(active))
        stats['peak_agenda'] = max(stats['peak_agenda'], len(agenda))
        return i

    try:
        for index, c in enumerate(cs):
            c = frozenset(c)
            if any(-l in c for l in c):
                stats['source_tautologies'] += 1
                continue
            if len(c) > width:
                stats['source_over_width'] += 1
                continue
            i = record(encode(c), dict(op='input', clause=index))
            if i is not None and not masks[i]:
                root = i
                break
        while root is None and agenda:
            _, i = heapq.heappop(agenda)
            stats['agenda_pops'] += 1
            if i not in active:
                continue
            a = masks[i]
            pa, na = a & full, a >> size
            others = set()
            for l in literals(a):
                others.update(occurrences[-l])
            for j in sorted(others):
                if j not in active or i not in active:
                    continue
                if max_pairs is not None and stats['pairs_checked'] >= max_pairs:
                    raise _Budget('pair cap')
                stats['pairs_checked'] += 1
                b = masks[j]
                pb, nb = b & full, b >> size
                cross = (pa & nb) | (na & pb)
                if cross & (cross-1):
                    stats['tautological_pairs'] += 1
                    continue
                # Exactly one complementary pair; all remaining literals survive.
                mask = ((pa | pb) ^ cross) | (((na | nb) ^ cross) << size)
                if mask.bit_count() > width:
                    stats['width_rejections'] += 1
                    continue
                pivot = variables[cross.bit_length()-1]
                if not pa & cross:
                    pivot = -pivot
                k = record(mask, dict(op='resolve', left=i, right=j, pivot=pivot))
                if k is not None and not mask:
                    root = k
                    break
        if root is None:
            stats['complete'] = True
    except _Budget as exc:
        stats['budget_limited'] = True
        reason = str(exc)
    stats.update(stored_rows=len(masks), active_rows=len(active),
                 stored_literal_slots=sum(x.bit_count() for x in masks),
                 mask_coordinate_bits=2*size,
                 search_width_histogram={str(k): v for k, v in sorted(
                     Counter(x.bit_count() for x in masks).items())})
    if root is not None:
        trimmed, target = _trim(nodes, root)
        cert = dict(kind=KIND, width=width, nodes=trimmed, root=target)
        replayed = replay_resolution(n, cs, cert)
        stats.update(_proof_stats(cert, replayed))
        return dict(status='UNSAT', reason='checked empty-clause derivation',
                    witness=None, certificate=cert, closure_certificate=None, stats=stats)
    closure = None
    if stats['complete']:
        closure = dict(kind=CLOSURE_KIND, width=width,
                       clauses=[sorted(literals(masks[i]), key=lambda l: (abs(l), l))
                                for i in sorted(active)])
        if not check_width_closure(n, cs, closure):
            raise AssertionError('saturated resolution closure failed independent replay')
    return dict(status='UNKNOWN', reason=reason, witness=None, certificate=None,
                closure_certificate=closure, stats=stats)

