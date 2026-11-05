"""Proof-carrying binary implications feed learned clauses to local integer laws.

Discovery uses only the original signed width-three CNF.  Every returned
contradiction is checked without the anchor heuristic, graph search or integer
eliminator.  Feasibility of the projected integer relaxation means UNKNOWN.
"""
from collections import Counter, defaultdict, deque
import json

from .integer_hull import check_integer_hull, integer_hull_refute, KIND as INTEGER_KIND
from .local_torsion import MAX_BITS, MAX_MODELS, MAX_OPS
from .modular_hull import _input

KIND = 'binary-path-integer-feedback-v1'
MAX_LEMMAS = 50000
MAX_PATH_STEPS = 1000000


def _cap(v, name, *, optional=True, ceiling=None):
    if v is None and optional:
        return
    if type(v) is not int or v < 0 or (ceiling is not None and v > ceiling):
        raise ValueError('invalid ' + name)


def _canonical(clause):
    """Signed set of literals in original labels; None for a tautology."""
    row = set(clause)
    return None if any(-l in row for l in row) else tuple(sorted(row, key=abs))


class _Limited(Exception):
    pass


def learn_anchor_clauses(n, clauses, *, max_edges=2000000, max_lemmas=MAX_LEMMAS,
                         max_path_steps=MAX_PATH_STEPS):
    """Keep raw anchor clauses; lift a private literal in a ternary premise.

    Here 'private' means non-anchor, not necessarily a single occurrence.
    A signed path entry +/- (i+1) denotes the forward/reverse orientation of
    the original binary row at zero-based index i.  Stop each BFS at anchors.
    Incomplete discovery returns no projected formula and no lemmas.
    """
    for value, name in ((max_edges, 'edge visits'), (max_lemmas, 'lemma count'),
                        (max_path_steps, 'stored path steps')):
        _cap(value, name)
    cs = _input(n, clauses)
    raw, binary, count = {}, {}, Counter()
    for i, c in enumerate(cs):
        row = _canonical(c)
        if row is None:
            continue
        if row not in raw:
            raw[row] = i
            if len(row) == 3:
                count.update(map(abs, row))
        if len(c) == len(row) == 2:
            binary.setdefault(row, i)
    anchors = {v for v, k in count.items() if k >= 2}
    adj = defaultdict(list)
    for i in binary.values():
        a, b = cs[i]
        adj[-a].append((b, i+1))
        adj[-b].append((a, -i-1))
    stats = dict(input_clauses=len(cs), distinct_raw=len(raw), anchors=len(anchors),
                 binary_arcs=2*len(binary), active_variables=len({abs(l) for c in cs for l in c}),
                 max_input_label_bits=max((abs(l).bit_length() for c in cs for l in c), default=0),
                 retained_raw=0, learned_clauses=0, path_steps=0, bfs_runs=0,
                 edges_visited=0, candidate_endpoints=0, max_path_length=0,
                 peak_bfs_vertices=0, budget_limited=False)
    proofs = {}
    starts = defaultdict(list)
    try:
        for c, i in raw.items():
            outside = [l for l in c if abs(l) not in anchors]
            if not outside:
                if max_lemmas is not None and len(proofs) >= max_lemmas:
                    raise _Limited('lemma cap')
                proofs[c] = dict(raw=i, clause=list(c))
                stats['retained_raw'] += 1
            elif len(c) == 3 and len(outside) == 1:
                start = outside[0]
                starts[start].append((i, tuple(l for l in c if l != start)))

        for start, sources in starts.items():
            stats['bfs_runs'] += 1
            parent = {start: None}
            depth = {start: 0}
            queue = deque([start])
            stats['peak_bfs_vertices'] = max(stats['peak_bfs_vertices'], 1)
            while queue:
                u = queue.popleft()
                for v, edge in adj.get(u, ()):
                    if max_edges is not None and stats['edges_visited'] >= max_edges:
                        raise _Limited('edge visit cap')
                    stats['edges_visited'] += 1
                    if v in parent:
                        continue
                    parent[v] = (u, edge)
                    depth[v] = depth[u]+1
                    stats['peak_bfs_vertices'] = max(stats['peak_bfs_vertices'], len(parent))
                    if abs(v) not in anchors:
                        queue.append(v)
                        continue
                    for i, context in sources:
                        stats['candidate_endpoints'] += 1
                        out = _canonical((*context, v))
                        if out is None or out in proofs:
                            continue
                        if max_lemmas is not None and len(proofs) >= max_lemmas:
                            raise _Limited('lemma cap')
                        if max_path_steps is not None and stats['path_steps'] + depth[v] > max_path_steps:
                            raise _Limited('stored path cap')
                        path, cursor = [], v
                        while cursor != start:
                            cursor, e = parent[cursor]
                            path.append(e)
                        path.reverse()
                        proofs[out] = dict(raw=i, start=start, path=path, clause=list(out))
                        stats['learned_clauses'] += 1
                        stats['path_steps'] += len(path)
                        stats['max_path_length'] = max(stats['max_path_length'], len(path))
    except _Limited as e:
        stats['budget_limited'] = True
        return dict(complete=False, reason=str(e), clauses=[], lemmas=[], stats=stats)
    keys = sorted(proofs)
    return dict(complete=True, reason='anchor projection complete',
                clauses=[list(c) for c in keys], lemmas=[proofs[c] for c in keys], stats=stats)


def replay_feedback_lemmas(n, clauses, lemmas, *, max_lemmas=MAX_LEMMAS,
                           max_path_steps=MAX_PATH_STEPS):
    """Reconstruct each claimed clause by its original premises, or raise.

    No anchors, reachability labels, candidate generation or arithmetic enter
    this replay. Other valid input/implication derivations can be checked.
    """
    _cap(max_lemmas, 'lemma count')
    _cap(max_path_steps, 'stored path steps')
    cs = _input(n, clauses)
    if not isinstance(lemmas, list) or (max_lemmas is not None and len(lemmas) > max_lemmas):
        raise ValueError('invalid lemma list or lemma cap')
    rows = []
    steps = 0
    for node in lemmas:
        if not isinstance(node, dict) or set(node) not in ({'raw','clause'}, {'raw','clause','start','path'}):
            raise ValueError('invalid feedback node')
        i = node['raw']
        if type(i) is not int or not 0 <= i < len(cs):
            raise ValueError('invalid raw source')
        c = set(cs[i])
        if any(-l in c for l in c):
            raise ValueError('tautological raw source')
        if 'path' in node:
            lit, path = node['start'], node['path']
            if type(lit) is not int or lit not in c or not isinstance(path, list) or not path:
                raise ValueError('invalid initial implication')
            if max_path_steps is not None and steps+len(path) > max_path_steps:
                raise ValueError('path replay cap')
            steps += len(path)
            c.remove(lit)
            for e in path:
                if type(e) is not int or not 1 <= abs(e) <= len(cs):
                    raise ValueError('invalid signed binary clause id')
                pair = cs[abs(e)-1]
                if len(pair) != 2 or abs(pair[0]) == abs(pair[1]):
                    raise ValueError('not a proper raw binary clause')
                # A forward edge on the presented clause (p,q) means not p -> q.
                a, b = pair if e > 0 else pair[::-1]
                if a != -lit:
                    raise ValueError('implication path is disconnected')
                lit = b
            c.add(lit)
        row = node['clause']
        if (not isinstance(row, list) or len(row) > 3 or
                any(type(l) is not int or not 1 <= abs(l) <= n for l in row) or
                any(-l in c for l in c) or row != sorted(c, key=abs)):
            raise ValueError('wrong feedback conclusion')
        rows.append(tuple(row))
    return tuple(rows)


def check_integer_feedback(n, clauses, cert, *, max_lemmas=MAX_LEMMAS,
                           max_path_steps=MAX_PATH_STEPS):
    """Verify the raw path lemmas, then a width-at-most-three integer certificate."""
    try:
        if (not isinstance(cert, dict) or set(cert) != {'kind','variables','lemmas','integer'}
                or cert['kind'] != KIND or type(cert['variables']) is not int
                or cert['variables'] != n):
            return False
        rows = replay_feedback_lemmas(n, clauses, cert['lemmas'], max_lemmas=max_lemmas,
                                      max_path_steps=max_path_steps)
        proof = cert['integer']
        if (not isinstance(proof, dict) or not isinstance(proof.get('terms'),list) or
                any(not isinstance(t,dict) or not isinstance(t.get('scope'),list) or
                    len(t['scope']) > 3 for t in proof['terms'])):
            return False
        return check_integer_hull(n, rows, proof)
    except (TypeError, ValueError, AttributeError, IndexError, KeyError):
        return False


def _parity_sum(rows):
    """Look for exactly a parity half-cube at each derived triple support."""
    blocks = defaultdict(list)
    for i, c in enumerate(rows):
        if len(c) == 3:
            blocks[tuple(map(abs,c))].append(i)
    terms, odd = [], set()
    rhs = 0
    for scope, ids in sorted(blocks.items()):
        mask = 0
        for word in range(8):
            if all(any(bool(word & (1<<j)) == (l>0) for j,l in enumerate(rows[ix]))
                   for ix in ids):
                mask |= 1<<word
        if mask not in (0b01101001, 0b10010110):
            continue
        b = int(mask == 0b10010110)
        rhs ^= b
        odd.symmetric_difference_update(scope)
        terms.append(dict(scope=list(scope), clauses=ids, coeff=[1,1,1],
                          rhs=b, modulus=2, weight=1))
    stats = dict(triples_scanned=len(blocks), table_cells=8*len(blocks),
                 parity_rows=len(terms), odd_columns=len(odd), xor_rhs=rhs)
    if terms and not odd and rhs:
        return dict(kind=INTEGER_KIND, terms=terms, modulus=2, residual_rhs=rhs), stats
    return None, stats


def integer_feedback_refute(n, clauses, *, max_edges=2000000, max_lemmas=MAX_LEMMAS,
                           max_path_steps=MAX_PATH_STEPS, use_parity_sum=True,
                           use_signed_column=True, **integer_limits):
    """Refute using raw consequences; feasible relaxations and caps give UNKNOWN.

    The explicit local Z/2 sum is tested before general integer elimination.
    integer_limits only control the latter, not the independently bounded lift
    or the eight-cells-per-triple parity scan.
    """
    if type(use_parity_sum) is not bool or type(use_signed_column) is not bool:
        raise ValueError('invalid shortcut option')
    ceilings = dict(max_scopes=None, max_rows=None, max_columns=None, max_ops=None,
                    max_bits=MAX_BITS, max_models=MAX_MODELS, max_local_ops=MAX_OPS)
    for key, val in integer_limits.items():
        if key not in ceilings:
            raise ValueError('unsupported integer option: '+key)
        _cap(val, key, optional=key=='max_scopes', ceiling=ceilings[key])
    cs = _input(n, clauses)
    p = learn_anchor_clauses(n, cs, max_edges=max_edges, max_lemmas=max_lemmas,
                             max_path_steps=max_path_steps)
    stats = dict(p['stats'], backend='none', integer=None, parity=None, signed_column=None)
    if not p['complete']:
        return dict(status='UNKNOWN', reason=p['reason'], witness=None, certificate=None, stats=stats)
    rows = p['clauses']
    proof = None
    if use_parity_sum:
        proof, stats['parity'] = _parity_sum(rows)
    if proof is not None:
        stats['backend'] = 'parity_sum'
    elif use_signed_column and set(integer_limits) <= {'max_bits'}:
        from .one_column_feedback import one_column_certificate
        proof, info = one_column_certificate(n, rows, max_bits=integer_limits.get('max_bits', MAX_BITS))
        stats['signed_column'] = info
        stats['budget_limited'] |= info['budget_limited']
        if proof is not None:
            stats['backend'] = 'signed_column'
    if proof is None:
        scopes = {tuple(map(abs,c)) for c in rows}
        answer = integer_hull_refute(n, rows, scopes=scopes, **integer_limits)
        stats['backend'] = 'integer_hull'
        stats['integer'] = answer['stats']
        stats['budget_limited'] |= answer['stats']['budget_limited']
        if answer['status'] != 'UNSAT':
            return dict(status='UNKNOWN', reason=answer['reason'], witness=None, certificate=None, stats=stats)
        proof = answer['certificate']
    else:
        stats['integer'] = dict(discovered_modulus=proof['modulus'], residual_rhs=proof['residual_rhs'],
                                certificate_terms=len(proof['terms']))
    cert = dict(kind=KIND, variables=n, lemmas=p['lemmas'], integer=proof)
    if not check_integer_feedback(n, cs, cert, max_lemmas=max_lemmas, max_path_steps=max_path_steps):
        raise AssertionError('integer feedback certificate failed original-clause replay')
    try:
        stats['certificate_bytes'] = len(json.dumps(cert, sort_keys=True, separators=(',',':')).encode())
    except ValueError:
        # An unusually large integer label can exceed Python's configured
        # decimal conversion limit. Serialization size is optional metadata.
        stats['certificate_bytes'] = None
    return dict(status='UNSAT', reason='checked implication paths and weighted integer contradiction',
                witness=None, certificate=cert, stats=stats)
