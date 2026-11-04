"""Exact Boolean join/project proof replay on original variable coordinates.

This checker does not call resolution, arithmetic inference, or proof search.
Every joined assignment has one shared value for each common variable.
"""
import json

from .modular_hull import _input

KIND = 'boolean-relation-join-project-v1'
MAX_UNION = 12


def _cap(value, name):
    if type(value) is not int or value < 0:
        raise ValueError('invalid ' + name)


def _scope(n, values):
    if not isinstance(values, list) or any(type(v) is not int or not 1 <= v <= n for v in values):
        raise ValueError('invalid relation scope')
    if values != sorted(set(values)) or len(values) > MAX_UNION:
        raise ValueError('relation scope must be sorted and distinct')
    return tuple(values)


def _project_word(word, positions):
    return sum(((word >> j) & 1) << i for i, j in enumerate(positions))


def _replay(n, clauses, certificate, *, max_union_width=MAX_UNION,
            max_nodes=200000, max_cells=5000000):
    cs = _input(n, clauses)
    for value, name in ((max_union_width, 'union width'), (max_nodes, 'node cap'),
                        (max_cells, 'table-cell cap')):
        _cap(value, name)
    if max_union_width > MAX_UNION:
        raise ValueError('union width exceeds checker limit')
    if not isinstance(certificate, dict) or certificate.get('kind') != KIND:
        raise ValueError('unrecognized relation proof')
    if type(certificate.get('variables')) is not int or certificate['variables'] != n:
        raise ValueError('wrong original variable bound')
    nodes = certificate['nodes']
    if not isinstance(nodes, list) or not nodes or len(nodes) > max_nodes:
        raise ValueError('invalid node count')
    if type(certificate['root']) is not int or certificate['root'] != len(nodes) - 1:
        raise ValueError('root must be the last node')
    claimed = certificate['union_width']
    if type(claimed) is not int or not 0 <= claimed <= max_union_width:
        raise ValueError('invalid declared union width')
    relations = []
    stats = dict(nodes=len(nodes), inputs=0, joins=0, union_width=0,
                 max_relation_width=0, enumerated_cells=0, stored_table_cells=0)
    for i, node in enumerate(nodes):
        if not isinstance(node, dict):
            raise ValueError('invalid proof node')
        scope = _scope(n, node['scope'])
        table = node['table']
        if type(table) is not int or table < 0 or table.bit_length() > 1 << len(scope):
            raise ValueError('invalid Boolean relation table')
        if node['op'] == 'input':
            clause = node['clause']
            if type(clause) is not int or not 0 <= clause < len(cs):
                raise ValueError('invalid original clause index')
            if set(scope) != {abs(l) for l in cs[clause]}:
                raise ValueError('input scope differs from original clause')
            union = scope
        elif node['op'] == 'join-project':
            left, right = node['left'], node['right']
            if any(type(j) is not int or not 0 <= j < i for j in (left, right)):
                raise ValueError('a parent is missing or not earlier')
            s, a = relations[left]
            t, b = relations[right]
            union = tuple(sorted(set(s) | set(t)))
            if not set(scope).issubset(union):
                raise ValueError('projection introduced a coordinate')
        else:
            raise ValueError('unrecognized inference')
        width = len(union)
        if width > claimed:
            raise ValueError('intermediate union exceeds declared width')
        cells = 1 << width
        stats['enumerated_cells'] += cells
        if stats['enumerated_cells'] > max_cells:
            raise ValueError('table-cell cap exceeded')
        stats['union_width'] = max(stats['union_width'], width)
        stats['max_relation_width'] = max(stats['max_relation_width'], len(scope))
        stats['stored_table_cells'] += 1 << len(scope)
        expected = 0
        if node['op'] == 'input':
            position = {v: j for j, v in enumerate(scope)}
            for word in range(cells):
                if any(bool(word >> position[abs(l)] & 1) == (l > 0) for l in cs[clause]):
                    expected |= 1 << word
            stats['inputs'] += 1
        else:
            position = {v: j for j, v in enumerate(union)}
            lp = tuple(position[v] for v in s)
            rp = tuple(position[v] for v in t)
            out = tuple(position[v] for v in scope)
            for word in range(cells):
                if ((a >> _project_word(word, lp)) & 1) and ((b >> _project_word(word, rp)) & 1):
                    expected |= 1 << _project_word(word, out)
            stats['joins'] += 1
        if table != expected:
            raise ValueError('declared table is not the exact join/projection')
        relations.append((scope, table))
    if claimed != stats['union_width']:
        raise ValueError('declared union width is not actual width')
    if relations[-1][1] != 0:
        raise ValueError('final relation is not empty')
    return stats


def check_relation_proof(n, clauses, certificate, **limits):
    """Return True only for a checked empty relation from the original clauses."""
    try:
        _replay(n, clauses, certificate, **limits)
        return True
    except (ValueError, TypeError, KeyError, IndexError, AttributeError, OverflowError):
        return False


def resolution_to_relations(n, clauses, certificate, *, max_union_width=MAX_UNION,
                            max_nodes=200000, max_cells=5000000):
    """Compile a checked resolution proof to independently replayed exact tables.

    The local table compiler uses clause semantics.  The checker above instead
    joins the parent relations and projects them, independently of resolution.
    """
    from .resolution_closure import ResolutionReplayLimit, replay_resolution
    cs = _input(n, clauses)
    for value, name in ((max_union_width, 'union width'), (max_nodes, 'node cap'),
                        (max_cells, 'table-cell cap')):
        _cap(value, name)
    if max_union_width > MAX_UNION:
        raise ValueError('union width exceeds checker limit')
    nodes = []
    union_width = 0
    cells = 0
    def limited(reason):
        return dict(status='UNKNOWN', reason=reason, witness=None, certificate=None,
                    stats=dict(compiled_nodes=len(nodes), enumerated_cells=cells,
                               union_width=union_width, budget_limited=True))
    try:
        rows = replay_resolution(n, cs, certificate, max_nodes=max_nodes,
                                 max_width=max_union_width, max_literal_occurrences=max_cells)
    except ResolutionReplayLimit as exc:
        return limited(str(exc))
    except (ValueError, TypeError, KeyError, IndexError, AttributeError) as exc:
        raise ValueError('invalid source resolution certificate') from exc
    for i, step in enumerate(certificate['nodes']):
        if len(nodes) >= max_nodes:
            return limited('relation node cap')
        if step['op'] == 'input':
            row = rows[i]
            node = dict(op='input', clause=step['clause'])
            width = len({abs(l) for l in row})
        else:
            left, right, pivot = step['left'], step['right'], step['pivot']
            a, b = rows[left], rows[right]
            row = rows[i]
            node = dict(op='join-project', left=left, right=right)
            width = len({abs(l) for l in a | b})
        union_width = max(union_width, width)
        if width > max_union_width:
            return limited('intermediate relation union cap')
        if cells + (1 << width) > max_cells:
            return limited('relation table-cell cap')
        cells += 1 << width
        scope = sorted({abs(l) for l in row})
        # A proper clause permits every word except its one falsifying word.
        bad = sum((1 << j) for j, v in enumerate(scope) if -v in row)
        table = ((1 << (1 << len(scope))) - 1) ^ (1 << bad)
        node.update(scope=scope, table=table)
        nodes.append(node)
    cert = dict(kind=KIND, variables=n, union_width=union_width, nodes=nodes,
                root=len(nodes) - 1)
    stats = _replay(n, cs, cert, max_union_width=max_union_width,
                    max_nodes=max_nodes, max_cells=max_cells)
    stats.update(budget_limited=False,
                 certificate_bytes=len(json.dumps(cert, separators=(',', ':'), sort_keys=True).encode()))
    return dict(status='UNSAT', reason='checked empty exact relation', witness=None,
                certificate=cert, stats=stats)
