"""Original-variable parity trees, checked against raw falsified CNF clauses.

The checker only uses the explicitly represented questions and Gaussian
elimination on their answers.  It neither trusts a recognized parity block
nor imports an input equation.  The finder is incomplete: it recognizes
complete parity blocks in the CNF and converts an inconsistent subsystem
into a tree.  A consistent subsystem returns UNKNOWN.
"""
from collections import defaultdict


KIND = 'parity-query-tree-v1'


def _input(n, clauses):
    if type(n) is not int or n < 0 or isinstance(clauses, (str, bytes)):
        raise ValueError('invalid variable bound or clauses')
    result = []
    try:
        for clause in clauses:
            if isinstance(clause, (str, bytes)):
                raise ValueError('invalid clause')
            row = tuple(clause)
            if any(type(lit) is not int or not 1 <= abs(lit) <= n for lit in row):
                raise ValueError('invalid original literal')
            result.append(row)
    except TypeError as exc:
        raise ValueError('invalid clause sequence') from exc
    return tuple(result)


def _set_insert(basis, support, rhs):
    """Checker arithmetic uses sparse sets of original variable names."""
    row = set(support)
    while row:
        pivot = max(row)
        if pivot not in basis:
            out = dict(basis)
            out[pivot] = (frozenset(row), rhs)
            return out, False
        other, bit = basis[pivot]
        row.symmetric_difference_update(other)
        rhs ^= bit
    return basis, rhs == 1


def _set_forced(basis, variable):
    row, value = {variable}, 0
    while row:
        pivot = max(row)
        if pivot not in basis:
            return None
        other, bit = basis[pivot]
        row.symmetric_difference_update(other)
        value ^= bit
    return value


def check_parity_query(n, clauses, certificate):
    """Replay a finite binary tree without assuming any input parity equation.

    Nodes form a tree, not a DAG: every non-root node has one incoming edge,
    all children have larger indices, and there are no unreachable nodes.
    A clause leaf must be falsified by every solution of its path equations.
    An ``inconsistent`` leaf needs an actual inconsistent path.  Sparse sets
    avoid allocating up to the largest numerical variable label.
    """
    try:
        raw = _input(n, clauses)
        if (type(certificate) is not dict
                or set(certificate) != {'kind', 'root', 'nodes'}
                or certificate['kind'] != KIND
                or type(certificate['root']) is not int
                or certificate['root'] != 0
                or type(certificate['nodes']) is not list
                or not certificate['nodes']):
            return False
        nodes = certificate['nodes']
        incoming = [0] * len(nodes)
        for i, node in enumerate(nodes):
            if type(node) is not dict:
                return False
            fields = set(node)
            if fields == {'query', 'zero', 'one'}:
                query = node['query']
                if (type(query) is not list or not query
                        or any(type(v) is not int or not 1 <= v <= n for v in query)
                        or query != sorted(set(query))):
                    return False
                for answer in ('zero', 'one'):
                    child = node[answer]
                    if type(child) is not int or not i < child < len(nodes):
                        return False
                    incoming[child] += 1
            elif fields == {'clause'}:
                ix = node['clause']
                if type(ix) is not int or not 0 <= ix < len(raw):
                    return False
            elif fields == {'inconsistent'}:
                if node['inconsistent'] is not True:
                    return False
            else:
                return False
        if incoming[0] != 0 or any(count != 1 for count in incoming[1:]):
            return False
        stack = [(0, {}, False)]
        visited = 0
        while stack:
            ix, basis, inconsistent = stack.pop()
            visited += 1
            node = nodes[ix]
            if 'query' in node:
                for bit, side in enumerate(('zero', 'one')):
                    updated, bad = _set_insert(basis, node['query'], bit)
                    stack.append((node[side], updated, inconsistent or bad))
            elif 'inconsistent' in node:
                if not inconsistent:
                    return False
            elif not inconsistent:
                for literal in raw[node['clause']]:
                    if _set_forced(basis, abs(literal)) != int(literal < 0):
                        return False
        return visited == len(nodes)
    except (TypeError, ValueError, KeyError, IndexError, AttributeError):
        return False


def parity_query_stats(certificate):
    """Structural statistics for an already checked tree."""
    nodes = certificate['nodes']
    result = dict(nodes=len(nodes), leaves=0, queries=0, inconsistent_leaves=0,
                  max_depth=0, max_query_support=0, query_variable_occurrences=0)
    stack = [(certificate['root'], 0)]
    while stack:
        ix, depth = stack.pop()
        result['max_depth'] = max(result['max_depth'], depth)
        node = nodes[ix]
        if 'query' in node:
            result['queries'] += 1
            result['max_query_support'] = max(result['max_query_support'], len(node['query']))
            result['query_variable_occurrences'] += len(node['query'])
            stack.extend((node[side], depth + 1) for side in ('zero', 'one'))
        else:
            result['leaves'] += 1
            result['inconsistent_leaves'] += 'inconsistent' in node
    return result


def _blocks(raw, positions):
    """Recognize a complete forbidden half-cube by counting distinct patterns.

    This scan does not enumerate absent assignments or all variable scopes.
    A repeated raw clause is only one pattern; a tautology gives no equation.
    """
    groups = defaultdict(dict)
    for ix, clause in enumerate(raw):
        signs = frozenset(clause)
        if any(-lit in signs for lit in signs):
            continue
        scope = tuple(sorted(abs(lit) for lit in signs))
        if not scope:
            continue
        pattern = sum(1 << j for j, v in enumerate(scope) if -v in signs)
        groups[scope].setdefault(pattern, ix)
    blocks = []
    for scope, patterns in sorted(groups.items()):
        mask = sum(1 << positions[v] for v in scope)
        for forbidden in (0, 1):
            ids = {word: ix for word, ix in patterns.items()
                   if word.bit_count() % 2 == forbidden}
            if len(ids) == 1 << (len(scope) - 1):
                blocks.append(dict(scope=scope, mask=mask, rhs=forbidden ^ 1, ids=ids))
    return blocks, len(groups)


def _inconsistent_indices(blocks):
    """Finder arithmetic is a separate dense-bitset implementation."""
    basis = {}
    xors = 0
    for ix, block in enumerate(blocks):
        row = (block['mask'] << 1) | block['rhs']
        why = 1 << ix
        while row > 1:
            pivot = row.bit_length() - 1
            if pivot not in basis:
                basis[pivot] = row, why
                break
            other, trace = basis[pivot]
            row ^= other
            why ^= trace
            xors += 1
        if row == 1:
            return [i for i in range(len(blocks)) if why >> i & 1], xors
    return None, xors


def _tree_from_blocks(selected, variables):
    nodes = []

    def reserve():
        ix = len(nodes)
        nodes.append(None)
        return ix

    def identify(block, fixed=0, depth=0):
        # The incoming path forces parity opposite to this block's RHS.
        ix = reserve()
        scope = block['scope']
        if depth == len(scope) - 1:
            last = (block['rhs'] ^ 1) ^ (fixed.bit_count() % 2)
            word = fixed | (last << depth)
            nodes[ix] = dict(clause=block['ids'][word])
        else:
            zero = identify(block, fixed, depth + 1)
            one = identify(block, fixed | (1 << depth), depth + 1)
            nodes[ix] = dict(query=[scope[depth]], zero=zero, one=one)
        return ix

    def locate(rows):
        if len(rows) == 1:
            return identify(rows[0])
        left, right = rows[:len(rows)//2], rows[len(rows)//2:]
        mask = rhs = 0
        for block in left:
            mask ^= block['mask']
            rhs ^= block['rhs']
        if not mask:
            return locate(left if rhs else right)
        ix = reserve()
        # The left discrepancy is value(query) XOR rhs.  A zero discrepancy
        # sends us right because the entire current discrepancy is one.
        zero_rows, one_rows = (right, left) if rhs == 0 else (left, right)
        zero = locate(zero_rows)
        one = locate(one_rows)
        nodes[ix] = dict(query=[v for j, v in enumerate(variables) if mask >> j & 1],
                         zero=zero, one=one)
        return ix

    root = locate(selected)
    return dict(kind=KIND, root=root, nodes=nodes)


def parity_query_refute(n, clauses):
    """Find a complete parity-block contradiction, otherwise return UNKNOWN.

    All arbitrary extra CNF clauses are allowed.  The final certificate uses
    only original clause IDs and original-variable parity queries.  The
    generated tree has at most as many leaves as there are raw input clauses.
    """
    raw = _input(n, clauses)
    variables = sorted({abs(lit) for clause in raw for lit in clause})
    positions = {v: i for i, v in enumerate(variables)}
    stats = dict(used_variables=len(variables), raw_clauses=len(raw),
                 support_groups=0, parity_blocks=0, selected_blocks=0,
                 selected_pattern_count=0, max_block_width=0, basis_xors=0)
    for ix, clause in enumerate(raw):
        if not clause:
            certificate = dict(kind=KIND, root=0, nodes=[dict(clause=ix)])
            stats.update(parity_query_stats(certificate))
            return dict(status='UNSAT', certificate=certificate, stats=stats)
    blocks, stats['support_groups'] = _blocks(raw, positions)
    stats['parity_blocks'] = len(blocks)
    indices, stats['basis_xors'] = _inconsistent_indices(blocks)
    if indices is None:
        return dict(status='UNKNOWN', certificate=None, stats=stats)
    selected = [blocks[i] for i in indices]
    stats['selected_blocks'] = len(selected)
    stats['selected_pattern_count'] = sum(len(block['ids']) for block in selected)
    stats['max_block_width'] = max(len(block['scope']) for block in selected)
    certificate = _tree_from_blocks(selected, variables)
    if not check_parity_query(n, raw, certificate):
        raise AssertionError('parity query tree failed independent raw-CNF checking')
    stats.update(parity_query_stats(certificate))
    if stats['leaves'] > len(raw) or stats['nodes'] != 2*stats['leaves'] - 1:
        raise AssertionError('incorrect output-size bound')
    return dict(status='UNSAT', certificate=certificate, stats=stats)
