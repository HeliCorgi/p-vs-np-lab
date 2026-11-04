"""Optional, checked interface to the CMR 1.4.0 ``cmr-graphic`` CLI.

Use a trusted local executable; this module neither installs packages nor
uses the network. Our CI builds discopt/cmr at CMR_COMMIT (version text alone
cannot identify a commit). Interface/format docs at that revision:
``doc/graphic.md``, ``doc/file-formats.md``, ``src/main/graphic_main.c``.
Only a validated positive graph reaches the Python decision procedure.
"""
from __future__ import annotations

from math import isfinite
import re
import subprocess

from .graphic_support import (_columns, _linear, _setup, decide_graphic_supports,
                              verify_graphic_certificate)

CMR_COMMIT = '0c42a44deb8262a1f2a400add5d6be80e90eda3c'
CMR_VERSION = '1.4.0'


def _matrix_text(rank, codes):
    # A basis becomes the labelled forest. Each column is the edge-path
    # mask of one other element. For each basis direction retain a parallel
    # chord as well: a unit column, realizable along the same single edge.
    # Thus every nonzero-rank matrix has at least one nonzero in every row.
    lines = [f'{rank} {len(codes)} {sum(c.bit_count() for c in codes)}']
    for j, c in enumerate(codes,1):
        while c:
            bit = c & -c
            lines.append(f'{bit.bit_length()} {j} 1')  # CMR uses 1-based indices.
            c ^= bit
    return '\n'.join(lines) + '\n'


def _forest_certificate(graph_output, basis, codes):
    rank = len(basis)
    tagged = {}
    for line in graph_output.splitlines():
        if not line.strip():
            continue
        fields = line.split()
        if len(fields) != 3:
            raise ValueError('expected exactly two endpoints and an edge label')
        u, v, label = fields
        if (u == v or not re.fullmatch(r'[rc][1-9][0-9]*',label) or label in tagged):
            raise ValueError('unexpected loop or invalid/duplicate edge label')
        tagged[label] = (u,v)
    rows = [f'r{i+1}' for i in range(rank)]
    chords = [f'c{j+1}' for j in range(len(codes))]
    if set(tagged) != set(rows+chords):
        raise ValueError('graph edge labels do not match this matrix')
    parent = {v:v for label in rows for v in tagged[label]}

    def find(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v

    for label in rows:
        a,b = (find(v) for v in tagged[label])
        if a == b:
            raise ValueError('row edges contain a cycle')
        parent[a] = b
    # Never glue a chord between separate forest components: such a chord
    # would invalidate the purported spanning forest, even if gluing would
    # accidentally make the reported chord fit.
    for label in chords:
        a,b = tagged[label]
        if a not in parent or b not in parent or find(a) != find(b):
            raise ValueError('column not spanned by reported forest')
    roots = {find(v) for v in parent}
    numbered = {v:i for i,v in enumerate(sorted(set(parent)-roots),1)}
    def endpoints(label):
        return [numbered.get(v,0) for v in tagged[label]]
    edges = [endpoints(label) for label in rows]
    columns = _columns(edges)
    for label, code in zip(chords,codes):
        u,v = endpoints(label)
        if _linear(code,columns) != ((1 << u) ^ (1 << v)):
            raise ValueError('reported column endpoints disagree with its binary path')
    return {'basis_vectors':list(basis),'basis_edges':edges}, len(roots)


def decide_with_cmr(supports, rhs, *, executable='cmr-graphic', timeout=30.0):
    """Use optional CMR graph realization to decide an XOR-support instance.

    UNKNOWN covers absent/incompatible executables, timeout, negative graph
    recognition, malformed graph output or failure of independent certificate
    verification. The caller should fall back on UNKNOWN for total decision.
    In rank zero the trivial empty tree needs no external recognition, but
    even then an unavailable or incompatible executable is reported UNKNOWN.
    ``timeout`` applies separately to the version probe and the recognition
    process, not to total Python preprocessing, verification or matching.
    """
    if type(rhs) is not int or rhs < 0:
        raise ValueError('rhs must be a nonnegative integer')
    if type(timeout) not in (int,float) or not isfinite(timeout) or timeout <= 0:
        raise ValueError('timeout must be positive and finite')
    groups, co, mapping = _setup(supports)
    codes = list(mapping.values())[1:]  # _setup inserts 0 first, then sorted nonzero differences.
    rank = len(co.basis)
    meta = dict(expected_version=CMR_VERSION,version=None,recognition='not_run',
                matrix_rows=rank,matrix_columns=len(codes),
                matrix_nonzeros=sum(c.bit_count() for c in codes),forest_components=None)
    out = dict(status='UNKNOWN',reason=None,witness=None,certificate=None,matching=None,
               matching_calls=0,cmr=meta)
    def fail(reason):
        out['reason'] = reason
        return out
    try:
        ver = subprocess.run([executable,'--version'],capture_output=True,text=True,
                             encoding='utf8',timeout=timeout,check=False)
        match = re.fullmatch(r'CMR version ([0-9]+\.[0-9]+\.[0-9]+) \([^()\n]+ build\)\.',
                             (ver.stderr+ver.stdout).strip())
        if ver.returncode or not match or match[1] != CMR_VERSION:
            return fail('cmr_version_mismatch')
        meta['version'] = match[1]
        if rank:
            proc = subprocess.run([executable,'-','-i','sparse','-G','-'],
                                  input=_matrix_text(rank,codes),capture_output=True,text=True,
                                  encoding='utf8',timeout=timeout,check=False)
            if proc.returncode:
                return fail('cmr_process_failure')
            verdicts = [s for s in proc.stderr.splitlines()
                        if s in ('Matrix IS graphic.','Matrix is NOT graphic.')]
            if verdicts == ['Matrix is NOT graphic.'] and not proc.stdout.strip():
                meta['recognition'] = 'reported_not_graphic'
                return fail('cmr_reports_nongraphic')
            if verdicts != ['Matrix IS graphic.']:
                return fail('unrecognized_cmr_output')
            try:
                cert, components = _forest_certificate(proc.stdout,co.basis,codes)
                verify_graphic_certificate(groups,cert)
            except ValueError:
                return fail('invalid_cmr_graph_certificate')
            meta.update(recognition='verified_graphic',forest_components=components)
        else:
            cert = {'basis_vectors':[], 'basis_edges':[]}
            meta.update(recognition='trivial_rank_zero',forest_components=0)
    except FileNotFoundError:
        return fail('cmr_not_found')
    except subprocess.TimeoutExpired:
        return fail('cmr_timeout')
    except (UnicodeError,OSError):
        return fail('cmr_io_failure')
    decided = decide_graphic_supports(groups,rhs,basis_edges=cert['basis_edges'],max_tree_trials=0)
    decided.update(cmr=meta,certificate=cert)
    return decided
