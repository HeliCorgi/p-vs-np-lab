"""Exact ordinary-PC quotient spaces and separated-subspace failure controls."""
import argparse
from collections import Counter
from fractions import Fraction
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path

from pnp_lab.pc_subspace import (check_pc_subspace, check_static_moment,
                                 pc_subspace, replay_pc_subspace)


def _models(n, raw):
    return sum(all(any(bool(word >> (abs(lit)-1) & 1) == (lit > 0)
                       for lit in clause) for clause in raw) for word in range(1 << n))


def _audit(name, n, raw, bound, target):
    answer = pc_subspace(n, raw, bound=bound, target_degree=target)
    assert answer['status'] == 'COMPLETE'
    certificate = answer['certificate']
    replay = replay_pc_subspace(n, raw, certificate, bound=bound, target_degree=target)
    profile = answer['profile']
    for key in ('ambient_dimension', 'basis_rank', 'low_degree_dimension',
                'low_degree_consequence_rank', 'separated_dimension', 'refutes',
                'eligible_axioms'):
        assert replay[key] == profile[key]
    if answer['static_separator'] is not None:
        assert not profile['static_refutes']
        assert check_static_moment(n, raw, answer['static_separator'], bound=bound)
    else:
        assert profile['static_refutes']
    encoded = json.dumps(certificate, sort_keys=True, separators=(',', ':')).encode()
    return dict(name=name, variables=n, clauses=raw, profile=profile,
                models=_models(n, raw), independent_closure_check=True,
                certificate_sha256=sha256(encoded).hexdigest(),
                certificate_bytes=len(encoded)), answer


def _boundary(raw, selected):
    counts = Counter(abs(lit) for i in selected for lit in raw[i])
    return frozenset(v for v, count in counts.items() if count == 1)


def _small_support(raw, monomial, s):
    """The true union over *clause sets*, not just individual clauses."""
    selected = set()
    variables = set(monomial)
    for size in range(1, min(s, len(raw)) + 1):
        for indices in combinations(range(len(raw)), size):
            if _boundary(raw, indices) <= variables:
                selected.update(indices)
    return sorted(selected)


def _empty_support_control(name, raw):
    n, s, bound, k = 6, 12, 3, 3
    case, answer = _audit(name, n, raw, bound, k)
    checked_sets = 0
    ratios = []
    for size in range(1, len(raw) + 1):
        for indices in combinations(range(len(raw)), size):
            boundary = _boundary(raw, indices)
            assert 2*len(boundary) >= size
            neighborhood = {abs(lit) for i in indices for lit in raw[i]}
            assert 4*len(neighborhood) > 7*size
            ratios.append(Fraction(len(boundary), size))
            checked_sets += 1
    monomials = [tuple(m) for degree in range(k + 1)
                 for m in combinations(range(1, n + 1), degree)]
    empty = [m for m in monomials if not _small_support(raw, m, s)]
    replay = replay_pc_subspace(n, raw, answer['certificate'],
                                generators=[[list(m)] for m in empty])
    assert replay['candidate']['separated']
    assert bound <= s // 4
    minimum = min(ratios)
    case['empty_support'] = dict(
        support_range=s, clause_sets_checked=checked_sets,
        stated_boundary_expansion=[1, 2],
        actual_minimum_boundary_ratio=[minimum.numerator, minimum.denominator],
        neighborhood_seven_fourths_checked=True,
        all_squarefree_monomials_up_to_k=len(monomials),
        degree_k_empty_support_monomials=sum(len(m) == k for m in empty),
        empty_support_monomials=[list(m) for m in empty],
        span=replay['candidate'],
        convention='Union of all clause sets A with 1 <= |A| <= s and boundary(A) contained in the monomial variables.')
    return case, answer


def run():
    cases = []
    raw = [(-1, -2), (-1, 2)]
    gap, answer = _audit('degree_fall_makes_new_products', 3, raw, 2, 2)
    assert (gap['profile']['static_basis_rank'], gap['profile']['basis_rank']) == (5, 6)
    dynamic = replay_pc_subspace(3, raw, answer['certificate'], generators=[[[1, 3]]])
    assert dynamic['candidate']['intersection_dimension'] == 1
    gap['new_dynamic_monomial'] = [1, 3]
    cases.append(gap)

    php = [(1, 2), (3, 4), (5, 6)] + [
        (-2*i-a, -2*j-a) for a in (1, 2) for i, j in combinations(range(3), 2)]
    low, low_answer = _audit('php_3_2_degree_two', 6, php, 2, 2)
    high, high_answer = _audit('php_3_2_degree_three', 6, php, 3, 3)
    assert not low['profile']['refutes'] and high['profile']['refutes']
    assert low['profile']['separated_dimension'] == 13
    assert high['profile']['basis_rank'] == high['profile']['ambient_dimension'] == 84
    assert high['profile']['static_basis_rank'] == 82 and not high['profile']['static_refutes']
    assert low['models'] == high['models'] == 0
    high['exact_pc_refutation_degree'] = 3
    high['static_degree_three_nonrefutation_witness'] = high_answer['static_separator']
    cases.extend([low, high])

    padded = php + [(-7,), (-8,), (-9,)]
    pad_low, _ = _audit('forced_zero_padding_degree_two', 9, padded, 2, 2)
    pad_high, _ = _audit('forced_zero_padding_degree_three', 9, padded, 3, 2)
    assert pad_low['profile']['separated_dimension'] == low['profile']['separated_dimension']
    assert pad_low['profile']['low_degree_dimension'] == 55 > low['profile']['low_degree_dimension']
    assert not pad_low['profile']['refutes'] and pad_high['profile']['refutes']
    cases.extend([pad_low, pad_high])

    omitted, _ = _audit('wide_axiom_omission_warning', 3,
                         [(-1,), (-2,), (-3,), (1, 2, 3)], 2, 2)
    assert omitted['profile']['omitted_clause_axioms'] == 1
    assert omitted['profile']['separated_dimension'] == 1 and omitted['models'] == 0
    omitted['not_a_generic_criterion_instance'] = 'The input width is 3 but B=2; its contradictory wide axiom is ineligible. The generic criterion uses B >= w.'
    cases.append(omitted)

    one_clause = [(1, 2, 3)]
    joint, joint_answer = _audit('individual_nonmembership_does_not_separate_span',
                                 3, one_clause, 3, 3)
    squarefree = [list(m) for degree in range(4)
                  for m in combinations((1, 2, 3), degree)]
    for monomial in squarefree:
        replay = replay_pc_subspace(3, one_clause, joint_answer['certificate'],
                                    generators=[[monomial]])
        assert replay['candidate']['separated']
    replay = replay_pc_subspace(3, one_clause, joint_answer['certificate'],
                                generators=[[m] for m in squarefree])
    assert replay['candidate']['intersection_dimension'] == 1
    joint['individual_nonzero_classes'] = len(squarefree)
    joint['joint_space'] = replay['candidate']
    joint['nonzero_intersection_polynomial'] = squarefree
    cases.append(joint)

    disjoint, _ = _empty_support_control('disjoint_triples_empty_support_space',
                                         [(1, 2, 3), (4, 5, 6)])
    assert disjoint['empty_support']['degree_k_empty_support_monomials'] == 18
    assert disjoint['empty_support']['span']['dimension'] == 40
    cases.append(disjoint)
    cycle_raw = [(1, 2, 3), (3, 4, 5), (5, 6, 1)]
    cycle, _ = _empty_support_control('three_clause_cycle_empty_support_space', cycle_raw)
    assert cycle['empty_support']['degree_k_empty_support_monomials'] == 16
    assert cycle['empty_support']['span']['dimension'] == 38
    true_support = _small_support(cycle_raw, (2, 4, 6), 12)
    assert true_support == [0, 1, 2]
    assert not any(set(map(abs, clause)) <= {2, 4, 6} for clause in cycle_raw)
    cycle['whole_clause_set_matters'] = dict(monomial=[2, 4, 6],
                                            support_clause_ids=true_support,
                                            contains_an_individual_clause=False)
    cases.append(cycle)

    # A closed-space certificate is substantially stronger than replaying a
    # few found derivations; deliberately delete a basis row in every case.
    rejected = 0
    for cert, n, raw in ((answer['certificate'], 3, [(-1, -2), (-1, 2)]),
                          (low_answer['certificate'], 6, php),
                          (high_answer['certificate'], 6, php)):
        bad = dict(cert, basis=cert['basis'][1:])
        assert not check_pc_subspace(n, raw, bad)
        rejected += 1
    return dict(
        schema_version=1, all_checks_passed=True, cases=cases,
        sample_php_degree_three_complete_pc_certificate=high_answer['certificate'],
        summary=dict(complete_pc_spaces=len(cases), independent_closure_checks=len(cases),
                     maximal_ambient_dimension=max(c['profile']['ambient_dimension'] for c in cases),
                     static_dynamic_rank_gaps=sum(c['profile']['basis_rank'] >
                                                 c['profile']['static_basis_rank'] for c in cases),
                     exact_php_pc_degree=3, php_static_degree_three_rank=82,
                     php_dynamic_degree_three_rank=84,
                     padding_preserved_separated_dimension=13,
                     individually_nonzero_but_jointly_dependent=8,
                     empty_support_spans_checked=2,
                     empty_support_dimensions=[40, 38],
                     malformed_complete_spaces_rejected=rejected),
        scope='Finite exact ordinary F2 PC spaces. A complete subspace certificate replays derivations and verifies a closed-space upper inclusion. Static moment witnesses certify only the original-axiom-multiple span. Empty-support controls are satisfiable small formulas; they do not instantiate an asymptotic UNSAT lower bound or validate the external affine-DAG criterion.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--out-dir', type=Path, required=True)
    out = parser.parse_args().out_dir
    out.mkdir(parents=True, exist_ok=True)
    report = run()
    (out / 'pc_subspace.json').write_text(json.dumps(report, sort_keys=True, indent=2) + '\n')
    print(report['summary'])
