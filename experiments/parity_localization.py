"""Exact finite audit of the bounded-support parity closure strategy.

This audits a construction on satisfiable signed sunflowers. It is not an
experiment estimating an asymptotic UNSAT lower bound or an implementation of
an all-input SAT solver. All raw subsets are checked at every retained state.
"""
import argparse
from itertools import combinations
import json
from pathlib import Path


def normalize(literals):
    """XOR of signed Boolean literals: cancel repeated variables over F2."""
    support = set()
    constant = False
    for literal in literals:
        if type(literal) is not int or literal == 0:
            raise ValueError('parity literals must be nonzero integers')
        v = abs(literal)
        constant ^= literal < 0
        if v in support:
            support.remove(v)
        else:
            support.add(v)
    return frozenset(support), constant


def parity(query, values):
    support, constant = query
    return bool(constant ^ (sum(values[v] for v in support) % 2))


def sunflower(m):
    return [((1 if j % 2 else -1),
             (2 + 2*j) * (1 if j % 3 else -1),
             (3 + 2*j) * (1 if j % 2 else -1)) for j in range(m)]


class Audit:
    def __init__(self, m):
        self.raw = sunflower(m)
        self.variables = frozenset(abs(l) for c in self.raw for l in c)
        self.groups = tuple(frozenset(j for j in range(m) if mask >> j & 1)
                            for mask in range(1 << m))
        self.nbr = {g: frozenset(abs(l) for j in g for l in self.raw[j])
                    for g in self.groups}
        assert all(4*len(self.nbr[g]) > 7*len(g) for g in self.groups if g)
        self.stats = dict(states_checked=0, maximality_comparisons=0,
                          residual_neighborhood_checks=0,
                          residual_boundary_checks=0, hall_checks=0,
                          offered_queries=0, offered_edges=0, forced_queries=0,
                          previous_answers_checked=0, one_bit_pair_checks=0,
                          matching_repairs=0, nonempty_absorptions=0,
                          largest_closure=0, maximum_exposed=0,
                          maximum_offered_support=0,
                          maximum_fresh_support=0, first_supports=0,
                          histories_checked=0, repeated_cancelled_queries=0,
                          constant_queries=0, absorbed_coordinate_queries=0)

    def validate(self, state):
        A, C, values, history, exposed_cost = state
        X = A | self.nbr[C]
        assert set(values) == X
        assert len(A) == exposed_cost
        assert 8*len(self.nbr[C]-A) <= 13*len(C)
        assert not C or len(C) < 8*len(A)
        assert all(any(values[abs(l)] == (l > 0) for l in self.raw[j]) for j in C)
        for G in self.groups:
            if C < G:
                assert 8*len(self.nbr[G]-A) > 13*len(G)
                self.stats['maximality_comparisons'] += 1
            if G and not G & C:
                fresh = self.nbr[G]-X
                assert 8*len(fresh) > 13*len(G)
                self.stats['residual_neighborhood_checks'] += 1
                occurrences = {v: sum(v in {abs(l) for l in self.raw[j]} for j in G)
                               for v in fresh}
                boundary = sum(n == 1 for n in occurrences.values())
                assert 4*boundary > len(G)
                self.stats['residual_boundary_checks'] += 1
        for query, answer in history:
            assert query[0] <= X
            assert parity(query, values) == answer
            self.stats['previous_answers_checked'] += 1
        self.stats['states_checked'] += 1
        self.stats['largest_closure'] = max(self.stats['largest_closure'], len(C))
        self.stats['maximum_exposed'] = max(self.stats['maximum_exposed'], len(A))

    def initial(self):
        state = (frozenset(), frozenset(), {}, (), 0)
        self.validate(state)
        return state

    def ask(self, state, literals):
        A, C, values, history, cost = state
        query = normalize(literals)
        Y, _ = query
        assert Y <= self.variables
        X = frozenset(values)
        fresh = Y-X
        if not fresh:
            answer = parity(query, values)
            out = (A, C, dict(values), history+((query, answer),), cost)
            self.stats['forced_queries'] += 1
            self.validate(out)
            return [(answer, out)]

        pivot = min(fresh)
        A1 = A | fresh
        eligible = (G for G in self.groups if C <= G and
                    8*len(self.nbr[G]-A1) <= 13*len(G))
        # Maximum cardinality is a particular inclusion-maximal choice.
        C1 = max(eligible, key=lambda G: (len(G), tuple(sorted(G))))
        added = C1-C
        for U in self.groups:
            if U and U <= added:
                assert len(self.nbr[U] - X - {pivot}) >= len(U)
                self.stats['hall_checks'] += 1
        ordered = sorted(added)

        def matching(i, used, chosen):
            if i == len(ordered):
                return chosen
            for literal in self.raw[ordered[i]]:
                v = abs(literal)
                if v not in used:
                    answer = matching(i+1, used | {v}, chosen+[(v, literal > 0)])
                    if answer is not None:
                        return answer
            return None

        match = matching(0, X | {pivot}, [])
        assert match is not None
        assert len({v for v, _ in match}) == len(added)
        ext = dict.fromkeys(A1 | self.nbr[C1], False)
        ext.update(values)
        ext.update(match)
        assert pivot not in values and pivot not in dict(match)
        ext[pivot] = False
        base_answer = parity(query, ext)
        answers = []
        for answer in (False, True):
            one = dict(ext)
            one[pivot] = bool(answer ^ base_answer)
            assert parity(query, one) == answer
            assert all(one[v] == value for v, value in values.items())
            out = (A1, C1, one, history+((query, answer),), cost+len(fresh))
            self.validate(out)
            answers.append((answer, out))
        zero, one = answers[0][1][2], answers[1][1][2]
        assert {v for v in zero if zero[v] != one[v]} == {pivot}
        self.stats['one_bit_pair_checks'] += 1
        self.stats['offered_queries'] += 1
        self.stats['offered_edges'] += 2
        self.stats['matching_repairs'] += len(match)
        self.stats['nonempty_absorptions'] += bool(added)
        self.stats['maximum_offered_support'] = max(
            self.stats['maximum_offered_support'], len(Y))
        self.stats['maximum_fresh_support'] = max(
            self.stats['maximum_fresh_support'], len(fresh))
        return answers


def audit():
    assert normalize((1, 1)) == (frozenset(), False)
    assert normalize((1, -1)) == (frozenset(), True)
    assert normalize((-2, 3, 3)) == (frozenset({2}), True)
    lab = Audit(7)
    start = lab.initial()
    labels = sorted(lab.variables)
    for q in (1, 2, 3):
        for support in combinations(labels, q):
            lab.stats['first_supports'] += 1
            # Signed constants and supports both occur deterministically.
            query = tuple(-v if (i+v) % 3 == 0 else v for i, v in enumerate(support))
            for first_answer, state in lab.ask(start, query):
                fixed = sorted(state[2])
                fresh = sorted(lab.variables-set(state[2]))
                duplicate = fresh[0] if fresh else fixed[0]
                repeated = lab.ask(state, query+(duplicate, duplicate))
                assert len(repeated) == 1 and repeated[0][0] == first_answer
                lab.stats['repeated_cancelled_queries'] += 1
                const = lab.ask(state, (duplicate, -duplicate))
                assert len(const) == 1 and const[0][0]
                lab.stats['constant_queries'] += 1

                # A query may be forced by a value assigned during absorption,
                # even if that coordinate was absent from every earlier query.
                absorbed = sorted(set(state[2])-set(state[0]))
                if absorbed:
                    forced = lab.ask(state, (absorbed[0],))
                    assert len(forced) == 1
                    lab.stats['absorbed_coordinate_queries'] += 1
                if not fresh:
                    continue
                next_queries = {(fixed[-1], fresh[0])}
                next_queries.add(tuple(fresh[:min(3, len(fresh))]))
                for second in sorted(next_queries):
                    for second_answer, state2 in lab.ask(state, second):
                        # Query the XOR of two previous expressions. It is
                        # forced and its answer includes the signed constant.
                        combined = lab.ask(state2, query+second)
                        assert len(combined) == 1
                        assert combined[0][0] == (first_answer ^ second_answer)
                        remain = sorted(lab.variables-set(state2[2]))
                        if remain:
                            ordered = remain if first_answer == second_answer else list(reversed(remain))
                            third = tuple(ordered[:min(3, len(ordered))])
                            for _, final in lab.ask(state2, third):
                                assert len(final[3]) == 3
                                lab.stats['histories_checked'] += 1
    assert lab.stats['first_supports'] == 575
    assert lab.stats['maximum_offered_support'] == 3
    assert lab.stats['nonempty_absorptions'] and lab.stats['absorbed_coordinate_queries']
    assert lab.stats['one_bit_pair_checks'] == lab.stats['offered_queries']

    # A one-row parity matrix has rank one, yet a wide support can absorb
    # more than 8 clauses. This invalidates a rank-only version of THIS charge.
    wide = Audit(9)
    initial = wide.initial()
    query = tuple(sorted(wide.variables-{1}))
    answers = wide.ask(initial, query)
    assert len(answers) == 2
    assert all(len(state[1]) == 9 and len(state[0]) == 18 for _, state in answers)
    assert all(len(state[2]) == 19 for _, state in answers)
    # The two complete words satisfy the full signed sunflower independently
    # of the closure validator. The fixture is explicitly satisfiable.
    models = [sum(int(state[2][v]) << (v-1) for v in sorted(wide.variables))
              for _, state in answers]
    assert all(all(any(bool(word >> (abs(l)-1) & 1) == (l > 0) for l in c)
                   for c in wide.raw) for word in models)
    rank_control = dict(query_rank=1, normalized_support=18,
                        absorbed_clauses=9, invalid_rank_charge_bound=8,
                        invalid_rank_charge_refuted=True,
                        complete_satisfying_words=models,
                        both_answers_checked=True,
                        scope='Counterexample to replacing exposure cardinality by equation rank inside this closure argument; not an UNSAT hardness counterexample.')
    # General Boolean queries do not have parity's sensitivity in every
    # coordinate under every fixing of the other coordinates. The input
    # clause itself is a query with fresh support but only one viable answer.
    clause_models = [word for word in range(8) if any(word >> j & 1 for j in range(3))]
    or_answers = sorted({bool(any(word >> j & 1 for j in range(3))) for word in clause_models})
    assert len(clause_models) == 7 and or_answers == [True]
    boolean_control = dict(input_clauses=[[1, 2, 3]], fresh_query_support=[1, 2, 3],
                           query='x1 OR x2 OR x3', satisfying_words=clause_models,
                           extendible_answers=or_answers,
                           arbitrary_boolean_two_sided_extension_refuted=True)
    return dict(schema_version=1, all_checks_passed=True,
                summary=lab.stats, rank_charge_control=rank_control,
                arbitrary_boolean_query_control=boolean_control,
                rank_control_checks=wide.stats,
                coverage='Every first support of size 1, 2 or 3 on the signed seven-petal SAT control; both replies, repeated and cancelling expressions, overlap and fresh continuations, adaptive third questions, and all raw subsets at every checked state. Does not enumerate all query trees.',
                scope='Finite audit of the two-sided parity extension and exposure invariant. The expanding UNSAT family lower bound is proved separately; no asymptotic claim is inferred from these SAT controls.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--out-dir', type=Path, required=True)
    out = parser.parse_args().out_dir
    out.mkdir(parents=True, exist_ok=True)
    result = audit()
    (out/'parity_localization.json').write_text(json.dumps(result, sort_keys=True, indent=2)+'\n')
    print(result['summary'])
