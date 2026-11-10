# Reconstructing one MCSP magnification proof and changing its witness selection

**Date:** 2026-11-11 JST. The user approved pausing direct attacks on the
general lower bound, studying an existing proof, and testing one change.
This note reconstructs the merging argument of McKay–Murray–Williams and
examines one replacement for its canonical witness selection. It uses
standard isolation and advice arguments; no novelty, new lower bound or
P-versus-NP resolution is claimed.

The change works with a tradeoff: two rounds of Sigma_2^P queries and
polynomial nonuniform hash advice suffice for bounded merging. This does
not preserve the original uniform construction or its sharp resource
bounds, and it does not remove the hard oracle computation.

## Source and scope of reconstruction

Dylan M. McKay, Cody D. Murray and R. Ryan Williams,
*Weak Lower Bounds on Resource-Bounded Compression Imply Strong Separations
of Complexity Classes*, STOC 2019,
[author-hosted PDF](https://people.csail.mit.edu/rrw/MCSP-MKTP-stoc19.pdf).
The copy examined has SHA-256
`bc6d4178bac7aa09d5f531a4eae820b4adf20afb2fd58ea93ca9b37038b27f03`.

We read Section 2.1, Lemma 3.1 and its proof, the conversion to Theorem 1.1,
and Theorem 1.4 with its Section 5 proof. We specialize the extra circuit
oracle A to a trivial predicate. Our reconstruction keeps the coarse
N·poly(n)-size, poly(n)-depth endpoint for s=n². The original paper obtains
sharper bounds using a larger branching factor and canonical parallel
output queries. We do not claim to reproduce those sharp bounds here.

## 1. What the original proof uses

Let T have N=2^n bits. A merge instance consists of circuits C_i and
disjoint integer intervals I_i within [0,N). It asks for a circuit D with
at most s gates agreeing with C_i on I_i. The paper chooses the
lexicographically first minimum-size feasible circuit; failure has a
separate status bit. All descriptions are padded to
L=O(s log(s+n)) bits.

| Step | Required fact | Where computational hardness remains |
|---|---|---|
| Encode each input bit | A constant circuit represents that bit on its singleton interval. | None. |
| Merge intervals | A size-s circuit must agree on the specified intervals only. | Finding a bounded feasible circuit. |
| Keep the invariant | The representative agrees with T throughout its assigned interval. | This is a correctness proof, not a merging algorithm. |
| Choose output bits in parallel | The canonical output bits are predicates in Sigma_3^P. | The short oracle queries. |
| Substitute ordinary gates | Under NP contained in P/poly, PH is contained in P/poly. | This is the explicit conditional assumption. |
| Count gates and depth | There are at most N-1 binary merges, with short inputs. | Polynomial cost per merge would give the desired upper bound. |

For completeness, the correctness induction does **not** need a minimum
or canonical representative. Any feasible circuit of size at most s works.
At a parent, all child circuits already agree with T on their intervals;
therefore the parent's feasible set is precisely the set of size-s circuits
agreeing with T on the union. Their behavior outside these intervals is
irrelevant. If T has a size-s circuit, that same circuit witnesses feasibility
at every node, whatever representatives the children selected.

Conversely, successful merges through the root give a size-s circuit for
all of T. If a merge fails, no size-s circuit agrees even on that interval,
so no such circuit can compute T. Propagate any failure explicitly; do not
interpret a failure string as an ordinary circuit at a later node.

For our coarse reconstruction use a binary tree of depth n. Each local
input has m=O(L+n)=poly(s) bits, including both descriptions and interval
endpoints. If every merge is replaced by a poly(s)-size, poly(s)-depth
ordinary circuit, total size is N·poly(s), and depth is n·poly(s)=poly(s)
for s>=n. At s=n² this is N·poly(n) size and poly(n) depth.

The paper supplies this replacement conditionally from NP contained in
P/poly, because the canonical bit queries are in PH. Taking the contrapositive
gives its circuit magnification consequence. No unconditional lower bound
is contained in this induction.

The closure step uses a fixed number of quantifier alternations. Under
NP contained in P/poly, Circuit-SAT has polynomial-size circuits, as do
complements of NP predicates. Given a polynomial-size circuit for an inner
predicate, existentially quantifying its witness inputs reduces to
Circuit-SAT with that circuit hardwired as advice; universal quantification
uses complementation. Induction handles each fixed PH level. The polynomial
exponent may depend on the level. No uniform algorithm or single exponent
for all levels is asserted.

## 2. The single alteration: choose a coherent bounded witness by isolation

Dropping optimality already permits adaptive Sigma_2^P prefix queries;
that standard self-reduction is recorded in
[the streaming note](mcsp_streaming_gate.md). Here we test **parallel
selection**, rather than relabeling that earlier observation as new work.

For a fixed local input y of padded length m, let

\[
 W_y=\{w\in\{0,1\}^L:\ \forall u\in\{0,1\}^{p(m)},\ V(y,w,u)\},
\]

where V is a fixed polynomial-time predicate. For circuit merging, w
encodes D, and u contains an n-bit assignment. V checks valid encoding,
the gate budget, and agreement on every specified interval covering that
assignment. Invalid inputs have an empty witness set. L is polynomial in m.

Merely asking, independently for each i, whether some w in W_y has w_i=1
can combine bits from different witnesses. For example, W={01,10} would
yield 11. A common witness must be selected before its bits are trusted.

### Isolation probability, including its constants

Choose q uniformly from 1,...,L+1, and choose an affine hash
h(w)=Aw+b into F_2^q with independent uniform matrix and offset bits.
For a fixed nonempty set W of size M, take
q_*=ceil(log2(2M)). Then 2M<=2^q_*<4M. Pairwise independence of the hash
values gives, for Z=|W intersect h^(-1)(0)|,

\[
 \Pr[Z=1]\ge \mathbb E Z-\mathbb E[Z(Z-1)]
 =\frac M{2^{q_*}}-\frac{M(M-1)}{2^{2q_*}}\ge\frac18.
\]

The first inequality holds pointwise: z-z(z-1) equals 1 for z=1, equals
0 for z=0 or 2, and is negative for z>=3. The selected q equals q_*
with probability 1/(L+1). A random hash trial therefore isolates W with
probability at least 1/[8(L+1)]. No distribution on the witnesses is assumed.

Choose K=16(L+1)(m+1) independent trials. For one nonempty W_y, the
probability that no trial isolates it is at most exp(-2(m+1)). There are
at most 2^m local inputs y. The union bound is

\[
 2^m\exp(-2(m+1))<1.
\]

Consequently there exists **one fixed family of K hashes**, chosen for
the parameters and input length, that isolates at least one witness for
every nonempty W_y. It does not depend on the actual merge input or the
actual truth table. Its description has O((m+1)(L+1)^3) bits.

This is nonuniform advice. The existence proof does not give a polynomial-time
algorithm for finding that family. Exhaustively searching for it would have
to be charged; it is not part of an efficient uniform SAT algorithm here.

### Two query rounds and verification

For every fixed hash h_j and bit i, make the following queries in parallel:

\[
 z_{j,i}=1\quad\Longleftrightarrow\quad
 \exists w\ \forall u:\ V(y,w,u)\land[h_j(w)=0]\land[w_i=1].
\]

These are Sigma_2^P predicates. When h_j isolates one witness, the resulting
L-bit string z_j is exactly that witness. For other hashes it may be an
incoherent mixture or the all-zero string.

In the **second** oracle round, verify each completed candidate:

\[
 v_j=1\quad\Longleftrightarrow\quad
 [h_j(z_j)=0]\land\forall u:\ V(y,z_j,u).
\]

These are coNP predicates, hence also usable as Sigma_2^P queries. Return
the first candidate with v_j=1, using a Boolean selection circuit; otherwise
return failure. A nonempty W_y has an isolating hash in the fixed family,
so at least one candidate passes. An empty W_y cannot pass verification.
Nonunique hashes that happen to produce valid witnesses are harmless.

There are KL first-round queries and K second-round queries. Each query
has length poly(m+L), including its matrix of at most (L+1)L bits. The
ordinary query-description wiring and candidate selection also have
polynomial size. Priority selection can be implemented with depth O(log K)
and polynomial size; the two oracle rounds must remain sequential.
The two fixed predicates can be combined into one tagged Sigma_2^P oracle
language. No low-depth completeness reduction to a particular quantified
formula syntax is being assumed.

This proves the controlled variant: bounded merging has nonuniform
polynomial-size circuits with two Sigma_2^P oracle rounds and logarithmic
Boolean selection depth. It is an application of standard isolation,
verification and advice fixing, not a newly claimed general complexity result.

## 3. What this changes, and what it leaves unresolved

| Resource or property | Original proof | Variant reconstructed here |
|---|---|---|
| Representative | Canonical minimum circuit | Any verified circuit within budget |
| Choice queries | Parallel Sigma_3^P bit predicates | Parallel Sigma_2^P bits, then coNP verification |
| Uniform construction | Supplied by the original paper | Efficient construction of the hash advice not supplied |
| Overhead | Theorem 1.1 has sharper explicit bounds | Only polynomial local overhead is retained |
| Coarse P/poly endpoint | Conditional N·poly(n)-size, poly(n)-depth upper bound | Same conditional endpoint |
| New ordinary-circuit lower bound | Not implied without its hypothesis | None |

For the last endpoint, NP contained in P/poly implies Sigma_2^P contained
in P/poly as well. Replacing our short oracle calls by those polynomial-size
circuits and hardwiring the polynomial-length advice gives polynomial cost
per merge. The binary tree from Section 1 therefore recovers the same coarse
conditional upper bound. Its contrapositive still needs the unproved
search-MCSP lower bound. Neither that assumption nor the hard local
computation has been eliminated.

Two costs must not be hidden: the hashes were fixed by an existence argument,
and the Sigma_2^P queries were not solved unconditionally. This variant does
not establish the original sharp uniform oracle theorem, a new shallow-circuit
frontier, or a polynomial-time SAT algorithm.

**Research decision.** Retain this as a completed study of one proof and one
controlled alteration. The correctness invariant, witness coherence, query
rounds and uniformity tradeoff are now explicit. This supplies no new main
route to P vs NP. Do not promote lowering the oracle alternation alone into
a claimed lower-bound breakthrough.

## 4. Finite audit

The script below checks exact isolation probabilities for every nonempty
witness set on 1, 2 and 3 bits: 273 sets in all. It counts every affine-hash
seed via a distribution of zero fibers, without a Monte Carlo estimate.

It separately enumerates actual two-input circuits with at most two AND/OR/NOT
gates. Their 14 truth functions exclude XOR and XNOR. One valid 21-bit circuit
description per function is retained; this finite witness set is deliberately
smaller than the set of all syntactic descriptions. Scalar decoding checks
each retained circuit independently.

For all 81 partial truth tables, a fixed-seed family of 3,168 hashes isolates
a representative whenever one exists. Parallel candidate-bit construction
followed by verification returns a correct circuit or reports infeasibility.
There are 5,308 candidates outside the selected hashed witness sets rejected
across these trials. Of these, 5,132 fail the circuit-encoding check and 42
encode circuits with wrong values on the partial table; the others fail
the chosen representative/hash restriction. Thus the verification stage
cannot simply be omitted in this test.
All 196 possible pairs of feasible child representatives across the 16 full
truth tables give exactly the correct parent feasible set.

The universal claims rest on the proofs above. These finite checks do not
implement a polynomial-time general merge oracle, establish efficient advice
generation, or certify a new lower bound. No Lean formalization is claimed.

```python
from collections import Counter
from fractions import Fraction
from itertools import combinations_with_replacement, product
from random import Random


def zero_fiber(bits, rows):
    return sum(all(((a & w).bit_count() & 1) == b for a, b in rows) << w
               for w in range(1 << bits))


abstract_cases = 0
for length in range(1, 4):
    domain = 1 << length
    row_masks = [zero_fiber(length, [(a, b)])
                 for a in range(domain) for b in (0, 1)]
    distributions = []
    counts = Counter({(1 << domain) - 1: 1})
    for q in range(1, length + 2):
        following = Counter()
        for mask, multiplicity in counts.items():
            for row in row_masks:
                following[mask & row] += multiplicity
        counts = following
        assert sum(counts.values()) == 1 << (q * (length + 1))
        distributions.append(counts)
    for witnesses in range(1, 1 << domain):
        probability = Fraction(0)
        for q, distribution in enumerate(distributions, 1):
            isolated = sum(count for fiber, count in distribution.items()
                           if (fiber & witnesses).bit_count() == 1)
            probability += Fraction(isolated, (length + 1) * (1 << (q * (length + 1))))
            for fiber in distribution:
                survivors = fiber & witnesses
                candidate = 0
                for w in range(domain):
                    if survivors >> w & 1:
                        candidate |= w
                valid = bool(survivors >> candidate & 1)
                if survivors.bit_count() == 1:
                    assert valid
                if valid:
                    assert witnesses >> candidate & 1
        assert probability >= Fraction(1, 8 * (length + 1))
        abstract_cases += 1


# Actual two-input circuits: constants/input wires free, at most two gates.
# Fixed 21-bit encoding: gate count (2), two slots (opcode 2 + args 3+3), output (3).
def encode(gates, output):
    value = len(gates)
    for j in range(2):
        op, a, b = gates[j] if j < len(gates) else (0, 0, 0)
        value = (value << 8) | (op << 6) | (a << 3) | b
    return (value << 3) | output


def decode(code):
    output = code & 7
    payload = code >> 3
    slots = [(payload >> 8) & 255, payload & 255]
    size = payload >> 16
    assert size <= 2
    gates = []
    for j, slot in enumerate(slots):
        op, a, b = slot >> 6, (slot >> 3) & 7, slot & 7
        if j < size:
            assert op <= 2 and a < 4 + j and b < 4 + j
            gates.append((op, a, b))
        else:
            assert slot == 0
    assert output < 4 + size
    table = 0
    for x in range(4):
        wires = [False, True, bool(x & 2), bool(x & 1)]
        for op, a, b in gates:
            wires.append(not wires[a] if op == 0 else
                         wires[a] and wires[b] if op == 1 else wires[a] or wires[b])
        table |= int(wires[output]) << x
    return table


catalog = {}
def enumerate_circuits(wires, gates):
    for out, table in enumerate(wires):
        code = encode(gates, out)
        catalog[table] = min(catalog.get(table, code), code)
    if len(gates) == 2:
        return
    choices = [(0, a, 0, 15 ^ wires[a]) for a in range(len(wires))]
    for a, b in combinations_with_replacement(range(len(wires)), 2):
        choices += [(1, a, b, wires[a] & wires[b]), (2, a, b, wires[a] | wires[b])]
    for op, a, b, value in choices:
        enumerate_circuits(wires + [value], gates + [(op, a, b)])


enumerate_circuits([0, 15, 12, 10], [])
assert set(catalog) == set(range(16)) - {6, 9}
for table, code in catalog.items():
    assert decode(code) == table

codes = sorted(catalog.values())
length, instance_bits = 21, 8
trials = 16 * (length + 1) * (instance_bits + 1)
rng = Random(20261111)
hashes = []
for _ in range(trials):
    q = rng.randrange(1, length + 2)
    rows = [(rng.getrandbits(length), rng.randrange(2)) for _ in range(q)]
    # Only evaluate the 14 representatives, not all 2^21 possible strings.
    fiber = sum(all(((a & code).bit_count() & 1) == b for a, b in rows) << i
                for i, code in enumerate(codes))
    hashes.append(fiber)

partial_cases = bad_candidates = bad_syntax = bad_semantics = 0
for partial in product((-1, 0, 1), repeat=4):
    witnesses = sum(all(bit < 0 or (decode(code) >> x & 1) == bit
                        for x, bit in enumerate(partial)) << i
                    for i, code in enumerate(codes))
    answer = None
    isolated = False
    for fiber in hashes:
        survivors = witnesses & fiber
        isolated |= survivors.bit_count() == 1
        # Parallel bit-existence answers, followed by membership verification.
        candidate = 0
        for i, code in enumerate(codes):
            if survivors >> i & 1:
                candidate |= code
        valid = any((survivors >> i & 1) and code == candidate
                    for i, code in enumerate(codes))
        bad_candidates += bool(survivors) and not valid
        if survivors and not valid:
            try:
                table = decode(candidate)
            except AssertionError:
                bad_syntax += 1
            else:
                bad_semantics += not all(bit < 0 or (table >> x & 1) == bit
                                         for x, bit in enumerate(partial))
        if valid and answer is None:
            answer = candidate
    assert isolated == bool(witnesses)
    assert (answer is not None) == bool(witnesses)
    if answer is not None:
        table = decode(answer)
        assert all(bit < 0 or (table >> x & 1) == bit for x, bit in enumerate(partial))
    partial_cases += 1

merge_pairs = 0
for table in range(16):
    left = [f for f in catalog if f & 3 == table & 3]
    right = [f for f in catalog if f & 12 == table & 12]
    for a, b in product(left, right):
        feasible = {f for f in catalog if f & 3 == a & 3 and f & 12 == b & 12}
        assert feasible == ({table} if table in catalog else set())
        merge_pairs += 1
assert bad_candidates > 0 and bad_syntax + bad_semantics > 0
print({'abstract_nonempty_witness_sets': abstract_cases,
       'circuit_functions': len(catalog), 'fixed_hashes': trials,
       'partial_table_instances': partial_cases, 'merge_representative_pairs': merge_pairs,
       'rejected_candidates': bad_candidates, 'invalid_circuit_encodings': bad_syntax,
       'wrong_partial_tables': bad_semantics, 'all_checks_passed': True})
```
