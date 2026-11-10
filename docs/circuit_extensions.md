# Phase 26: keep nonlinear gates and test the missing simulation

## Decision relative to the P versus NP goal

The goal remains a complete proof of P=NP or P≠NP. Neither has been obtained.
Starting checkout: `68646aaf6af142a354d04c33c412e012900b9ebd`.
The referenced discussion reviewed phase 24; this checkout also contains
phase 25's exact affine one-cover number `2^m-1`.

Do not continue improving this cover number as the main route to that goal.
It measures a representation that can already be exponentially larger than a
linear-time computation. Completing the separate expander/PC formalization
would establish a restricted result, not remove this gap. Preserve those
results, but require a simulation handling nonlinear intermediate gates and
auxiliary variables before transferring their bounds.

We execute the next bounded test proposed at the end of phase 25: construct
the extended circuit encoding, check its projection, and construct actual
short refutations. This is an elementary obstruction test using standard
Tseitin encodings and resolution, with no novelty claim. It is not a new
general SAT algorithm or a complete P versus NP approach.

## 1. Exact encoding, not an affine replacement

For a topologically ordered Boolean circuit, introduce one fresh variable
per gate. The clauses for `z = a AND b` are

```
(-z OR a), (-z OR b), (z OR -a OR -b).
```

For `z = a XOR b` they are

```
(a OR b OR -z), (-a OR -b OR -z),
(a OR -b OR z), (-a OR b OR z).
```

For `z = NOT a` use `(a OR z), (-a OR -z)`. Add the required output unit.
Each gate's clauses force precisely its truth table. Induction over gates
therefore proves that every original input has exactly one extension
satisfying the gate clauses, and that the output unit accepts exactly the
inputs accepted by the circuit. This is a full all-circuit mathematical
argument; the Python tests check small truth tables independently.

For `Q_m(x,y) = XOR_i (x_i AND y_i)`, use `m` AND gates and `m-1` XOR gates.
For every `m >= 1`, the positive encoding has:

* `2m` original variables and `2m-1` gate variables: `4m-1` total;
* `3m + 4(m-1) + 1 = 7m-3` clauses of width at most three;
* exactly `(2^m-1)2^(m-1)` satisfying assignments, in bijection with `Q_m=1`.

The basis here is AND/XOR, not the AND/OR/NOT basis used for the earlier
`5m-4` gate comparison. Both give linear-size circuits. Dense wire numbers
use `O(log(m+1))` bits, so the explicit CNF uses `O(m log(m+1))` bits.
Construction and evaluation can be implemented in polynomial bit time;
the construction enumerates gates, not satisfying assignments.

**Linear auxiliaries alone do not remove the old obstruction.** Projection
of an affine flat is an affine flat. Consequently, if an extended relation
is covered by `s` affine flats and its projection is exactly `Q_m=1`, their
projected flats form an affine one-cover of `Q_m=1`; hence `s >= 2^m-1`.
The small CNF above is not a small union of affine flats. Its nonlinear AND
constraints and shared wires are exactly the representation change.

## 2. An explicit family with linear-size resolution refutations

Let `D_m` contain two copies of that circuit's gate clauses, with the same
original inputs and disjoint gate variables, together with output units
`o` and `-o'`. This is UNSAT because both circuits compute the same function.
It has `6m-2` variables and `14m-6` clauses.

**Theorem.** `D_m` has an ordinary resolution refutation of width at most
three with `32m-18` lines, counting all original clauses as input lines.
The construction is uniform, with `O(m log(m+1))` bits of certificate.

**Proof.** First consider a pair of AND gates `z=a AND b`, `w=a AND b`.
Resolve `(-z,a)` with `(w,-a,-b)` on `a`, then with `(-z,b)` on `b`.
This gives `(-z,w)` in two steps. Exchanging copies gives `(z,-w)` in
two more steps. Thus the `m` product pairs require `4m` resolution steps.

For an XOR pair with input equalities, write `z=a XOR b`, `w=c XOR d`.
The premises include `(-a,c), (a,-c), (-b,d), (b,-d)` and both sets of
four XOR clauses. The following fourteen resolvents prove output equality.
Each row specifies its parents or their literal content; earlier rows are
numbered `r1,...,r14`. The pivot is the complementary literal removed.

| Row | Parents | Pivot | Resolvent |
|---|---|---|---|
| r1 | `(-a,c)`, `(-c,-d,-w)` | c | `(-a,-d,-w)` |
| r2 | `(-a,c)`, `(-c,d,w)` | c | `(-a,d,w)` |
| r3 | `(a,-c)`, `(c,d,-w)` | c | `(a,d,-w)` |
| r4 | `(a,-c)`, `(c,-d,w)` | c | `(a,-d,w)` |
| r5 | `(-b,d)`, `(a,b,-z)` | b | `(a,d,-z)` |
| r6 | `(-b,d)`, `(-a,b,z)` | b | `(-a,d,z)` |
| r7 | `(b,-d)`, `(-a,-b,-z)` | b | `(-a,-d,-z)` |
| r8 | `(b,-d)`, `(a,-b,z)` | b | `(a,-d,z)` |
| r9 | r5, r4 | d | `(a,-z,w)` |
| r10 | r6, r3 | a | `(d,z,-w)` |
| r11 | r7, r2 | d | `(-a,-z,w)` |
| r12 | r8, r1 | a | `(-d,z,-w)` |
| r13 | r11, r9 | a | `(-z,w)` |
| r14 | r12, r10 | d | `(z,-w)` |

Induct along the `m-1` parity gates, reusing the earlier product/parity
equalities as input clauses for this template. Finally resolve `(o)` with
`(-o,o')`, then with `(-o')`. Including the original `14m-6` clauses gives

`(14m-6) + 4m + 14(m-1) + 2 = 32m-18` lines.

No resolvent exceeds width three. The argument also covers `m=1`, where
there is no XOR gate. This proves the theorem for every `m`, independently
of the finite experiments. It is a paper proof, not a new Lean theorem.

The implementation discovers gate-local templates using resolution on at
most six variables, then reuses them under renaming. There are at most
`3^6=729` nontautological clauses on such a scope, so even uncached local
saturation is bounded by a constant per gate. Discovery is accounted for;
we do not merely assume that someone provides a short certificate. For
degenerate gates the finder may derive a subclause of an equality clause.
Its final certificate still consists only of input and resolution nodes.
The existing separate checker reconstructs every clause from the original
CNF and rejects altered inputs, invalid pivots, and forward references.

The generated source CNF, correspondence, and circuit are explicit inputs
to this family construction. No algorithm for recognizing hidden circuits
inside arbitrary CNFs or deciding equivalence of arbitrary circuits is
claimed. In particular, two identical copies are an easy family; a general
circuit-equivalence test has not been obtained.

## 3. Why this does not refute the earlier proof-system lower bound

`D_m` is a new explicit contradiction family, not a recoding of the earlier
hard expander CNFs with a proved simulation in both directions. Short proofs
for `D_m` do not invalidate that earlier theorem. They rule out using the
inner-product positive affine-cover number as a lower bound for the
refutations constructed here. A large satisfying-set cover number and a
large UNSAT-proof size are different claims about different objects.

Nor is the linear-size positive encoding itself a solution method. Every
general circuit has a linear-size Tseitin encoding. SAT must still find a
compatible assignment to the shared nonlinear constraints.

## 4. A goal-level gate for the new direction

A tempting proposal is to keep arbitrary circuits compact and compile away
existentially hidden wires. State the proposed primitive precisely:

> A uniform deterministic algorithm takes any explicitly encoded Boolean
> circuit `C(x,y)` and produces, in polynomial time in its encoded size, an
> ordinary circuit `E(x)` with `E(x)=1 iff exists y: C(x,y)=1`.

Count all input wires in the encoding; permit `x` to be empty. The mathematical
circuit model in this proposition permits constant 0 and 1 gates, including
zero-input output circuits. Include every construction step and the output
circuit's size in the time bound.

**Proposition. This primitive exists if and only if P=NP.**

*Forward:* take an arbitrary 3CNF, regard it as a polynomial-size circuit
`C(y)`, and eliminate all its variables. Evaluate the resulting zero-input
circuit. This is a uniform polynomial-time SAT decision algorithm.

*Reverse:* if P=NP, the language of triples `(C,x,interface)` for which some
`y` makes `C(x,y)=1` has a polynomial-time decider. Use the standard uniform
polynomial-size circuit simulation of a polynomial-time Turing machine,
hardwire the description and interface of `C`, and leave `x` as input wires.
The running-time bound and construction are polynomial in the size of `C`,
including its input interface. The result is the required `E`.

Thus "efficiently project a general circuit" cannot be used as an
unproved simplifying lemma: under these quantifiers it is the original
P=NP goal. Small circuits for separate input lengths without a uniform
construction would not establish the same statement.

**Stop/continue decision:** stop the affine-cover sharpening branch as the
primary route, and retain this implementation as an extension-aware negative
control. Do not claim that adding gate variables supplies a polynomial SAT
algorithm. Continue a positive algorithmic proposal only with a specified
global procedure and an all-input polynomial bound; continue a negative
proposal only with a bound for a model that simulates the intended general
computations, or another argument covering all polynomial-time deciders.
No proposal meeting either condition was proved in this cycle. Repeating
larger duplicate-circuit tests cannot close that gap.

## 5. Executed checks and reproduction

```
PYTHONPATH=src python3 -m unittest discover -s tests -p test_circuit_extensions.py -v
python3 experiments/circuit_extensions.py --out-dir reproduced
python3 scripts/reproduce.py --out-dir reproduced --check
```

The new report is included in the standard reproduction driver. Seven new
tests cover independent gate truth tables, all auxiliary assignments for
`m=1,2,3`, duplicate-circuit UNSAT and same-output SAT controls, repeated
inputs and fanout, invalid graphs, tampered proofs, and certificate replay.
The report checks refutations for `m=1,2,3,8,64,1024`. At `m=1024`, this is
6,142 variables, 14,330 original clauses and 32,750 width-three proof lines.
Finite runs are evidence about the implementation; the all-size claims
come from the proofs above. No new Lean files or axioms are introduced.

Standard background: G. S. Tseitin, *On the complexity of derivation in
propositional calculus* (1968); S. A. Cook, *The complexity of theorem-proving
procedures* (1971), [doi:10.1145/800157.805047](https://doi.org/10.1145/800157.805047).
The constructions and scope distinctions needed here are given explicitly;
no new literature-priority claim is made.
