# Phase 26: affine one-covers under Tseitin extensions

## Preselected falsifiable question, budget and stopping rule

Starting point: the phase-25 exact original-input cover number for the positive
level of binary inner product is 2^m-1. Phase 25 explicitly left auxiliary gate
variables untested.

**H1 (projection gate):** If an extended witness relation S has exact projection
P_m = {(x,y): x dot y = 1 mod 2}, then an exact affine one-cover of S still needs
at least 2^m-1 affine flats, even when the extension is nonfunctional.

**H2 (tightness gate):** For the explicit AND/XOR Tseitin 3-CNF defined below,
the minimum is exactly 2^m-1 on *all* variables.

**H3 (negative control):** Not every positive affine flat on the original
variables lifts to an affine flat of the gate graph. A two-dimensional explicit
counterexample exists for m=3.

Falsifiers: an affine flat in S whose projection violates the phase-25
flat property; an incorrectly encoded gate truth table; an extended witness
with output fixed to one and wrong original inner product; a failure of a
fixed-x lifted chart; or an affine lift of the explicit nonaffine example.

**Stop:** prove the universal statements by elementary mathematics; inspect
every extended Boolean assignment only at m=1,2,3, and enumerate only
zero-, one- and two-dimensional affine flats there. Do not enumerate arbitrary
affine subspaces of the 4m-1 dimensional extended ambient space. Do not
increase the old phase-25 RREF limit. No additional Lean formalization is
claimed in this cycle.

## Definitions and lower bound for every existential extension

Write V = F_2^m, Q_m(x,y) = sum_i x_i y_i mod 2, and P_m = Q_m^{-1}(1).
For any finite auxiliary space W = F_2^r and **any** relation
S subseteq (V x V) x W with pi(S) = P_m, call a finite family of affine
flats lying inside S and covering S an *affine one-cover*. A cover can overlap
and repeat flats.

**Theorem A (arbitrary exact-extension monotonicity).**
The minimum affine one-cover size c(S) satisfies

    c(S) >= c(P_m) = 2^m - 1  (m >= 1).

**Proof.** Projection pi onto the first 2m coordinates is an affine/linear
map. Thus every affine flat A contained in S projects to an affine flat
pi(A) contained in P_m. Since pi(S) = P_m, the images of any cover of S
cover P_m. Consequently its size is at least the exact original-input cover
number from phase 25. No injectivity, unique gate extension, or special CNF
form was assumed. This does not rule out representations *other than*
affine-flat covers or establish any computational time lower bound. QED.

## Concrete linear-size Tseitin 3-CNF

For each original pair x_i,y_i introduce p_i iff x_i AND y_i,
using the following three clauses (signs are conventional Boolean literals):

    (not p_i or x_i)
    (not p_i or y_i)
    (p_i or not x_i or not y_i)

For i=1,...,m-1, define a prefix parity t_i iff t_{i-1} XOR p_i,
with t_0 = p_0. An XOR c iff a XOR b uses four clauses:

    (a or b or not c)
    (a or not b or c)
    (not a or b or c)
    (not a or not b or not c)

Add the output unit clause t_{m-1}; for m=1 this is simply p_0.
There are exactly 2m original variables, 2m-1 gate variables,
4m-1 variables total, and 3m + 4(m-1) + 1 = 7m-3 clauses,
all of width at most three. All quantities are linear in m.

The displayed clauses are verified directly by their 2^3 local truth
tables. Every original assignment has exactly one extension satisfying
the gate-definition clauses, with final output Q_m(x,y). Hence the full
CNF satisfying relation T_m is exactly the graph of a total function
g_m over P_m, not merely an equisatisfiable encoding. The circuit and
3-CNF are uniformly constructible in O(m) word operations; with the
standard integer-index encoding their total bit length is O(m log m).

**Theorem B (sharp all-variable cover).** For every m>=1,

    c(T_m) = 2^m - 1.

**Proof.** Theorem A gives the lower bound. For each nonzero x in V,
the affine (m-1)-flat

    A_x = {(x,y): x dot y = 1}

lies in P_m, and these 2^m-1 flats partition P_m. On A_x all x_i are
constant, so each product gate p_i=x_i*y_i is an affine function of y.
Every prefix parity gate t_i is an XOR of these affine outputs and is
also affine in y. Thus the map y -> (x,y,g_m(x,y)) is affine on the
affine hyperplane x dot y = 1. Its graph over A_x is an affine
(m-1)-flat of T_m. These graphs partition T_m and supply an upper
cover of exactly 2^m-1 flats. QED.

**Algorithmic distinction.** This family is trivially satisfiable:
choose x_0=y_0=1 and all other original variables zero, then compute
gate values in one linear pass. The exponential affine-cover size is
therefore not even evidence of hardness for these particular SAT
instances, let alone for arbitrary SAT.

## A counterexample to lifting *every* affine flat

Let m>=3 and take two free bits u,v. Fix
x_0=y_0=1; set x_1=x_2=u and y_1=y_2=v; set all other coordinates zero.
These four original points form an affine 2-flat. Their inner product is

    1 + u*v + u*v = 1  (over F_2).

Yet the two AND outputs p_1=p_2=u*v are not affine functions on
F_2^2: the XOR of their four values is one, not zero. Therefore their
graph in the Tseitin witness relation is not affine. In the fixed
m=3 audit, 315 positive original affine 2-flats exist, and only 135
lift as affine 2-flats. This negative control prevents silently assuming
that arbitrary original flats lift; Theorem B uses only the explicit
fixed-x flats.

## Independent finite controls and reproducibility

The standard-library-only implementation is
[experiments/tseitin_affine_lift.py](../experiments/tseitin_affine_lift.py).
The independent tests are
[tests/test_tseitin_affine_lift.py](../tests/test_tseitin_affine_lift.py).
The deterministic snapshot is
[results/tseitin_affine_lift.json](../results/tseitin_affine_lift.json).

From the repository root:

    python experiments/tseitin_affine_lift.py
    python -m unittest discover -s tests -p test_tseitin_affine_lift.py -v

For m=1,2,3 the number of satisfying assignments is 1,6,28;
the explicit partition uses 1,3,7 lifted charts. The full extended
Boolean spaces have respectively 2^3, 2^7 and 2^11 assignments.
The m=3 positive original 0-,1-,2-flats number 28,378,315;
after checking whether the unique Tseitin extensions are affine, they
number 28,378,135. Independent local gate truth tables, raw CNF
enumeration, parity oracle, and the nonaffine plane give adversarial
checks. All-m statements rely on the written proof, not finite data.

**Verification scopes:** Mathematical Theorems A and B are direct
self-contained arguments (not newly Lean-checked). Python verifies only
the fixed finite samples. Pre-existing Lean results from phase 24
and other formalizations are not a formalization of Theorem B.
No all-input SAT algorithm, lower bound on arbitrary SAT algorithms,
or P versus NP resolution is claimed.

## Primary source checks and next falsification

- G. S. Tseitin, *On the complexity of derivation in propositional
  calculus* (1968; English reprint in *Automation of Reasoning*,
  1983), DOI https://doi.org/10.1007/978-3-642-81955-1_28.
  Source for the historical proof-complexity context of gate extensions;
  the exact gate clauses and affine-cover proof here are derived and
  checked directly, not attributed as a theorem from that paper.
- Stephen Cook, *The P versus NP Problem*, Clay Mathematics Institute,
  https://www.claymath.org/wp-content/uploads/2022/06/pvsnp.pdf.
  Full SAT coverage and uniform worst-case polynomial time are needed
  for the P=NP route.

**Next adversarial gate:** Distinguish covering *all satisfying
assignments* by affine flats from efficiently deciding mere
nonemptiness. A polynomial-size description of an existential
3-CNF can coexist with a large affine cover. To argue for either
direction of P vs NP, specify the actual algorithm or proof system
with auxiliaries, prove a simulation/cost theorem, and test its
uniform all-input quantifier. Do not recast Theorem A as a generic
algorithmic lower bound.
