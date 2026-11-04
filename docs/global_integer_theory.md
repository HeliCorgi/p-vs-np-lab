# Global integer hulls: the exact relaxation and its stopping point

The [integer backend](integer_hull.md) combines local Boolean tables over the integers and discovers a contradictory modulus from the assembled equations. This removes a real restriction of the preceding field-specific implementations: an obstruction need not occur in any individual table, and its modulus can have a repeated prime factor. The procedure is an implementation of an established kind of affine integer relaxation. It does not introduce a new general polynomial-time SAT algorithm.

There are two separate conclusions. Global integer composition recovers information lost by testing the local tables for exceptional primes. Nevertheless, the [existing expansion examples](modular_barrier.md) have **full integer affine lattices** on every permitted raw fragment. They therefore defeat every modulus simultaneously, including the new backend and one-bit conditioning that continues to use only those raw fragments. Representation-changing preprocessing is outside this statement. Both conclusions have elementary proofs below.

## 1. What the integer relaxation actually asserts

For a selected set S of Boolean variables, let R_S be the satisfying words of the raw clauses wholly supported on S. Put one augmented row (w,1) into the integer matrix M_S for each w in R_S. Define

\[
  L_S=\operatorname{span}_{\mathbb Z}\{(w,1):w\in R_S\}.
\]

The global relaxation seeks **integer**, not necessarily Boolean, coordinates x_1,...,x_n such that

\[
  (x_S,1)\in L_S\qquad\text{for every selected }S.                 \tag{1}
\]

Equivalently, each scope has its own integer coefficients lambda_(S,w), possibly negative, satisfying

\[
 \sum_{w\in R_S}\lambda_{S,w}=1,\qquad
 x_i=\sum_{w\in R_S}\lambda_{S,w}w_i\quad(i\in S).               \tag{2}
\]

An actual model satisfies (2) by putting coefficient one on its local word and zero elsewhere. The converse fails in two distinct ways: a solution can have non-Boolean x_i, and a Boolean x_S in an integer affine hull need not belong to R_S. A feasible relaxation must therefore return `UNKNOWN` unless a separate original-clause check supplies a Boolean model.

The Boolean unary marginals of (2) are x_i for value one and 1-x_i for value zero. Thus (2) is precisely the ordinary affine integer programming, or AIP, relaxation of the CSP whose constraints are these selected local relations. It identifies **unary** marginals of overlapping scopes. It does not require agreement of their full distributions on a two-variable or larger intersection. In particular, scanning scopes of width k does not by itself implement the stronger width-k AIP hierarchy.

For an empty local relation, (2) contains 0=1. For a nonempty relation, the distinction between an integer affine hull and a rational affine hull is essential: clearing denominators of a rational basis can omit divisibility conditions.

### An exact list of local equalities and congruences

Let U M_S V=D be a Smith reduction, with U,V unimodular and nonzero diagonal entries d_1,...,d_r. Right multiplication by V maps the integer row lattice of M_S onto that of D. Hence (1) is equivalent to

\[
 \begin{aligned}
   d_j&\mid (x_S,1)V_j &&(j\le r),\\
   (x_S,1)V_j&=0       &&(j>r).
 \end{aligned}                                                     \tag{3}
\]

An entry d_j=1 gives no restriction. For d_j>1, (3) is a congruence; the remaining columns give exact integer equalities. After moving the last coordinate to the right, each nontrivial row has the form

\[
   a_t\cdot x\equiv b_t\pmod {d_t},
\]

where d_t=0 denotes the exact equation a_t dot x=b_t. Introduce one **private unrestricted integer** z_t for each nonzero d_t and write a_t dot x-d_t z_t=b_t. Combining these rows gives a single integer linear system A y=b. No choice of a prime, finite group, state labels, or satisfying assignment is needed to define that system.

## 2. Why a global contradictory modulus exists

For the mathematical argument, take a global Smith form U A V=D and write c=U b. Integer solvability is exactly the conjunction of d_i dividing c_i at every nonzero diagonal position and c_i=0 on zero rows. If the second condition fails, a row of U gives an exact linear combination 0=c_i with c_i nonzero.

If the first condition fails, put m=abs(d_i). The corresponding row u of U satisfies

\[
  uA=d_i e_i^{\mathsf T}V^{-1},\qquad ub=c_i.
\]

Every coefficient of uA is divisible by m, while c_i is not. This is the refutation 0=c_i modulo m. **Factoring m is unnecessary.** The statement includes a contradiction such as 0=2 modulo 4. There is no justification for replacing it by modulo 2, where it becomes 0=0.

The implementation uses unimodular integer diagonalization without enforcing a divisibility chain between the successive diagonal entries. That is sufficient for solvability and the same certificate argument: after isolating a pivot row, its coefficient gcd divides every coefficient before and after any unimodular column transformation. A row whose gcd fails to divide its right side supplies a contradictory modulus. An isolated solvable row can be removed because its transformed variable is unrestricted over Z.

### The final proof need not trust the elimination

A certificate supplies raw local laws (a_t,b_t,d_t), integer weights q_t, and the discovered m. A verifier checks the original Boolean tables and then checks

\[
 m\mid q_t d_t\quad\text{for each }t,\qquad
 \sum_t q_t a_t\equiv0\pmod m,\qquad
 \sum_t q_t b_t\not\equiv0\pmod m.                                \tag{4}
\]

The first condition is indispensable: a valid congruence modulo two cannot automatically be used modulo four. Multiplying its weight by two is allowed, because that product does annihilate its integer slack modulo four. Exact rows have d_t=0 and can be used in every modulus. For an exact final contradiction m=0, the corresponding conditions are q_t d_t=0, exact coefficient cancellation, and a nonzero right side.

Each original Boolean model would satisfy all the checked local laws and therefore their weighted sum, contradicting (4). The verifier needs neither the scope finder nor a Smith trace nor the global elimination algorithm. Those components discover a candidate proof; the original clauses and integer arithmetic determine whether it is valid.

### What is polynomial, and what is not claimed

For a fixed scope width, a polynomial number of scopes has polynomial total Boolean-table size. Its integer linear feasibility problem admits polynomial bit-complexity algorithms; this is classical normal-form work of [Kannan and Bachem (1979)](https://doi.org/10.1137/0208040). This observation concerns the relaxation, not equivalence with SAT.

The repository's simple Euclidean implementation is not a reimplementation or a complexity proof of that classical algorithm. It places explicit caps on local words, matrix dimensions, operations, and intermediate integer bit lengths. A cap gives `UNKNOWN`. If some scopes or laws were skipped, a reported feasible integer system refers to the **retained rows**, not the full intended collection. Enumerating all subsets of size k costs n raised to a k-dependent power; increasing k with n does not retain a fixed polynomial bound. Enumerating a local table costs up to 2^k even before integer elimination.

## 3. Locally torsion-free equations can create global prime powers

The carry-loop controls use Boolean triples satisfying

\[
 a_i+x_i-b_i=c_i,\qquad c_i\in\{0,1\}.
\]

Each local relation has three models. Its integer affine hull is exactly the displayed equality and has no finite torsion. Long private equality paths identify b_i with a_(i+1), cyclically, and identify the x_i values. Adding the gate equations then gives

\[
                  m x=q,\qquad q=\sum_i c_i.                     \tag{5}
\]

If a local scope cannot contain an entire private wire, it contains no connection between distinct gates. Partial gates have full affine lattices on their present coordinates; a complete gate contributes its one primitive equation. Dangling equality paths only duplicate a coordinate. Every such local profile is consequently torsion-free, despite the global obstruction (5).

Over Q, (5) always has the solution x=q/m. Over a field of characteristic p, it is consistent exactly when p does not divide m or p divides q. Therefore all prime-field systems are consistent precisely when rad(m) divides q, whereas the integer system is consistent only when m divides q. The choices (m,q)=(4,2), (9,3), and (49,7) separate these tests.

This is a separation from **separate field-linear feasibility**, not from all algorithms that use fields and Boolean reasoning. For example, 4x=2 becomes x=2 over F_3, whose single-coordinate Boolean relation is empty. A Boolean bridge can notice this. The experiments retain the preceding mixed-field backend as a baseline, and it already refutes the tested carry loops. The improvement here is uniform recovery of an integer obstruction without supplying its modulus, together with a compact arithmetic proof interface.

## 4. The stronger obstruction: full integer lattices

Suppose a nonempty Boolean relation R on d coordinates has, for every i, two words u_i,v_i in R that differ only in coordinate i. Orient the difference so that v_i-u_i=e_i. Its augmented lattice then contains

\[
    (e_i,0)=(v_i,1)-(u_i,1)\quad\text{for every }i.
\]

Take any w in R and subtract its coordinate units from (w,1). This yields (0,1). Thus

\[
          \operatorname{span}_{\mathbb Z}\{(w,1):w\in R\}
                 =\mathbb Z^{d+1}.                              \tag{6}
\]

Consequently R imposes no nontrivial affine equality or congruence in these Boolean coordinates, over **any** modulus. This is stronger than having full rational affine dimension or having no exceptional prime in a short list.

A single ordinary signed OR clause of width at least two already has property (6): for any bit to flip, set a different literal true. Hence basic per-clause AIP receives no information from proper 3-CNF clauses. Useful affine information must come from aggregating clauses, changing coordinates, or learning additional constraints.

### Applying the existing expansion proof

For a fragment J of proper signed ternary clauses, suppose every nonempty U contained in J has at least |U|+2 incident variables. The [Hall matching argument](modular_barrier.md) can satisfy every clause with a distinct variable while avoiding any specified pair of coordinates. In particular it provides the one-coordinate flip pairs required for (6), regardless of the signs.

The previous fixed-locality NP-complete high-girth class therefore has full integer affine lattices on every permitted raw fragment. The existential SAT/UNSAT signings with the same support and expansion through floor(n/1000) clauses or variables have this property on all those fragments as well. **Even an oracle supplying every local integer equality and every congruence for every modulus gives no nontrivial row on these instances.** Unlimited global combinations cannot recover a row that is absent at every leaf.

The quantifiers remain those of the earlier proof. Fixed-k high-girth SAT is NP-complete. The linear-locality SAT/UNSAT pair is an existence result; it is not a claimed reduction establishing NP-hardness at linear locality. These are barriers to this specified information interface, not lower bounds on every SAT algorithm. The raw signs and full local model sets still contain information that (6) discards.

### One-bit conditioning does not remove this barrier

Fix a bit s to b. To free any other bit i, use the same matching while avoiding both s and i. Set the unused s to b and flip i. The conditioned relation is nonempty and has integer affine hull exactly x_s=b, with every other coordinate unrestricted. On a scope not containing s it has full integer affine hull.

It follows that both branches of every singleton probe have consistent integer relaxations. No first forced literal can be learned, so an iteration that learns units only from such probes also immediately reaches a fixed point. Count the pinned bit in the original scope: a post-restriction scope of w variables can involve w+1 original variables. The barrier must hold at that total width. The same argument covers a raw clause-fragment bound without changing its clause count.

## 5. What prior research already settles

[Brakensiek, Guruswami, Wrochna and Živný (2020)](https://arxiv.org/abs/1907.04383) combine BLP and AIP: an LP removes local assignments forced to have zero weight, then an integer relaxation uses the remaining support. Their characterization uses block-symmetric polymorphisms and includes every tractable fixed Boolean CSP template. This is not a claim that arbitrary 3-SAT becomes tractable. The backend here implements the AIP component on selected Boolean relations; it should not be called BLP+AIP without the LP support step.

[Lichter and Pago, ICALP 2025, updated arXiv v3 in January 2026](https://arxiv.org/html/2407.09097v3), Theorems 1.1 and 1.3, exhibit a seven-element Maltsev template missed by Z-affine k-consistency, BLP+AIP, BA^k and CLAP, with sublinear-k lower bounds for the two parameterized methods. Cohomological conditioning solves that example but fails on an NP-complete template even at sublinear k. Their construction combines mod-two and mod-three Tseitin instances by a disjunction. These are established limitations of stronger algorithms, not just warnings inferred from our small examples.

An elementary mechanism behind such failures is worth making explicit. If A u=b and A v=b have integer-denominator solutions u=P/p and v=Q/q with coprime p,q, choose integers r,s with rp+sq=1. Then rP+sQ is an integer solution of A z=b. Negative coefficients allow this combination even when neither rational solution represents an actual model. This is the coprime-denominator fact used in that paper (Lemma 2.2, credited there to Berkholz and Grohe).

## 6. A useful conditioned control, with a limited conclusion

For disjoint-variable formulas F and G, a selector s forms a disjunction by requiring (s OR C) for every clause C of F and (NOT s OR D) for every clause D of G. The selector branches activate F and G respectively. To retain width three, replace a guarded three-literal clause t OR a OR b OR c by

\[
              (t\lor a\lor h)\ \land\ (\neg h\lor b\lor c),
\]

with a private helper h. Shorter clauses just acquire the guard. Eliminating h recovers the guarded clause, so the formula is satisfiable exactly when at least one arm is satisfiable.

Consider a raw fragment for which each arm, with its own disabling guard set false, is satisfiable. The fragment's relation has full integer affine hull. Indeed, disable an arm and set its helpers to zero: every original bit of that arm becomes free, while the other arm can use a model. To flip one helper, keep its arm disabled and satisfy b or c in its second clause; all other helpers remain zero. To flip s, choose satisfying words for both active arms; the same words satisfy their disabled versions too. These are one-coordinate flip pairs for every coordinate, proving (6). A scope omitting s contains only unguarded second clauses from split gadgets, where the same argument is even simpler.

Thus root integer reasoning can be silent while a selector case split finds two integer refutations. For split gadgets, private resolution or equivalent checked elimination may be needed after restriction to expose the original arm. A solver can find a candidate pivot from raw syntax and verify both restricted proofs without receiving the intended selector. This is established case analysis or failed-literal probing with a stronger arithmetic oracle; it is an incremental extension of [the earlier case/parity rule](case_parity.md), not a new reason to expect a universal bound.

## 7. Consequence for the next research decision

There is no remaining justification for a program of adding one modulus at a time. The integer presentation already subsumes all local affine congruences for the selected relations. The next step must identify information that this presentation discards and prove why retaining it helps on an explicitly stated family.

Three distinctions should remain visible in future experiments:

* Nonnegative local weights retain convex information; signed integer weights retain divisibility information. Replacing one by the other or running them independently does not retain both. Simply requiring nonnegative integer weights restores a general discrete feasibility problem.
* Conditioning can reveal structure hidden by a disjunction. A bounded amount of conditioning is still covered by strong negative examples, including the elementary singleton barrier above. An unrestricted branch tree needs its own total-size bound.
* Correlations on larger overlaps can strengthen unary-marginal AIP. A hierarchy level is a resource parameter, not an all-input polynomial bound. Known failures of stronger hierarchies must be addressed directly before claiming that larger local tables solve the original problem.

A plausible P=NP argument would still need a deterministic procedure deciding every input, a proof of its soundness and completeness, and a fixed polynomial bound in the original encoding length on discovery, arithmetic bit sizes, branching, and checking. A lower bound on this integer proof interface would still concern that interface. Neither success nor failure here supplies a lower bound for unrestricted algorithms.
