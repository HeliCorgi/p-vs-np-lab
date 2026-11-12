# Phase 27: substitution with definitional extensions, and its sharp limit

The goal is a complete proof of P=NP or P≠NP. This phase does not obtain one.
It completes the extension-transfer investigation left unfinished after
[phase 26](circuit_extensions.md), including the full Lean package build and
transitive axiom audit. It does not continue sharpening affine-cover counts.

The result is a degree simulation for actual ordinary polynomial calculus
(PC). Its factor is unavoidable for direct substitution of proof lines.
Consequently, this simulation alone does not transfer the previous degree
lower bounds to unrestricted polynomial-size computations. This is a
standard substitution principle with an explicit formal implementation; no
novelty or priority claim is made.

## 1. The statement, with every premise

Let `x` be a finite set of original variables, work over `F_2`, and let `F`
be a set of ordinary polynomial equations containing all original Boolean
axioms `x_i^2-x_i`. Let `z` be additional variables, and choose ordinary
coordinate polynomials `q_j(x)` satisfying

\[
\deg q_j\le D,\qquad D\ge1.
\]

Let `E(x,z)` be the added equations. Require for each `e in E` that

\[
\forall a\in\mathbb F_2^n:\quad e(a,q(a))=0.
\tag{1}
\]

This is an identity on **all Boolean original assignments**, not merely on
models of `F`. The latter condition would be vacuous when `F` is UNSAT and
would allow an unjustified new axiom `1=0`. No SAT oracle or presumed short
derivation of the substituted equations is part of (1).

Let `F^E` consist of the original equations renamed into `(x,z)`, the Boolean
axioms for both sorts of variables, and `E`. Define substitution `sigma` by
`sigma(x_i)=x_i`, `sigma(z_j)=q_j(x)`. Then, for every natural `B`,

\[
\boxed{p\in C_B(F^E)\quad\Longrightarrow\quad
        \sigma(p)\in C_{DB}(F).}
\tag{2}
\]

Here `C_B` is the space of consequences derived using ordinary polynomials
with every proof line of total degree at most `B`. Repeated powers are not
reduced for free. In particular,

\[
1\in C_B(F^E)\Longrightarrow1\in C_{DB}(F).
\tag{3}
\]

If the minimum refutation degree of `F` is `r`, every degree-`B` refutation
of `F^E` must satisfy `DB >= r`, hence `B >= ceil(r/D)`. The formal theorem
uses the equivalent contrapositive: absence of a refutation through degree
`DB` implies absence through degree `B` in the extended system. It does not
postulate that absence; an application still needs its original lower bound.

The Lean endpoints are `extension_derives_transfer`,
`extension_refutation_transfer`, and `extension_lower_bound` in
[`ExtensionSubstitution.lean`](../formal_pc/ProofLab/ExtensionSubstitution.lean).
The more general substitution theorem is over any field; the Boolean
extension corollaries use `F_2` and finite original variables.

## 2. Proof and the cost of each rule

Ordinary substitution gives `deg sigma(p) <= D deg p`, by expanding a monomial
and adding the degrees of its substituted factors. Zero, addition and scalar
multiplication then preserve the `DB` ceiling.

For a primitive PC step `p -> v p`, if `p` is nonzero, the polynomial ring is
an integral domain and `deg(v p)=deg p+1`. Eligibility of that step implies
`deg p+1 <= B`. After the already completed derivation of `sigma(p)`, multiply
it by the polynomial `sigma(v)`. The existing ordinary-PC reuse theorem
expands this into variable multiplications and additions, with ceiling

\[
\max\{DB,\deg\sigma(v)+\deg\sigma(p)\}\le DB.
\]

The zero case is handled separately. Thus arbitrary polynomial multiplication
has not been added to the proof system as a primitive rule.

For an eligible input equation, its substituted degree is at most `DB`.
An original input maps to itself. An extension definition maps to a polynomial
vanishing on the entire Boolean cube by (1). An extension Boolean axiom maps
to `q_j^2-q_j`, which also vanishes there. The already proved Boolean-reduction
theorem derives any such vanishing polynomial from the original Boolean
axioms at its ordinary total degree. Its NS certificate is converted to PC
using the proved inclusion NS subset PC, not the false converse.

Induction on the ordinary-PC derivation proves (2); substitution preserves
the constant one, giving (3). The Lean proof carries out these steps and
audits their actual dependencies.

## 3. Concrete gates satisfy the premise

For an acyclic AND/XOR/NOT circuit, assign original variables their coordinate
polynomials. Traverse gates in topological order. Over `F_2`, choose

\[
q_z=\operatorname{sf}(q_aq_b)\quad\text{(AND)},\qquad
q_z=q_a+q_b\quad\text{(XOR)},\qquad
q_z=1-q_a\quad\text{(NOT)}.
\]

Here `sf` is squarefree reduction **for choosing a coordinate function**.
It is not a free proof rule. The added ordinary equations are respectively
`z-ab`, `z-(a+b)`, and `z-(1-a)`. The formal gate lemmas prove that their
substitutions satisfy (1). For example, `z=x AND x` has `q_z=x`, but the
substituted equation is `x-x^2`, an ordinary nonzero polynomial that requires
the Boolean axiom. The Python negative control checks this distinction.

The all-cube identities and the degree transfer are formalized. A general
formalized circuit datatype, a Lean recursion constructing every `q_j`, and
an end-to-end verified Python compiler are not claimed. The executable
coordinate constructor is checked independently against truth-table Möbius
inversion on small circuits. Expanding all the coordinates need not be fast.

## 4. The factor cannot be suppressed for general small circuits

Consider `AND_n(x)=x_1 ... x_n`, computed by `n-1` binary AND gates. A balanced
construction has multiplication depth `ceil(log_2 n)` for `n>=1`, with depth
zero when `n=1`.

**Formal theorem:** any ordinary polynomial `p` over `F_2` agreeing with
`AND_n` on every Boolean assignment has degree at least `n`.

To prove it, squarefree reduction preserves evaluations and cannot increase
total degree. A multilinear polynomial over `F_2` is determined by its values
on the Boolean cube. Therefore `sf(p)=x_1 ... x_n`. The latter monomial has
total degree `n`, so `deg p >= n`. This is the Lean endpoint
`and_representation_degree_lower_bound`. It covers every polynomial
representation of the coordinate, not just one particular expansion.

There is also a sharp example for replaying an individual proof line. For
`q=x_1 ... x_n`, `n>=1`, substituting the degree-two Boolean axiom `z^2-z`
gives `q^2-q`, whose ordinary degree is exactly `2n`. Its degree-`2n` and
degree-`n` monomials cannot cancel. Every PC derivation ending in that exact
polynomial has degree at least `2n` simply because its final line has that
degree. Both facts are formal endpoints, `and_boolean_axiom_exact_degree`
and `and_boolean_axiom_replay_cost`.

**Scope of sharpness:** this proves the `D` factor is necessary for a uniform
line-by-line substitution bound. It does **not** show every refutation must
use that Boolean axiom, nor that an arbitrary alternative simulation or
direct extended proof needs high degree. It is not a refutation lower bound
for the AND circuit itself.

For gates of multiplication depth at most `h`, degree induction gives
`D <= 2^h`: XOR/NOT do not increase the maximum degree, while a binary AND
at most doubles it. Thus constant multiplication depth permits a constant
loss, but logarithmic depth already permits `D=n`. This depth calculation
is a paper argument, tested by the balanced constructions, not an added
Lean circuit-complexity theorem.

## 5. Sparse expansion size is a separate obstruction

Even low gate count does not bound the size of an expanded coordinate
polynomial. On Boolean inputs over `F_2`,

\[
\operatorname{OR}_n(x)=1+\prod_{i=1}^n(1+x_i)
 =\sum_{\varnothing\ne S\subseteq[n]}\prod_{i\in S}x_i.
\]

Each subset gives a distinct monomial, so this multilinear polynomial has
exactly `2^n-1` terms, although the AND/NOT construction uses `4(n-1)` gates.
Multilinear uniqueness shows this is not fixed by selecting a different
multilinear representative. An arithmetic circuit can retain the factored
form compactly; no lower bound against such circuits follows.

The finite report expands AND/OR/XOR at `n=1,2,4,8,12`. At `n=12`, the OR
control has 44 gates and 4,095 output monomials. Full truth-table checking is
performed only through `n=8`; the report records zero tested assignments for
`n=12`. Ordinary squares of dense OR polynomials are not computed and are
recorded as null. XOR has degree one, and the earlier 32-pair inner-product
circuit has maximum coordinate degree two. Thus nonlinearity alone does
not imply the worst case; the actual coordinates matter.

The work counters measure term operations, not total bit complexity. The
constructor has explicit term/work limits and raises `ExpansionLimit` when
they are exceeded. Exhaustion never means SAT, UNSAT, or a completed expansion.

## 6. Decision relative to the complete-proof objective

This produces a usable theorem for extensions with bounded coordinate degree.
If an original family requires degree `Omega(n)` and `D` is constant, a
linear degree lower bound survives. If `D=n`, the same inequality supplies
only a constant lower bound. It does not prove that constant-degree
refutations exist; it says that this transfer no longer excludes them.

There is no polynomial-size proof simulation in (2), and degree lower bounds
alone do not quantify every deterministic polynomial-time decider. Even a
proof-size lower bound for one fixed proof system needs a justified bridge
before it can imply P!=NP. No such general bridge is obtained here.

Stop attempts to remove the `D` factor from direct substitution or to infer
bounded `D` merely from polynomial gate count. Both proposed shortcuts have
explicit obstructions above. Preserve the formal theorem for the classes to
which it applies. A next lower-bound proposal must account for auxiliary
definitions and shared circuit/proof size without expanding all coordinates;
a positive algorithmic proposal must give an all-input polynomial decision
procedure. Neither condition has been proved in this phase, and no complete
P-versus-NP proof candidate is being announced.

## 7. Verification and provenance

The existing pinned foundation files, both Lean versions, Mathlib revision,
and proof rules are unchanged. The new module uses the MIT-licensed Boolean
reduction and PC-reuse theorems attributed in [the package README](../formal_pc/README.md).
The audit adds all 16 new named theorems to the existing 126 endpoints.
The successful package build and **142 transitive axiom audits** are recorded
in [the local formal audit](../results/extension_substitution_formal_audit.json),
with source hashes and actual axiom sets. This is a local working-tree run,
not a GitHub CI or publication claim.

Five new test methods include 32 fixed-seed eight-gate circuits with fanout
and repeated inputs, independent truth-table Möbius inversion for every wire,
ordinary-versus-squarefree negative controls, balanced/chain comparisons,
and explicit budget failures. The new [deterministic report](../results/extension_degree.json)
is included in the standard reproduction driver. Run from the checkout root:

```sh
PYTHONPATH=src python3 -m unittest discover -s tests -p test_extension_degree.py -v
python3 scripts/reproduce.py --out-dir reproduced --check
cd formal_pc
lake build ProofLab
python3 audit.py
```

The standalone file compiled before an environment disconnection; package
integration and the full audit were completed after reconnecting. No failed
or unrun check is counted as a successful one.
