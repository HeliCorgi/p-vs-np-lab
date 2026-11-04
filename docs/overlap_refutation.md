# A degree-bounded algebraic certificate of affine coverage

A bad event is a conjunction of parity equations on parameter bits. Covering
the entire parameter space proves **UNSAT**: no parameter avoids all the
forbidden events. Individual event sizes need not determine coverage because
their overlaps matter. Here we certify coverage without enumerating all
assignments or explicitly computing the size of the union. We do not decide
SAT from a failed proof search.

## Indicator identity and checker

Work in the Boolean ring
`R = F_2[x_1,...,x_n] / (x_j^2-x_j : 1<=j<=n)`. Each Boolean function has
one multilinear polynomial representative. The indicator of the equation
`a·x=b` is `1+b+a·x`. For an event `E_i`, multiply these indicators to obtain
`g_i`. Thus `g_i` evaluates to one exactly on that original event, including
all its input equations. An inconsistent event has zero indicator; an empty
conjunction has constant-one indicator.

We seek an identity

\[
  1=\sum_{(i,T)\in C} x^Tg_i,\qquad x^T=\prod_{j\in T}x_j.
\]

At an avoiding point every summand would vanish, a contradiction. This
argument is valid even when events coincide or intersect. It does **not**
require that an assignment belong to an odd number of the original events:
which terms contribute at that assignment depends on the multipliers.

The [generator and verifier](../src/pnp_lab/overlap_refutation.py) agree on
squarefree monomial masks and original event indices. The generator removes
redundant equations by Gaussian elimination, skips inconsistent events,
expands indicators only for eligible events, and eliminates rows in the
monomial coefficient space with GF(2) provenance tags. Constant 1 in the
row span yields the original indexed multiples. The separate verifier
expands the *raw supplied equations*, recomputes each term's degree cost,
checks labels and degree, and compares the whole polynomial with constant 1;
it does not call the search or trust the generator's coefficient columns or
linear combinations. A certificate passing for one event arrangement is not
a certificate of unrelated source-CNF correctness: the caller must also
validate the source-to-event transformation. This is executable checking,
not a new end-to-end Lean verification.

## What a degree cutoff means

For a consistent event with coefficient rank `r`, the search includes
multipliers satisfying `|T|+r <= D`. This is a **static** row space, not full
dynamic polynomial calculus: no newly derived smaller equation is fed back
as a fresh axiom to multiply. The charged sum is an upper bound on degree
after multiplying/reducing; squarefree cancellations do not extend the
allowed multiplier budget. Within an event, replacing equations by an
independent system leaves its indicator unchanged, of degree at most `r`.
The certificate states the exact maximum charged degree of its terms;
`max_degree` in the checker optionally imposes a caller's limit.

Let `s` be the number of coordinate labels occurring in the eligible
equation bases. Inactive multiplier coordinates can be set to zero in a
putative identity; the indicators are independent of those coordinates.
Therefore enumerating only active coordinates loses no bounded-degree proof.
For fixed `D`, there are at most `M = sum_{j=0}^min(s,D) binom(s,j)`
monomial columns and at most `m M` candidate rows for `m` input events.
All Gaussian and polynomial operations, including the provenance and final
verification, cost polynomially many bit operations in the explicit input
length for fixed `D`. Live coefficient IDs do not index a table by the
numerical value of an arbitrary bit mask. `max_rows` limits row attempts,
not raw input reads, event rank tests, one-row expansion, or total memory.
The polynomial's exponent can grow with `D`; high-degree verification is
not asserted polynomial just in the number of listed certificate terms.

A row limit returns `UNKNOWN` when an untested row remains. Even after the
entire bounded span is exhausted, missing 1 means only that this particular
proof calculus has no refutation of that degree. The backend never returns
SAT. Conversely `D=n` suffices for completeness without a row budget:
assign each individual point of a covered cube to one event containing it.
An event of rank `r` has `n-r` nonpivot free coordinates. Its indicator times
the product fixing those `n-r` bits to the point is exactly that point's
indicator. Expand the fixing product into monomials, sum over the cube and
cancel duplicate terms. Each term has charged degree at most `n`. This
existence proof can be exponential and supplies no general polynomial bound.

## A lower bound *on the codimension-two selector encoding*

The fixed-degree restriction is not just a weakness on artificially high
codimension events that are omitted by construction. Even if every event
has codimension two, degree must be unbounded in this static system. Here
is the transfer giving a linear lower bound on a family with linear input
variable and clause counts (the dense bit encoding can be larger).

Take a 3-CNF with three distinct variables per clause. Write `t_i` for a
literal's truth bit and `f_i=1+t_i` for its false bit. In each clause use
two selector variables `u,v`; selection bits are `b=(u,v,1+u+v)`. Reject
these four events via their indicators:

\[
  uv,\qquad f_1u,\qquad f_2v,\qquad f_3(1+u+v).
\]

Each event is a consistent codimension-two affine subspace. If the first
event is rejected the three selectors are one-hot, so an avoiding point
chooses a true literal in every clause. Conversely such a choice supplies
an avoiding point. The last three events alone already preserve the SAT
answer: the selectors have odd parity, hence select at least one literal;
the possible extra `111` choice is legal only if all three literals are true.

Now suppose an encoded UNSAT instance has a static proof of degree `D` as
above. Substitute independently in each clause

\[
   u=t_1,\qquad v=f_1t_2,\qquad 1+u+v=f_1f_2.
\]

This is a ring substitution because all Boolean-ring elements are
idempotent. Under it the first three displayed indicators vanish; the last
is exactly the source clause's falsity indicator `f_1 f_2 f_3`. Every
surviving multiplier, of original size at most `D-2`, becomes a multilinear
polynomial of degree at most `2(D-2)`. Expanding it, each surviving product
is a source clause indicator times a monomial of size at most `2(D-2)`.
Derive these multiples in polynomial calculus by multiplying the clause
axiom by one variable at a time, then add the derived lines. Even charging
each multiplication its pre-reduction degree plus one, this is a source
refutation of degree **at most `2D-1`**. The same argument works if the
redundant `uv` events were omitted. It is a proof-degree transfer, not an
algorithm for discovering these refutations cheaply.

For the source lower bound use Alekhnovich and Razborov, [*Lower Bounds for
Polynomial Calculus: Nonbinomial Case* (2003)](https://www.mathnet.ru/eng/tm403),
[author's March 2003 manuscript, §2.1 and §4.3, Corollary 4.7](https://people.cs.uchicago.edu/~razborov/files/misha.pdf).
For fixed width 3 and fixed clause density `Δ=6` this gives degree `Ω(n)`
with high probability over **any field**, including GF(2), in the Boolean
polynomial calculus used above. These random instances are also UNSAT
with high probability: independent random signed clauses with distinct
variables give expected satisfying assignments `2^n (7/8)^(6n) = o(1)`.
Thus there exist unsatisfiable original formulas on `n` bits with `6n`
clauses for which static certificates on their selector-event images require
`D=Ω(n)`. The images use `13n` parameter bits and `24n` codimension-two
events (or `18n` after dropping selector-only events). This result uses a
characteristic-two lower bound; a theorem restricted to odd characteristic
would not justify it.

This rules out a fixed-degree completeness guarantee for this certificate
search **on the specified event encoding**. It does not lower-bound every
SAT algorithm, a system with arbitrary new extension variables, or a
separate preprocessing method producing different proof axioms. A high
required degree is not in itself a proof that a different discovery method
needs that many seconds or that all certificates have exponential size.

## Finite checks

The [tests](../tests/test_overlap_refutation.py) check coverage and evaluate
the generated certificate identities directly on all 2,048 arrangements of
the nonempty affine flats of the two-bit cube, plus seeded higher-dimensional
and malformed-certificate cases. A three-bit example has only rank-two
events, is fully covered, and exhausts its degree-two span without 1; its
degree-three proof succeeds. These tests support the implementation; the
unbounded-degree result uses the transfer and the stated prior theorem.

## Compact selector and occurrence padding

The same lower-bound transfer holds for the one-fresh-bit compilation with
just two bad indicators per source clause. With `f,g,h` the three literal's
falsity bits, in the same Boolean ring write

\[
 E_1=f(1+z),\qquad E_2=g(1+z+h).
\]

Then `g E_1 + f E_2 = fgh`: the same two `fg(1+z)` contributions cancel in
characteristic 2. Conversely set `z=1+(1+f)h`. This makes `E_1=0` and
`E_2=fgh` on **all** source assignments, not only satisfying ones. A degree-D
certificate for the compact cover therefore projects to a source PC proof
of degree at most `2(D-2)+3 = 2D-1` for exact-width clauses on distinct
variables. Each indicator in this compilation has codimension two: `z`
occurs in the second equality but not the first. This pullback rules out
fixed static degree on the compact *encoding*, independently of whether a
different elimination procedure can undo the selector first.

The hard-family statement can also require at least three appearances of
every occurring variable, as in the earlier [no-pair-merge class](hole_flats.md).
Before performing either selector compilation, for every original variable
`x` add `(x,u,v), (not x,u,w), (x,v,w), (u,v,w)` on three fresh private
variables `u,v,w`. Every original assignment extends by making the fresh
variables true. Restricting an arbitrary PC proof of the padded formula
to this same constant assignment kills the added clause axioms, preserves
the old ones, and cannot increase refutation degree (multiplication by a
restricted constant contributes at most the original degree). The padded
source therefore inherits the original lower bound, with only linear size
growth; every clause still has three distinct variables. This statement is
about the two explicit event encodings of those sources, not all possible
solver-specific reformulations.

[Formal/AffineCover.lean](../Formal/AffineCover.lean) states the local
selector identities and substitutions as Boolean function equalities,
one-bit existential projection, and the semantic implication from a finite
weighted XOR identity to coverage. It does not formalize the Python checker,
Gaussian elimination, the proof-degree transfer, or the cited PC lower bound.
