# Phase 24: affine-cover size does not measure general Boolean computation

The unfinished branch `research/affine-cover-circuit-boundary`, at
`54f7d62a74f4943007b39c39b2197e186ddae44e`, was the actual continuation point.
Its quadratic polar module did not compile. This cycle repairs that module
and connects it to an exponential covering theorem. The result closes a
specific proposed route from the preceding restricted lower bounds to P versus
NP: a small general computation need not have a small exact affine cover on
its original inputs.

This is an elementary representation obstruction, not a new circuit lower
bound or a P versus NP solution. The existing phase-20 affine-clause DAG
theorem and its remaining formalization obligations are unaffected.

## 1. Exact finite result

For `m` pairs of Boolean coordinates, write

\[
 Q_m(x,y)=\sum_{i=1}^m x_i y_i\in\mathbb F_2,
 \qquad P_m=\{(x,y):Q_m(x,y)=1\}.
\]

An affine one-cover is a finite family of injective affine maps

\[
 f_a:\mathbb F_2^{t_a}\longrightarrow\mathbb F_2^{2m}
\]

whose images are contained in `P_m` and whose union contains every point of
`P_m`. Overlaps and repeated images are allowed. The charts are mathematical
parameterizations; neither their construction nor a disjointness property is
assumed. Every nonempty affine flat has such an injective chart, so this
condition expresses a cover by flats, rather than an extra computational
restriction on how they are supplied. Empty sets can be omitted.

The checked finite inequalities are

\[
 t_a\le m,\qquad
 2^{2m-2}\le\sum_a2^{t_a}\le |A|2^m,
 \qquad |A|\ge 2^{m-2}\quad(m\ge2).
\]

The last lower bound is intentionally not claimed to be optimal.

In Lean the ambient coordinate type is `Option W`, with
`m = Fintype.card W + 1`. The two counting endpoints in
[`QuadraticAffineCover.lean`](../formal_pc/ProofLab/QuadraticAffineCover.lean)
are `cover_count_budget` and `exponential_cover_count`. They prove respectively

```text
2^(2 * card W) <= card A * 2^(card W + 1)
2^(card W - 1) <= card A          [Nonempty W]
```

The dimension bound, large subset of the positive level, and counting
inequalities are derived internally. No PC separation hypothesis or numerical
cover-size hypothesis is imported from the earlier DAG criterion.

## 2. Why each constant affine flat has dimension at most m

The explicit polar pairing is

\[
 B((x,y),(x',y'))=x\cdot y'+x'\cdot y.
\]

Probing against `(0,e_j)` and `(e_j,0)` recovers every coordinate, so the
linear map `z -> B(z,-)` into the dual space is injective. Domain and dual
have equal finite dimension, hence this map is a linear equivalence.

If `Q_m` is constant on `a+U`, its second difference gives

\[
 B(u,v)=Q_m(a+u+v)-Q_m(a+u)-Q_m(a+v)+Q_m(a)=0
 \quad(u,v\in U).
\]

Thus `U` is totally isotropic. The polar image of `U` has dimension `dim U`,
and `U` is contained in the common kernel of that image. The already checked
dual-kernel dimension theorem gives

\[
 2\dim U\le 2m.
\]

[`QuadraticPolar.lean`](../formal_pc/ProofLab/QuadraticPolar.lean) constructs
these maps, proves nondegeneracy and isotropy, and applies the dimension
theorem to the actual linear part of an injective affine chart. It works for
either constant value, including zero. A sharper bound for the nonzero value
is not used or claimed here.

## 3. Why the positive level is large enough

There is no need to assume or formalize an exact formula for `|P_m|`. For
arbitrary `x',y'` on the remaining `m-1` coordinates, define

\[
 x_0=1,\qquad y_0=1+x'\cdot y'.
\]

Together with `x',y'` these coordinates have inner product one. Distinct free
coordinate pairs give distinct full assignments. This explicit map is the
Lean `positiveSlice`, and supplies `2^(2m-2)` distinct points of `P_m`.

An injective chart with `t_a` parameters has at most `2^t_a` image points.
The finite-union bound counts points without assuming disjointness. Combining
it with `t_a <= m` proves the displayed bound. The exponent subtraction in
the last step is justified by `m >= 2`. A zero-parameter cube remains a
singleton throughout.

## 4. The same function has a small Boolean circuit

Compute the `m` products `x_i AND y_i` and XOR them in a chain. In the binary
gate basis `{AND, OR, NOT}`, an XOR of existing wires is

```text
u = a OR b
v = a AND b
w = NOT v
output = u AND w
```

It uses four gates. Reusing the current parity wire, the whole circuit uses
`m + 4(m-1) = 5m-4` gates for `m >= 1`. The description is uniform in `m`.
A sequential bit algorithm also takes linear time with direct access to the
two input blocks. This gate construction is a paper argument; the new Lean
endpoints formalize the geometric and finite counting statements, not a
general Boolean-circuit semantics or Turing-machine runtime model.

Consequently no fixed polynomial in general circuit size can bound the size
of an exact affine one-cover on the same original input variables for all
Boolean circuits. Applying such a proposed bound to this explicit linear-size
family contradicts the exponential finite covering bound for sufficiently
large `m`. This refutes that precise representation translation. It does not
refute every possible simulation into every affine-clause proof system.

## 5. Implication for the P versus NP objective

The preceding lower bound concerns affine clauses over original variables
with specified semantic inference rules. P versus NP concerns every uniform
polynomial-time decider. Completing the remaining expander and counting
formalizations would strengthen the evidence for the restricted theorem; it
would not supply the missing quantifier over all deciders.

The inner-product example makes one possible attempted bridge demonstrably
false: arbitrary small computations cannot always be flattened into small
unions of monochromatic affine flats on their original variables. Sharing a
Boolean circuit, using nonlinear intermediate functions, or adding extension
variables changes what must be represented. The current cover lower bound
must not be silently transferred to any of those settings. This example
alone also says nothing about the refutation complexity of a chosen circuit's
Tseitin encoding.

The next P-versus-NP-relevant target must specify a computation or proof model
that actually admits the intended efficient simulation, including its
auxiliary variables and bit cost, and prove a bound in that model. No such
universal simulation or all-algorithm lower bound has been established here.
Distinct-flat deduplication in the intrinsic DAG corollary, the expander
reduction operator, and the full phase-20 exponential formalization remain
separate unfinished tasks; this cycle does not label them completed.

## 6. Verification and provenance

The [machine-readable audit record](../results/affine_cover_formal_audit.json)
records the exact successful source commit, workflow/job IDs, source hashes,
observed transitive axiom sets, and preceding failed checkpoints. The package
pins and three MIT-licensed foundation files are unchanged. Standard Mathlib
caches may be used; this is not a fresh replay of every cached kernel object.
The gate-count argument and the all-circuit translation corollary are paper
deductions, explicitly separate from the named Lean endpoints.

The complete package build and all 126 endpoint axiom audits passed at
`6aa1b3feccd9476a2ef8209b16d22b1a6968e3b5` in
[run 42125609896](https://github.com/HeliCorgi/p-vs-np-lab/actions/runs/42125609896).
The separate core/reproduction workflow passed all 388 unit tests and matched
all 62 deterministic reports. The local unit suite also passed all 388 tests.
These regression checks are separate from the formal counting theorem.
