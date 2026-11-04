# Global torsion from locally torsion-free Boolean tables

The carry cycles in `src/pnp_lab/global_lattice_fixtures.py` isolate the next
question after the local Smith profiles: can an arithmetic obstruction appear
only when several locally saturated integer relations are composed? The answer
is yes, with any prescribed modulus. The discovery algorithm receives only a
signed, permuted width-three CNF, and discovers the modulus by integer
elimination. This is a controlled example for the [integer hull
relaxation](integer_hull.md), not a general SAT algorithm.

## 1. A saturated local gate

For Boolean coordinates `a,x,b`, the equation

\[
a+x-b=0
\]

has exactly the three words `(0,0,0)`, `(1,0,1)`, and `(0,1,1)`. Its raw clauses
are

\[
(\neg a\lor b),\quad(\neg x\lor b),\quad
(a\lor x\lor\neg b),\quad(\neg a\lor\neg x).
\]

Complementing all three bits gives the relation `a+x-b=1`, also encoded by
four clauses. Denote these two relations by `G_c`, for `c` equal to zero or one.

Neither gate has a hidden modulus. For `G_0`, the integer row lattice of the
augmented Boolean words is exactly

\[
\{(A,X,B,H)\in\mathbb Z^4:A+X-B=0\}.
\]

Indeed, if `B=A+X`, its vector equals `H` times `(0,0,0,1)`, plus `A` times
`(1,0,1,0)`, plus `X` times `(0,1,1,0)`. The last two generators are differences
of augmented model words. Complementation is an invertible integer change of
the augmented coordinates, so the same conclusion holds for `G_1`. All
nonzero Smith factors are one. Over every field the affine hull has precisely
the displayed equation, with no additional equation.

Deleting any gate coordinate leaves either an unconstrained bit or a
two-bit implication/at-most-one table. The latter has three Boolean words
forming an integer affine basis of the whole two-dimensional lattice. Thus
partial gate scopes introduce no new affine law.

## 2. Compose gates without revealing their modulus locally

Take `m` gates with distinct ports:

\[
a_i+x_i-b_i=c_i,\qquad i=0,\ldots,m-1.
\]

Connect `b_i` to `a_(i+1)` cyclically by a private equality path. Connect the
`x_i` along another path of equality paths, so that all of them represent a
common value `x`. Every private path has `L` edges, distinct internal Boolean
variables, and the usual pair of binary clauses on each edge. No equality
path connects two ports of the same gate.

Set the carries to

\[
c_i=\left\lfloor\frac{(i+1)q}{m}\right\rfloor
     -\left\lfloor\frac{iq}{m}\right\rfloor,
\qquad 0\leq q\leq m.
\]

They are Boolean, and their sum is `q`. The complete exact integer system
reduces to

\[
\boxed{m x=q.}
\]

The reduction uses only substitution along equality paths, and substitution
of successive gate outputs; these are unit-pivot integer operations. One
initial counter coordinate remains free. Consequently the nontrivial global
Smith factor is `m`, although every single gate has only unit Smith factors.
The full integer equations are feasible exactly when `m` divides `q`.

For `0<q<m`, the Boolean CNF is unsatisfiable, since even unrestricted integer
coordinates cannot satisfy `m*x=q`. At `q=0`, set every bit to zero. At `q=m`,
set every `x`-path bit to one and every counter-path bit to zero. These give
independently verified SAT siblings with exactly the same support structure.
The intermediate rational solution with `x=q/m` and initial counter zero has
counter values equal to the fractional parts of `i*q/m`, so all coordinates
lie in `[0,1]`. Rational feasibility, including these coordinate bounds,
therefore does not supply the integer refutation.

This point also gives a basic linear-programming relaxation solution. Each
gate's intersection of its equation with the Boolean cube is exactly its
three-vertex triangle, so its rational point is a nonnegative distribution
over the three allowed words. An equality path uses the distribution on its
all-zero and all-one words with the prescribed marginal. The shared one-bit
marginals agree. Thus the obstruction here is integrality, not failure to
find a rational convex combination of local models.

There are

\[
N=3m+(2m-1)(L-1),\qquad
M=4m+2L(2m-1)
\]

Boolean variables and clauses. With `L=10`, these are `21m-9` and `44m-20`.
The direct explanation `m*x=q` is a linear-size integer proof, with
coefficients of bit length `O(log m)` after substitution. This size statement
describes this family and its explicit proof; it is not a bound on unrestricted
SAT proof discovery.

## 3. Every small raw local table is still torsion-free

**Local statement.** For every raw scope containing at most `L` Boolean
variables, its integer affine hull is defined by the complete gate equations
and equality-edge equations actually contained in that scope. It has no
torsion.

A complete equality path contains `L+1` vertices. Such a scope cannot contain
a complete private path linking two gate ports. Each connected component of
its induced constraints therefore contains at most one gate, together with
dangling equality paths, or consists only of equality paths. A full gate has
the saturated lattice proved above; a partial gate has a full affine lattice.
Appending equality copies duplicates coordinates by unit-pivot substitutions,
and adds no torsion. The components have independent choices, so their
Cartesian product has the product affine lattice. This proves the statement
for every such scope, not merely the scopes sampled by the implementation.

The finite experiment uses `L=10`. The algorithm's default scope finder
actually proposes scopes of at most five variables on these instances; its
four-domain detector proposes none. Every proposed scope is profiled, with
no skipped table, and every profile has only unit Smith factors. The generator
metadata is not passed to the algorithm. A signed permutation of variables is
an invertible affine transformation over the integers, preserving these
claims, while clause and literal order carry no information used by them.

## 4. All prime fields can agree while the integers refute

Over a field of characteristic `p`, the full gate/wire equations are feasible
if and only if

\[
p\nmid m\quad\text{or}\quad p\mid q.
\]

When `p` does not divide `m`, set `x=q/m` in that field, choose one initial
counter, and propagate around the cycle. When `p` divides both `m` and `q`,
choose any `x` and again propagate. When `p` divides `m` but not `q`, summing
the gates yields an immediate contradiction. Characteristic-zero fields are
always feasible. Thus every prime-field linear system is feasible exactly
when `rad(m)` divides `q`, where `rad(m)` is the product of the distinct prime
divisors of `m`.

| Global equation | Every prime-field linear system feasible? | Integer result |
| --- | --- | --- |
| `4x=2` | Yes | Contradiction modulo 4 |
| `5x=1` | No: characteristic 5 refutes | Contradiction modulo 5 |
| `7x=1` | No: characteristic 7 refutes | Contradiction modulo 7 |
| `8x=2` | Yes | Contradiction modulo 8 |
| `9x=3` | Yes | Contradiction modulo 9 |
| `25x=5` | Yes | Contradiction modulo 25 |
| `49x=7` | Yes | Contradiction modulo 49 |

Because every small local affine law follows from the displayed gate/wire
equations, the field assignment also satisfies every such law. This is a
statement about **field-valued** solutions. It does not assert that the
solutions in different fields are the same Boolean word, or even Boolean.
For example, `4x=2` implies `x=2` over `F_3`, which no Boolean value satisfies.

That distinction matters in comparison with phase 14. The previous
`mixed_modular` procedure translates consequences through Boolean truth
tables, and already refutes the tested carry-cycle controls for `m` equal
to 4, 5, 7, and 9. The experiment records those successful baseline
refutations. These examples demonstrate automatic discovery of a global
integer modulus; they do **not** establish a strict separation from the
earlier Boolean field bridge.

## 5. Reproduction and boundaries

Run `experiments/global_integer.py --out-dir <directory>` with `src` on
`PYTHONPATH`. The report contains fourteen signed/permuted inputs: seven
unsatisfiable carry cycles, and seven SAT siblings with checked original
Boolean words. The integer routine reports `UNKNOWN` for the latter, because
integer-relaxation feasibility is not a general SAT certificate.

The largest example has 1,020 variables and 2,136 clauses. All 2,280 proposed
local scopes are torsion-free, yet global elimination produces a checked
1,019-term contradiction modulo 49. The report includes the complete raw
75-variable `4x=2` instance and its independently replayed certificate as a
small specimen. All terms in these certificates are local **exact** integer
equations: their local modulus is zero, and the nonzero final modulus is
discovered only globally.

The report also replays a concrete failure control. The earlier
[`modular_barrier.json`](../results/modular_barrier.json) contains a checked
957-node refutation tree for a 31-variable, 152-clause formula. Its all-positive
signing on the same supports has the all-one SAT witness. For **both** inputs,
all 152 discovered root scopes have a full integer affine lattice and produce
zero equations. The integer routine returns `UNKNOWN` with a feasible
relaxation. The [conditional integer pass](integer_probe.md), with no outer
call cap and no private-resolution prepass, then tries both values of every
variable: 63 integer calls per input, zero learned units, and `UNKNOWN` at a
fixed point. No inner resource limit is hit. The saved raw UNSAT tree is
rechecked, not rediscovered by another exponential search; its hash and source
report are recorded. This executable control prevents either integer
composition or this one-variable conditioning rule from being described as a
complete SAT algorithm.

For the relation to established affine integer programming, the distinction
between signed integer coefficients and nonnegative distributions, and the
remaining obstruction for general SAT, see [global integer
theory](global_integer_theory.md). No novelty or general complexity-separation
claim is based on this fixture family.
