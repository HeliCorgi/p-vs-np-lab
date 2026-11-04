# Discover a global integer obstruction without guessing its modulus

## What is implemented

[`integer_hull.py`](../src/pnp_lab/integer_hull.py) takes only a Boolean
width-three CNF. It computes the integer affine hulls of proposed small local
relations, combines their equations over the integers, and returns either:

- `UNSAT`, with a refutation independently checked against the original clauses;
- `UNKNOWN`, including when the integer relaxation is feasible.

There is no list of primes or moduli to try. The algorithm may discover a
modulus such as 2, 3, 4, 9, or 25 from a global divisibility failure. It can also
discover an exact integer contradiction. A satisfying integer solution of the
relaxation is **not** a Boolean SAT witness. This component deliberately does
not return `SAT`.

The distinction from [local torsion diagnostics](local_torsion.md) is essential.
Every local table may have a torsion-free integer presentation while their
composition has a divisibility obstruction. For example, the equations around
an odd cycle are all `x_i + x_(i+1) = 1`; every individual edge has two Boolean
models and no local torsion. Eliminating the other variables produces `2*x = 1`.
The new component finds the resulting contradiction modulo 2.

## The exact relaxation

For a proposed variable scope `S`, take all original clauses contained in `S`
and enumerate their satisfying Boolean words `R_S`. Let

\[
L_S=\operatorname{span}_{\mathbb Z}\{(w,1):w\in R_S\}
\subseteq \mathbb Z^{|S|+1}.
\]

The selected-scope relaxation asks for **one shared integer vector** `x` such
that `(x|S,1)` belongs to `L_S` for every selected scope. The coordinates of `x`
are unrestricted integers at this stage. Different scopes must agree on the
same variable coordinate; their coefficients in the local model spans need
not agree on higher-order overlap marginals.

Equivalently, introduce integer variables `lambda_(S,w)` for each local word
and require

\[
\sum_{w\in R_S}\lambda_{S,w}=1,\qquad
x_i=\sum_{w\in R_S}\lambda_{S,w}w_i\quad(i\in S).
\]

The lambda variables may be negative. This is the unary-marginal affine
integer programming relaxation for the selected local relations. It is not
the hierarchy that equates all tuple distributions on overlaps, and it has no
nonnegative linear-programming constraints.

For each table, the existing local Smith reducer provides unimodular matrices
conceptually satisfying `U*M*V=D`, with the model vectors as rows of `M`.
Only the column operations constructing `V` are needed to extract the laws:

- A nonunit diagonal value `d_j > 1` gives
  `(x,1)*V_j = 0 (mod d_j)`.
- A zero diagonal position gives the exact equality `(x,1)*V_j = 0`.
- A unit diagonal position gives no restriction.

These are **all** conditions for integer membership in the local row lattice.
The affine constant is transferred to the right-hand side; an emitted row is
`a*x = b` when its modulus is 0, or `a*x = b (mod d)` when its modulus is `d>=2`.
Common factors and an inessential sign may be normalized. Duplicate global
laws are removed, retaining one original-clause justification.

The local Smith trace is independently replayed before use. The final UNSAT
certificate does not rely on trusting either that trace or its implementation:
its local laws are checked directly on Boolean models of the cited raw clauses.

## Global elimination and the discovered modulus

A congruence `a_i*x = b_i (mod d_i)` becomes

\[
a_i x-d_i z_i=b_i,
\]

with a distinct unrestricted integer slack `z_i`. Exact equalities need no
slack. The resulting system is an integer equation system `A*y=b`.

The implementation diagonalizes it with unimodular row and column operations.
Unlike a full Smith normal form, successive diagonal values need not divide
one another: diagonalization already decides whether the integer equations
have a solution. Every row operation tracks its integer combination of the
original local laws. Column transformations are used to change the integer
variable basis, never to divide a nonunit coefficient.

One useful implementation simplification is exact. After clearing a chosen
pivot column in all other live rows, adding a multiple of that column to
another live column changes only the pivot row. Such additions can be
performed without storing a dense change-of-basis matrix. Previously isolated
rows have zero entries in all remaining live columns and are unaffected.

Suppose an isolated row is `d*y_j=c`. If `d` does not divide `c`, the tracked
combination produces a contradiction **modulo `abs(d)`**. A zero coefficient
row with a nonzero right-hand side produces an exact contradiction. There is
no need to factor `d`, to pick a prime dividing it, or to normalize a nonzero
right-hand side to 1. In particular, `0=2 (mod 4)` is retained as a valid
refutation.

Why does the modular proof remain valid in the original coordinates? If `w`
is the tracked row combination, then after unimodular column operations its
coefficient vector is divisible by `d`. Multiplying by the integer inverse
change of basis shows that `w*A` in the original coordinates is also divisible
by `d`. The independent checker verifies that cancellation directly, including
the coefficients of the implicit congruence slacks.

## Independent certificate format

The certificate kind is `boolean-integer-hull-v1`. It contains:

- `modulus`: 0 for an exact contradiction, or an integer at least 2;
- `residual_rhs`: the nonzero final right-hand side, reduced modulo the modulus
  when it is positive;
- `terms`: local laws with `scope`, original `clauses` indices, `coeff`, `rhs`,
  local `modulus`, and an integer `weight`.

`check_integer_hull(n, clauses, certificate)` uses neither scope discovery,
Smith reduction, nor global elimination. For every term it independently
enumerates the Boolean assignments satisfying the cited original clauses and
checks the claimed local law. Then it verifies:

1. For final modulus `m>=2`, `m` divides `weight_i * local_modulus_i` for each
   term. This accounts for every unrestricted congruence slack.
2. Every original variable coefficient cancels modulo `m`.
3. The combined right-hand side is nonzero modulo `m` and matches the declared
   residual.

For an exact contradiction the same checks are exact integer equalities:
each weighted local modulus must be zero, every variable coefficient must
cancel, and the resulting right-hand side must be nonzero.

These conditions are sufficient for soundness. Any original Boolean model
satisfies every cited local law. A checked combination would force that model
to satisfy the displayed impossible integer or modular equation. The argument
does not require `m` to be prime. For a positive final modulus, the producer
reduces weights modulo `m` to shorten the certificate; the checker remains
valid for arbitrary bounded integer weights.

## Scope discovery, budgets, and limitations

The default proposal step combines the previous raw-clause and neighborhood
scopes of at most 9 bits with candidate three-port four-state domain scopes
of at most 15 bits. Four-state domains are used only to propose scopes. Their
actual Boolean relation is read afresh from the original clauses; no group,
modulus, charge, or state naming is supplied by the fixture. An explicit list
of scopes can instead be given for a controlled experiment.

The current implementation uses the following resource controls:

| Control | Default | Meaning |
|---|---:|---|
| `max_scopes` | no additional cap | Number of proposed scopes inspected |
| `max_models` | 256 | Number of satisfying Boolean words in one local table |
| `max_local_ops` | 20,000 | Elementary steps in each local Smith reduction |
| `max_rows` | 2,048 | Distinct retained exact/congruence laws |
| `max_columns` | 2,048 | Active integer coordinates, including congruence slacks |
| `max_ops` | 200,000 | Global elementary row/column additions |
| `max_bits` | 512 | Coefficient, transformation, combination, and RHS bit cap |

Local Boolean truth tables have width at most 15 even if a larger model count
would be allowed. The local model, operation, and bit caps cannot exceed the
existing local checker's hard limits. A table that exceeds a cap supplies no
claim that further integer laws do not exist. Unprocessed or skipped scopes
are recorded, and `scope_complete` becomes false.

`integer_feasible=True` means the **retained rows** are integer-feasible. It
does not establish feasibility for skipped scopes, and it never establishes
Boolean satisfiability. A contradiction using a subset of retained laws is
still a valid refutation even when another budget was reached.

Statistics report local profiles and skipped reasons, exact and congruence
row counts, active/slack column counts, row-operation counts, maximum observed
coefficient/combination/RHS bit lengths, and the discovered modulus. Operation
counts are counts of elementary matrix operations, not machine instructions;
the cost of an operation also depends on support and bit length. This bounded
implementation does not claim a worst-case polynomial decision algorithm for
unrestricted SAT, nor that its particular sparse diagonalization always stays
within a polynomial intermediate-size bound without a cap.

The obstruction to unrestricted SAT remains mathematical, not just a budget
choice. If every selected local model lattice is the whole augmented integer
lattice, the component has no nontrivial row to combine. The earlier local
flip-pair constructions give precisely this blindness. Furthermore, local
integer feasibility can hold even when Boolean ranges or nonlinear relations
make the original problem unsatisfiable. Other proof rules or additional
information are then needed.

## API and validation

```python
from pnp_lab.integer_hull import integer_hull_refute, check_integer_hull

answer = integer_hull_refute(n, clauses)
if answer["status"] == "UNSAT":
    assert check_integer_hull(n, clauses, answer["certificate"])
```

`collect_integer_rows` returns `(rows, stats)` for diagnostics or composition;
`check_integer_row` independently checks one such row. `integer_scopes` exposes
the deterministic scope proposals. The refuter validates its own certificate
against the original CNF before returning it.

The committed unit tests check all 256 Boolean three-bit relations, compare
350 random small integer systems and fixed edge cases with an independent
rank-and-maximal-minor lattice-index oracle, and verify original-clause binding,
malformed certificates, cap behavior, torsion-free local odd-cycle examples,
and scrambled ternary/order-four flows. For nonempty single-table relations,
feasibility is required to remain `UNKNOWN` with no purported Boolean witness.

The [carry-cycle fixtures](../src/pnp_lab/global_lattice_fixtures.py) add a
family in which all proposed local integer profiles are torsion-free but the
global equations give `m*x=q`. This separates global integer discovery from
the previous strategy of looking only for exceptional characteristics in
individual local tables. It is a controlled family result, not a P versus NP
solution.
