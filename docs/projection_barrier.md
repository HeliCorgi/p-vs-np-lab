# Existential projection can require wider boundary clauses

This experiment checks an elementary limit of a particular representation. It
does not claim a new theorem: a small graph already shows that short clauses over
boundary color relations need not remain short after internal variables are
eliminated.

## The graph and the relation

Fix a palette of exactly `q` available colors, with `q >= 2`. There are `q`
ordered boundary terminals `t0, ..., t(q-1)` and one internal vertex `x`.
The only edges join `x` to each terminal. Thus the input constraints are

\[
\bigwedge_{i=0}^{q-1} c(x)\ne c(t_i).
\]

For a boundary assignment, a color for `x` exists precisely when the terminals
leave at least one palette color unused. Because the number of terminals equals
the palette size, the projected relation is

\[
R_q(t_0,\ldots,t_{q-1})
 = \exists x\;\bigwedge_i c(x)\ne c(t_i)
 = \neg\operatorname{AllDifferent}(t_0,\ldots,t_{q-1}).
\]

It has the following exact auxiliary-free CNF, consisting of one clause:

\[
\bigvee_{0\le i<j<q} c(t_i)=c(t_j).
\]

For `q=5`, there are 52 boundary color partitions up to palette renaming. Exactly
51 are allowed: the excluded partition is `01234`. The displayed clause has ten
equality literals.

## Why all ten literals are necessary when q=5

The permitted literals are terminal-pair color equalities and disequalities.
There are no auxiliary variables in the representation being considered. Every
assignment is an actual coloring, so equality predicates satisfy the usual
equivalence-relation rules; they are not independent Boolean variables.

Consider any CNF that represents the projected relation exactly.

1. It rejects the all-distinct boundary. At least one of its clauses must
   therefore be false on that boundary.
2. Every terminal-pair disequality is true on an all-distinct boundary. A clause
   false there cannot contain a disequality literal. It can contain only
   equality literals, after harmless duplicates and constants are removed.
3. For each pair `(i,j)`, make exactly those two terminals equal and keep every
   other terminal color distinct. This uses `q-1` colors, so it extends to the
   star using the remaining color at `x`.
4. The only true terminal-pair equality on this witness is `c(t_i)=c(t_j)`.
   A valid clause false at allDistinct must include this literal. Otherwise it
   would reject an allowed witness.

Consequently that clause must contain every terminal-pair equality. Its width is
at least `q*(q-1)/2`. The full equality disjunction achieves this width, so the
bound is exact. Adding more narrow clauses cannot avoid the argument: one clause
still has to reject the all-distinct assignment, and each clause must be true on
every allowed assignment.

The certificate consists of the excluded state and one allowed witness per
terminal pair. For `q=5`, this is ten witnesses, without an exhaustive search
over all subsets of the twenty equality/disequality literals.

| Available colors and terminals | Canonical boundary states | Allowed states | Required clause width |
|---|---:|---:|---:|
| 3 | 5 | 4 | 3 |
| 4 | 15 | 14 | 6 |
| 5 | 52 | 51 | 10 |
| 6 | 203 | 202 | 15 |

For `q=3` and `q=4`, the program additionally checks all normalized clauses false
at allDistinct. These contain only equality literals, so there are respectively
8 and 64 candidates. In each case, only the full equality disjunction is valid
on the projected relation.

## What the experiment establishes

With the palette fixed at five colors, this example rules out closure under
existential projection for auxiliary-free CNFs over terminal-pair color
predicates whose maximum clause width is below ten, including width two. The
input is a conjunction of binary disequality constraints. The projected
relation itself has an exact width-ten clause.

For the general family, no one clause-width bound covers all members as `q`
grows. In that statement, **both the palette size and the number of terminals
grow with `q`**. It does not establish that every fixed clause-width bound fails
when the palette stays at five colors and only the number of terminals grows.
That separate fixed-palette question is not settled by this example.

Retaining `x` changes the representation: the same relation has an existential
representation using only `q` binary disequality constraints. The obstruction
depends on eliminating auxiliaries and restricting the available boundary
literal vocabulary. It does not forbid other representations or algorithms.

This result is distinct from Boolean 2-SAT. A binary color constraint concerns
two variables with `q` possible values, and an equality literal is a predicate
on those values. It is not a clause of two independent Boolean variables. The
result is also not a running-time lower bound, a Hadwiger--Nelson geometric
construction, or a P-versus-NP separation.

For interpreting boundary-compression experiments, the lesson is specific:
finding an exact short formula for one interface does not by itself establish
that arbitrary subsequent projections will admit formulas in the same class.

## Finite-relation API and safeguards

`src/pnp_lab/relations.py` provides exact, explicit finite tables:

- `FiniteRelation(variables, color_count, rows)` stores labeled color tuples on
  an ordered variable scope.
- `join` and `conjoin` form natural joins, matching actual colors of shared
  variables. The output order is the left scope followed by new right variables.
- `project(ordered_variables)` existentially eliminates everything else and
  preserves the requested terminal order. `exists(variables)` is a convenience
  operation preserving the order of the variables retained.
- `canonical_rows()` returns color partitions only after checking complete
  palette-permutation symmetry. A named-color pin such as `c(t0)=2` generally
  breaks that symmetry and is rejected by this summary operation.
- `ColorLiteral`, `clause_holds`, and `cnf_holds` evaluate equality/disequality
  predicates on actual color assignments.

Color canonicalization never rearranges terminals and never occurs before a
join. Independently canonicalizing two partial assignments could destroy the
identification of colors across their shared boundary. Named-color pinnings
remain valid finite relations with their original labels; they are not treated
as interchangeable color classes.

Explicit tables can grow exponentially. This API is a small exact reference
implementation for experiments and checks, not a claimed efficient solver for
unbounded instances.

## Reproduce

From the repository root:

```bash
python experiments/projection_barrier.py --out-dir results
PYTHONPATH=src python -m unittest discover -s tests -p test_relations.py -v
```

The default palettes are `3 4 5 6`; `--colors 3 4` runs a smaller subset. The
experiment writes `results/projection_barrier.json`. The output records the
explicit graph family, source-file SHA-256 hashes, all canonical allowed states,
the exact CNF, every single-pair witness, and all verification outcomes. It has
no timestamps, random inputs, or external-data dependencies.

For every palette, verification compares relation joins followed by projection
against a separate brute-force check of every boundary assignment and every
center color. It also checks the counts `q*(q-1)^q` for full star colorings and
`q^q-q!` for allowed labeled boundary assignments. Tests cover natural joins with
reordered shared scopes, existential composition versus direct graph checks,
empty relations, palette mismatch, color-pinned relations, and clause semantics.
