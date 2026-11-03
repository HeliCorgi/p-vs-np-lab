# Exact XOR + CNF solving by an observed affine quotient

This module gives a uniform exact algorithm for every finite Boolean XOR + CNF
input. Its running time is exponential in an explicitly defined observation
rank. It does **not** give a polynomial-time algorithm for unrestricted SAT, a
P versus NP separation, or a new claim about the difficulty of all algorithms.

The contribution here is an executable construction, its full-input correctness
argument, and independently evaluated finite examples. Gaussian elimination and
enumeration of free Boolean choices are established methods. The name
`effective_rank` is a field in this implementation, not a claim of a new or
minimal measure of nonlinearity.

## Input and API

The input is an `AffineRelation` and an ordinary CNF. The explicit list
`affine.variables` contains distinct names for **all** variables, including
unconstrained variables and variables appearing only in the CNF. A DIMACS
literal `i` means `variables[i - 1]`; `-i` means its negation. Zero is not a
literal. Each clause is a tuple of literals, and the CNF is a tuple of clauses.
There is no DIMACS terminating zero inside this API.

```python
from pnp_lab.affine import AffineRelation
from pnp_lab.mixed import solve_mixed, check_sat_witness, check_unsat_certificate

affine = AffineRelation.from_named(
    ("x", "y", "a", "b", "unused"),
    [(("x", "a", "b"), 1), (("y", "a", "b"), 0)],
)
cnf = ((1, 2),)  # x OR y
result = solve_mixed(affine, cnf, include_trace=False)
assert result["affine_dimension"] == 3
assert result["effective_rank"] == 1
assert result["checked_cells"] == 2
assert result["model_count"] == 8
assert check_sat_witness(affine, cnf, result["witness_mask"])
```

`solve_mixed` accepts four keyword options:

| Option | Default | Meaning |
|---|---|---|
| `exhaustive` | `True` | Enumerate all quotient cells, also obtaining the exact model count when complete. If `False`, stop at the first witness. |
| `max_cells` | `None` | Optional nonnegative limit on evaluated quotient cells. It is not a time or memory limit. |
| `include_trace` | `True` | Return the visited representatives and original-CNF truth counts. |
| `include_certificate` | `False` | If UNSAT is established, return an explicit proof object including every rejecting quotient cell. |

These options are independent. Large experiments should normally disable both
trace and certificate. Requesting a certificate can create exponential output
even when trace is disabled. If a certificate was not requested, the
`certificate` field is `None`: it does not secretly denote a succinct
certificate that the checker will exhaustively regenerate.

The result is JSON-compatible. `status` is `SAT`, `UNSAT`, or `UNKNOWN`.
`exhaustive` states whether the computation actually finished the quotient;
`requested_exhaustive` records the requested mode. A SAT witness found before a
budget expires still establishes SAT, but incomplete enumeration leaves
`model_count` as `None`. A budget exhausted without a witness gives `UNKNOWN`,
never UNSAT. There is no implicit default cap.

The empty CNF is true; an empty clause is false. An empty scope has one
assignment. An inconsistent XOR system is UNSAT immediately, with zero checked
cells, model count zero, and `affine_dimension` / `effective_rank` equal to
`None`. For a consistent system, rank zero has **one** quotient cell.

## Definition of the observation rank

After exact elimination, write the XOR solution set as

\[
 x_i=c_i\oplus\langle a_i,t\rangle,\qquad t\in\mathbb F_2^d.
\]

Here `d` is the affine dimension. The free coordinates give an injective and
onto parameterization of the input XOR solution set. The implementation reads
the normalized RREF already provided by `AffineRelation`; it does not use
floating-point arithmetic.

Remove tautological clauses, repeated literals, and duplicate clauses from the
CNF. Keep an empty clause if present. This normalization performs no general
SAT reasoning, unit propagation, or affine-aware simplification. Let `S` be the
set of variable indices occurring in the remaining clauses. Define

\[
 r=\dim\operatorname{span}\{a_i:i\in S\}.
\]

Thus `r <= d <= n`. The definition includes variables in unit clauses and can
overestimate the information needed to decide a particular formula. It is not
the minimum nonlinear rank of the Boolean function. Removing a tautological
clause is sound because its truth is independent of every variable it names.

Choose a row basis `b_1,...,b_r` of this span and define

\[
 q(t)=(\langle b_1,t\rangle,\ldots,\langle b_r,t\rangle).
\]

The basis is computed in RREF. A unit vector at each basis pivot column is a
column of a right inverse `L`, so `q(Lz)=z` for every `z` in `F_2^r`. This is an
explicit deterministic witness lift, not an oracle for finding a fixed point.

## Correctness for every finite input

**Lemma 1: the parameterization covers exactly the XOR solutions.**
For a consistent RREF, choose the nonpivot variables freely. Each pivot
equation uniquely determines its pivot variable from those choices. The
resulting assignment satisfies every equation. Conversely, every solution has
one choice of the free variables and is reproduced by this construction.

**Lemma 2: the CNF is constant on each fiber of `q`.**
Every observed `a_i` is a linear combination of the basis forms. If `q(t)=q(u)`,
then `dot(a_i,t)=dot(a_i,u)` for every observed variable. These variables have
the same affine offsets, so each non-tautological clause has the same truth
value. Tautological clauses are always true. Hence the original CNF is
constant on each fiber, including when duplicates or an empty clause occur.

**Lemma 3: all fibers are represented.**
The rows of `q` are independent, so `q` is onto `F_2^r`. The constructed right
inverse gives one representative `t=Lz` for every possible cell `z`. Therefore
enumerating `z=0,...,2^r-1` covers all truth possibilities of the CNF inside the
XOR solution set.

**Theorem: a completed run is sound and complete.**
If a representative satisfies the CNF, its affine lift is a model of the entire
input. If every representative rejects the CNF, Lemma 2 excludes every point
in each fiber, while Lemmas 1 and 3 cover every possible model. Thus the input
is UNSAT. Inconsistency of the XOR system separately establishes UNSAT before
this construction. Without a budget, the finite loop terminates for every
finite input. Early SAT termination is sound; incomplete rejection alone is
not a proof and is reported as UNKNOWN.

Each fiber has `2^(d-r)` points by rank-nullity, and the parameterization is
injective. Consequently a completed run also returns the exact number of
models:

\[
 \#\mathrm{models}=\#\mathrm{satisfying\ cells}\cdot 2^{d-r}.
\]

## Complexity and the remaining exponential

Let `N` be the bit length of the explicitly encoded input, including all
variable names, XOR rows, and CNF literals. In particular, `n` is bounded by
the input size: a binary integer declaring an astronomically large implicit
scope is not the input model. Let `m` be the number of XOR rows before
normalization and `C` the CNF encoding length.

Gaussian elimination, parameterization, rank computation, and construction of
the right inverse use polynomially many operations on finite masks with at
most `O(n)` bits. A conservative implementation-level bound for these ordinary
elimination steps is polynomial in `m+n+C`; no tight performance claim is
needed. Each of the `2^r` cells uses polynomial work to form a representative,
lift it, and evaluate the clauses. Therefore

\[
 T(N)=O(\operatorname{poly}(N)+2^r\operatorname{poly}(N)).
\]

Python's arbitrary-size integers do not make long rows constant-cost:
intersection, XOR, shift, parity/popcount, and arithmetic act on finitely many
stored bits. Charging, conservatively, polynomial bit cost for each such
operation preserves the displayed bound. Cell counters and the exact model
count need at most `O(n)` bits, aside from input-dependent bookkeeping. Input
normalization by `AffineRelation` is part of the overall polynomial work, even
though the solver receives an already constructed object.

Without trace or certificate storage, working space is polynomial in `N`.
With either enabled, storing all visited cells takes up to
`O(2^r poly(N))` bits. If both are serialized, cells appear in both output
locations. Certificate verification is polynomial in input **plus explicit
certificate size**, and can therefore also be exponential in the original
input.

Every ordinary CNF is an input: choose an unconstrained `AffineRelation` over
its occurring variables. The coefficient forms are then the coordinate unit
vectors. After the stated trivial normalization, `r` is the number of
occurring variables and can equal `n`. Thus this uniform algorithm still
contains exhaustive `2^n` enumeration for unrestricted SAT. A small rank on
some instances is useful structure, not a polynomial bound for all inputs.

## Checkers, proof objects, and trust

`check_sat_witness` directly evaluates the normalized input XOR rows and the
original CNF, without using the solver's affine parameterization, observation
basis, right inverse, or clause-mask evaluator. `AffineRelation` has already
normalized the input, so this checker alone does not independently verify the
original pre-normalization XOR rows. The finite tests retain those raw rows
and compare against a separate exhaustive oracle.

An `affine-quotient-unsat-v1` certificate contains an affine base point and
forms, the observation basis and its right inverse, aggregate counts, and all
rejecting cells. The checker does not call the solver or its compiler. It
verifies that the given affine map lies inside the XOR solution set and has
dimension `n - rank(A)`, hence is onto; verifies the observed span and right
inverse; checks that the ordered cell list contains exactly every `r`-bit cell;
and independently evaluates each representative and its original-CNF truth
count. It rejects missing or duplicate cells and false algebraic or evaluation
claims. An alternate valid proof may also be accepted: this is a semantic
checker, not a cryptographic integrity check.

For a normalized contradictory XOR system, the shorter
`inconsistent-affine-v1` certificate simply identifies the existing `0=1` row.
It is not a derivation from the pre-normalization rows. `certificate=None` is
rejected by the checker. SAT and UNKNOWN results carry no UNSAT certificate.

The trusted implementation includes Python's finite integer operations,
`AffineRelation` normalization, encoding validation, and the checkers themselves.
The SAT checker shares the input validator; the UNSAT checker uses its own
high-pivot echelon rank computation and scalar evaluations rather than the
solver's low-pivot RREF and lift. These separate paths reduce correlated
implementation mistakes; they do not eliminate the trust boundary.

The mathematical argument applies to all finite inputs. Fixed-seed tests and
finite experiments check executable instances of that argument.
[`Formal/QuotientSearch.lean`](../Formal/QuotientSearch.lean) proves the abstract
quotient/lift and enumeration logic. Its residual predicate is already assumed
to factor through the observation map; the argument for the original CNF's
fiber invariance is the mathematical Lemma 2 above. The Lean theorem does not
formally verify this Python implementation, Gaussian elimination, parsing, or
certificate checker. The precise connection to general 3SAT is given by the
[binary-CNF plus XOR reduction](two_cnf_xor_reduction.md).

## Local checks

```bash
PYTHONPATH=src python -m unittest discover -s tests -p 'test_mixed.py' -v
```

The tests compare 180 fixed-seed systems with an independent truth-table oracle
over the raw XOR rows and CNF. Additional cases check affine offsets, dependent
observations, unused directions, variable reorderings, constants, empty scopes,
tautologies, pure CNF, budgets, witnesses, JSON round trips, and incorrect
certificate modifications. These finite checks do not constitute an
asymptotic lower bound or an end-to-end formal proof of the code.

## Related primary source

Matthew Gwynne and Oliver Kullmann, [*On SAT representations of XOR
constraints*](https://arxiv.org/abs/1309.3060), 2013 / LATA 2014, studies CNF
representations of systems of linear equations over GF(2), including the
strength of propagation in those representations. That is background for why
native XOR reasoning and ordinary CNF encodings should be distinguished. It
does not establish a novelty claim for the observation-rank algorithm above;
the correctness argument for this implementation is stated explicitly here.
