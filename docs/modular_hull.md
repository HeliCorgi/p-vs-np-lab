# Discover affine consequences over GF(3) from Boolean input clauses

A variable of the input always takes **only 0 or 1**. A *row* is a consequence
of the form `sum a_i x_i = b (mod p)`, with p=2 or p=3. Only the linear
relaxation may assign a field value other than 0 or 1. A contradiction in
that relaxation proves UNSAT; its consistency does not prove SAT. The
[finder and independent verifier](../src/pnp_lab/modular_hull.py) take signed,
one-based literals under an explicit variable scope and no problem-specific
tags, coordinate correspondence or charge data.

## Recognizing bounded candidate tables

Ignore tautologies, repeated literals, and duplicate copies of the same
signed clause when indexing by its set of variables; retain an original
zero-based clause ID for every retained clause. Include each raw clause
scope. Mark a triple as a candidate *block* if a ternary clause occurs on
it and some binary clause occurs on each of its three pairs. No sign
pattern is required, so an accidental block is harmless. For each occurring
clause scope replace each of its (at most three) variables independently
by its singleton or by any marked block containing it; include the union.
Also include the closed primal neighborhood of a variable when this has at
most nine members. Deduplicate, then process scopes in increasing size and
lexicographic order. The largest union is of size nine. This is a cheap
way to find promising scopes, not a completeness claim for every CNF.

For example, an unknown one-hot block has one ternary at-least-one clause
and three binary at-most-one clauses. A forbidden triple of indicators of
three distinct blocks reveals a nine-variable candidate comprising all three
blocks. A ternary constraint on indicators of two blocks and an ordinary
Boolean port yields a seven-variable candidate as well. Arbitrary renaming,
coordinate-wise complementation, or clause order shuffling preserves the
unsigned support patterns. Over GF(3), complementing a Boolean coordinate
acts on its column as `1-x`; both the coefficients and the right hand
side of a valid row may change. The finder need not identify the original
coordinate orientation.

## From a Boolean table to *all* its affine equations

For each proposed scope S, collect all indexed input clauses contained in
S. Enumerate exactly the bit words on S that satisfy those clauses. Bitset
truth tables are used for discovery. For the nonempty set T of surviving
words, form rows `(x,1)` for x in T and compute their right nullspace over
the chosen prime field. Every vector `(a,c)` in the nullspace gives
`a·x = -c`; conversely, every affine equation on the Boolean survivors is
represented this way. The implementation emits a basis, not every linear
combination. If T is empty the single impossible row `0=1` suffices.
Unlisted coordinates receive coefficient zero. Previously processed rows
are **not** assumed to be true local axioms when reading the input table.

Insert those equations into a second elimination over GF(p), saving linear
combination coefficients of original local rows at pivots. When a zero
left hand side has a nonzero right hand side, multiply by its inverse in
the field to obtain exactly `0=1`. Fold coefficients for rows that used
the same local evidence into a single row per contributing scope. If no
contradiction occurs, return UNKNOWN without a certificate.

`collect_modular_rows` provides the same local basis rows, IDs and stats
without global elimination, for composition with other checked rules.
`check_modular_row` verifies one such row. A row certificate lists scope,
original clause IDs, coefficients, and RHS. A full contradiction
certificate lists the prime and locally justified, already weighted rows.
The independent checker iterates the Boolean points in each scope; if a
point violates the claimed row, at least one cited original clause must
exclude it. It then adds each coefficient at its **original variable ID**
and each RHS modulo p. It accepts only zero total coefficient in every
column and RHS equal to one. This checker does not call the scope finder,
Boolean bitset table builder or Gaussian elimination. It certifies the
given input, never a reconstructed graph or a purported header checksum.

## Complexity and limits

With m explicit clauses a coordinate belongs to O(m) marked triples, so the
naive number of generated unions, counting repetitions, is O((m+1)^4).
Every local table has at most 512 Boolean points and ten augmented columns.
Fetching all local clauses takes at most 130 subset lookups (sizes 0,1,2,3
in a nine-bit table), and at most eight distinct sign patterns per such
nonempty triple. Building the closed neighborhoods, field elimination over
at most n global variable columns, explicit provenance and replay are all
polynomial in the original explicit input length for these fixed scope and
prime bounds. That worst-case polynomial is **not** asserted to be fast.
There is no enumeration of the graph's global flows. `max_scopes` caps
tables actually examined; it does not cap generating and deduplicating
candidate scopes, global arithmetic, or verifier time. Stats count
exhaustively represented table assignments, including bit-parallel work;
they are not timing or CPU-instruction counts.

The [tests](../tests/test_modular_hull.py) compare the field relaxation with
all affine equations for all 256 Boolean three-bit relations, independently
check scrambled zero/one-defect GF(3) flows on K4 and proof tampering, and
test budget and empty-formula behavior. The [five Lean
statements](../Formal/ModularHull.lean) address local truth-table
implication under coordinate renaming, soundness of weighted combinations,
a coefficientwise residual 0=1 in Fin 3, a nonzero residual including 0=2 in Fin 4, and an explicit Boolean-word
implication between row domains. They do not formalize the Python search,
parser, elimination, resource bound or completeness on arbitrary SAT.
