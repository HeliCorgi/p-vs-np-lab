# Local XOR translations, matching, and the binary defect left behind

For explicit finite supports \(S_i\subseteq\mathbf F_2^d\), pick one member of each so their XOR is \(t\). An empty support is impossible; with no groups the only sum is zero. Here the coordinates are fixed. We change the *origin* separately in each group, not the basis of the ambient space.

## A polynomially recognizable matching case

If \(S_i\) lies in the Hamming ball of radius one about \(c_i\), all its translates \(u_i=s_i+c_i\) have weight zero or one. The exact identity

\[
 \sum_i s_i=t\quad\Longleftrightarrow\quad\sum_i u_i=t+\sum_i c_i
\]

reduces an entire instance of such groups to the [unit-mask perfect matching algorithm](support_threshold.md). Addition throughout is XOR. The translated target may be nonzero, even if the original target was zero. On SAT, undo each translation and check the choices directly on the original supports and target. A matching rejection relies on the existing maximum-cardinality matching backend, not on a new short UNSAT certificate.

Recognition does not enumerate \(2^d\) possible centres. For two distinct options \(a,b\), a centre covering both is either one of the two endpoints (distance one), one of their two one-bit midpoints (distance two), or nonexistent (distance greater than two). Test the at most two candidates on all other options. Singletons can use the option itself as centre. If every option already has weight at most one, use zero. These operations take polynomial bit time in the explicit input size.

For at most three distinct options, pairwise distances at most two suffice for a common centre. For a triple take the coordinatewise majority \(m\). The coordinates in which just \(a,b,c\) disagree with their majority form disjoint sets of sizes \(i,j,k\); pairwise distances are \(i+j,i+k,j+k\). If \(i\ge2\), then \(j=k=0\) and \(b=c\), contrary to distinctness; similarly for the others. Four options can fail this property: \(000,011,101,110\) have pairwise distance two but no common radius-one centre.

## When only some groups fit

Partition each support into disjoint pieces, each contained in one radius-one ball. The implementation greedily removes a ball covering the largest number of still unassigned options. To find such a ball, enumerate all original remaining options as singleton centres and the at most two candidate centres of each pair. Thus even on unrestricted explicit list sizes this preprocessing is polynomial. For a nonfitting triple the minimum piece count is two if any pair has distance at most two, and three otherwise. The partition uses that minimum. No optimality is asserted for larger supports.

The product of the piece counts is a raw bound on matching calls. To reduce it, set aside the **nonfitting binary** groups. Each is \(\{a_i,b_i\}\), with \(D_i=a_i+b_i\) and a bit \(y_i\) selecting its option \(a_i+y_iD_i\). Choose one piece for each nonbinary split group; this is one *outer branch*. The other, matchable groups now have fixed supports \(P_g\) (one whole support or one piece). Choose an anchor \(p_g\in P_g\), and form

\[
 W=\operatorname{span}\{s+p_g:g,\ s\in P_g\},\qquad
 q_W\left(\sum_i y_iD_i\right)=q_W\left(t+\sum_g p_g+\sum_i a_i\right),
\]

where \(q_W\) is echelon reduction modulo \(W\). The displayed system is **necessary**: the matchable-side sum differs from its anchor sum by an element of \(W\). It need not be sufficient; the actual sums need not fill their affine hull. Gaussian elimination with selector provenance either rejects the whole outer branch or supplies one solution and an independent kernel basis. If there are \(b\) binary defects and the projected columns have rank \(r\), enumerate the \(2^{b-r}\) selector solutions in Gray order. For each, subtract the chosen binary masks and apply the translated unit-matching decision to the remaining groups.

Every original solution lies in exactly one outer piece combination, satisfies the projected equation, and is recovered by the corresponding matching problem. Consequently exhausting all consistent leaves proves UNSAT and finding one checked witness proves SAT. Multiple solutions of one matching problem are never counted. If \(M\) is the number of outer combinations, the bound is polynomial preprocessing per outer branch plus at most \(\sum_{\text{consistent outer }j}2^{b-r_j}\) polynomial-cost matching calls. In particular large ranks are useful, but the number of outer branches and selector nullities still matter. All mask, rank, and graph operations charge polynomially many bits per subproblem; the displayed sum need not be polynomial.

[`decide_with_gauge_matching`](../src/pnp_lab/gauge_matching.py) has separate `max_matching_calls` and `max_outer_branches` limits. The former does not cap a sequence of affine-rejected outer branches. Neither is a wall-clock or memory limit. A partially covered search returns `UNKNOWN`, never an unjustified UNSAT. `branches_total` counts the raw product *before* quotient filtering; `compatible_branches_identified` counts all solutions of the projected systems actually reached, not matching calls or models. Singleton choices and verified translations retain the original order in the returned witness.

## What happens on the actual sparse 3SAT image

In the [weight-two constructor](../src/pnp_lab/ternary_support.py), a clause chooses among unit selector masks. Each shifted occurrence implication is a translate of a radius-one support: its three distinct options live on two coordinates \(V_j,C_j\) and span both difference directions. A singleton-occurrence variable has a matchable copy group. A variable with multiple occurrences has one nonmatchable binary copy per occurrence: \(V_j\) and a pair of equality ports, separated by distance three. Thus there is exactly one outer branch. Its \(W\) is precisely the span of all value and clause-selector coordinates (for formulas with no empty clause). Modulo \(W\), a binary copy difference is just the sum of the preceding and following equality ports on its variable's cycle. Equality ports occur in no other groups.

The homogeneous equations on a cycle with \(k\ge2\) copies force all its selector bits to agree: one equation for every neighboring pair. All-false anchors give a consistent choice of equality bits; choosing the other anchor convention would only translate the selector solutions. A cycle has rank \(k-1\), including the length-two cycle with two distinct parallel ports. For \(v\) repeated variables and \(b\) total repeated occurrences, the rank is \(b-v\); the raw \(2^b\) choices shrink to exactly \(2^v\) matching candidates. This derivation applies regardless of literal signs. Existence of these affine completions does **not** assert existence of satisfying assignments. On SAT, search can stop early; on UNSAT this backend tests them all.

For a connected odd cycle on \(n\ge3\) vertices, use both \((x_i\lor x_{i+1})\) and \((\neg x_i\lor\neg x_{i+1})\) for each edge. The source demands alternating bits and is UNSAT. Every variable occurs four times; the algorithm reduces the raw \(2^{4n}\) leaf product to \(2^n\) compatible candidates and makes **exactly \(2^n\) matching calls**. The bit encoding has polynomial length in \(n\), so this is an all-size superpolynomial lower bound on this specific deterministic implementation without budgets. The source is 2-CNF. It neither lower-bounds other algorithms nor is an obstacle to a method recognizing this family directly.

## Reproducible checks

[`results/gauge_matching.json`](../results/gauge_matching.json) is generated by [`experiments/gauge_matching.py`](../experiments/gauge_matching.py). In a 64-group positive control every raw option had weight greater than one; a single translated matching instance returned a checked witness. For an explicit dense translate of three corners of a square, the affine hull kept the missing corner while matching correctly rejected it. For a signed three-variable 3-CNF with exactly one model, the necessary affine test kept all eight binary assignments; matching found the original model `101` on its seventh call. Adding the eighth exclusion clause made the source unsatisfiable and required all eight calls.

The source checks cover 81 formulas (including controls and cycles), all 1,139 source assignments, and direct lift/projection checks of 235 source models. On the seven-variable odd cycle the raw-before-pruning product is 268,435,456, while **128 matching calls were actually made**. Independent budget controls exercise both ways to return UNKNOWN. These checks validate finite cases; the arguments above establish the stated general guarantees and limitations.
