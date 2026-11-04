# Project the forbidden union exactly, and lift an original witness

The input is a list of affine bad events on binary parameters. Each event is an AND of parity equations; all such events are ORed. SAT means that some point **avoids** that union. This backend computes an existential projection and does not count witnesses.

## One-bit identity

Fix all remaining bits at a point y. Write C for the common forbidden part independent of bit x, A for the union of the other bad events sliced at x=0, and B for the corresponding union at x=1. No choice of x can work exactly when

    (C or A) and (C or B) = C or (A and B).

Distributing the last intersection creates pairwise intersections of affine slices, again affine or empty. Row reduction discards inconsistent intersections. Starting with the input, this equality maintains the precise set of **unextendible** remaining points after every elimination. Absent bad sets mean a survivor exists; a forbidden whole space means none exists. To recover bits, walk the recorded layers backwards: try zero and, if that hits a bad set, try one. The projected invariant guarantees one choice works. Independently evaluate the original events before returning SAT. The [Lean bit lemma](../Formal/AffineCover.lean) proves the pointwise equivalence for arbitrary event labels; it does not certify the row-reduction code.

This is related to Boolean variable elimination, not a claim of inventing existential quantification or resolution. See Davis and Putnam, [A Computing Procedure for Quantification Theory](https://doi.org/10.1145/321033.321034).

## Reducing the intermediate lists

The [implementation](../src/pnp_lab/event_projection.py) uses canonical RREFs for exact equality, removes flats contained in a larger forbidden flat, and merges parallel binary cosets. In detail, for two distinct right sides b,c on the same independent normal rows A, their union is exactly the solutions of Ax=b+t(b+c) for some bit t. At any row p with b_p≠c_p, solve for t and eliminate that row. This yields one affine flat of rank one less, with exactly the combined point set. Unlike a generic affine-hull approximation this step is exact because the field has two elements. Repeat until no such pair remains. Common flats of the two slices can likewise be factored out before multiplying them.

For a specified bit, at most the product of the two remaining slice-list lengths many cross intersections are tried. A greedy alternative evaluates this bound for each remaining bit and takes the smallest one, breaking ties deterministically. A pair budget stops *before* an unaffordable layer with UNKNOWN; it does not cap normalization, greedy order selection, memory or lifting. All arithmetic uses explicitly represented binary masks. Per-layer bit cost is polynomial in its input and intermediate list lengths; there is no polynomial bound here on those lengths for every input/order.

## A limitation independent of how parallel cosets are merged

Take selector bits z_i and pairs a_i,b_i for i=1,...,k, k≥2. Require odd selector parity and forbid z_i=1 together with a_i=0 or with b_i=0. Encode the bad even-parity hyperplane as its two halves at a_1=0 and a_1=1 if *all* inputs should have codimension two. This is a linear number of explicit flats on 3k bits (polynomially many bits even in dense masks).

After eliminating all the z bits first, the forbidden set on the remaining pairs is **exactly** the Cartesian product of k copies of {00,01,10}. Indeed, if some pair equals 11, choose that selector alone; if no such pair exists every selector must be zero. No early full-coverage or empty-union shortcut ends this computation before the indicated cut: both extendible and unextendible remaining points exist there.

The product has 3^k points. The projection of any single affine flat contained in it to a two-bit block is an affine subset of the three allowed points, so has at most two elements. That flat therefore contains at most 2^k points. **Any exact representation of the projected forbidden set as a union of affine flats needs at least ceil((3/2)^k) flat entries.** This lower bound holds even if a better union simplifier is used; the stated group of bits must be eliminated before the other bits. It is not a theorem about every elimination order or every possible representation. In fact the displayed product itself is a short different representation, and the existence problem on this family is easy.

The [experiment](../results/event_projection.json) checks k=2..8, measures the forced and alternate orders on the same inputs, and also projects the old three-variable cube and its satisfiable neighbor via three explicit source encodings. On the compact cube the auxiliary-first source decision takes 16 cross-slice intersections. This and the 36 probes on the older solver's 19-bit kernel refer to different representations. The proof, not extrapolation of a timing curve, establishes the general lower bound.
