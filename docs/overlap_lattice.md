# Counting outside a union of affine error sets

Let a parameter assignment be an `n`-bit vector `x`. A forbidden event is the
set of assignments satisfying **every** equation `(a, b)` in its input list,
with `parity(a & x) = b`. We seek an assignment in none of the events.
The [solver](../src/pnp_lab/overlap_lattice.py) returns the exact number of
surviving parameter vectors and one checked original vector, or `UNKNOWN`
if it cannot complete the requested count within the explicit budgets. An
empty conjunction forbids the whole space; inconsistent equations define an
empty event. Multiple parameter witnesses may project to the same source-CNF
model: the number is not automatically a count of source models.

## Why signed intersections suffice

For an affine set `A`, denote its indicator by `[A]`. Begin with coefficient
one on the full space. On reading the next forbidden event `E`, multiply the
represented function by `1-[E]`. Each old term `c[A]` remains and contributes
`-c[A∩E]`. Empty intersections contribute nothing. The implementation reduces
the combined augmented equations over GF(2) to canonical reduced row echelon
form (RREF), so identical affine intersections become the **same dictionary
key**. Their coefficients add, and an exact zero disappears. Terms for one
step are produced only from the previous dictionary, never from one another.
After any prefix this signed sum equals its complement indicator *pointwise*,
not just in expectation. This follows immediately by induction and
`[A][E]=[A∩E]`.

A consistent rank-`r` term in dimension `d` has `2^(d-r)` points. Therefore
the weighted sum of these sizes is the exact surviving mass. The intermediate
indicator takes only values zero and one even though individual coefficients
can have either sign and magnitude greater than one. Zero surviving mass
proves coverage of that component. For a witness, intersect the **final**
dictionary with a trial coordinate value `0` and compute its mass. Keep that
half if it is nonempty, otherwise keep the `1` half. The two halves partition
the current nonempty survivor set. Repeating at most `d` times recovers a
point without recomputing inclusion–exclusion from scratch. The final returned
point is also checked directly against every raw, unnormalized input event.

This is an elementary application of inclusion–exclusion on affine
intersections, not a claim to invent intersection-poset counting. For related
background, Athanasiadis, [*Characteristic Polynomials of Subspace Arrangements
and Finite Fields* (1996)](https://doi.org/10.1006/aima.1996.0059), relates
characteristic polynomials of arrangements defined over the integers to counts
over sufficiently large prime fields. Here the equations are **already over
GF(2)**; the direct indicator proof above requires no change-of-field theorem.

## Restrictions, independent factors and linear separators

Before the signed calculation, discard impossible and duplicate events. If
one event lies inside another, the smaller set is redundant for the union;
RREF implication checks this containment including the affine constants.
Within each slice of the parameter space, reduce the event equations modulo
the slice equations. A forbidden hyperplane `a·x=b` forces every survivor
to satisfy `a·x=1-b`. Collect such requirements, reduce again, and repeat.
Every nonterminal successful round increases the rank of the required system.
A contradiction among forced rows or a forbidden event containing the full
remaining slice closes that slice with count zero.

Choose a basis of all surviving **linear observation masks** in the free
coordinates. Express every row mask in that basis. Join basis indices if one
event refers to both, whether through one row or through different rows in
its conjunction. Different resulting components use disjoint blocks of
independent observations. Because independent linear forms attain every
joint assignment with equally many preimages, it is sound to multiply their
complement counts, then multiply once by `2^(n - required_rank - observation_rank)`
for unobserved free directions. A solution of the original required
equations together with the selected observation bits lifts the component
witnesses. This detects factors even when their masks overlap in the original
coordinate representation; it is not a general SAT decomposition oracle.

`condition_on` optionally supplies a list of parity masks. Enumerate all
assignments to a basis of their span, **sum** the counts from these disjoint
slices, and keep a witness from any nonempty one. No independence is assumed
between these observations and the remaining event masks. The dimension of
the separator is a cost: `s` independent masks require up to `2^s` slices.
An arrangement with a small separator can simplify dramatically. For example,
when clause-selector coordinates interact only through source variables,
fixing those source bits can expose independent per-clause systems. Slicing
on *every* original SAT variable merely reintroduces exponential enumeration.

`max_intersections` is global across all slices and components. It counts
attempted `A∩E` operations in the signed updates, including empty intersections.
`max_slices` separately bounds the number of enumerated linear slices (default
256; `None` opts out). Neither budget caps polynomial preprocessing,
dictionary operations, bit arithmetic, or witness recovery. Proven constant
cases can finish without either. If either budget interrupts remaining
required work, the exact-count API returns `UNKNOWN` with no purported count
or witness; in particular it does not label a partly searched input UNSAT.
`peak_terms` counts entries in a **completed component layer**, not temporary
storage or memory in bytes. `work_samples` stores per-block diagnostics from
at most the first 16 slices; the aggregate counters are not sampled.

## Quantitative positive case and a connected barrier

**Many equal intersections.** In `d≥3` dimensions forbid each of the `d`
coordinate axes `{0,e_i}` by setting every other coordinate to zero. The
normal spaces of these events are connected in the factorization above.
Every intersection of at least two axes is the origin. After `j≥2` axes the
indicator is the full-space term, minus each axis, plus `j-1` times the
origin. Thus peak support is `d+2`, survivors number `2^d-d-1`, and the
algorithm tries `(d²+3d-4)/2` update intersections. Ordinary subset expansion
has `2^d` subsets. This is an all-size calculation, not a general bound.

**Connected path with exponentially many distinct nonzero terms.** Forbid
`x_i=x_(i+1)=0` on each edge of an `n`-vertex path. These codimension-two
flats have distinct normals, none contains another, no hyperplane unit is
available, and the event spans form one connected component. Consider the
induced matching `(1,2),(4,5),(7,8),…`, taking `floor(n/3)` edges. Each subset
of those edges fixes a distinct union of endpoints to zero. No other path
edge is fully contained in that union: the intervening unselected vertex
breaks every extra adjacency. Therefore each resulting intersection is
generated by **exactly one subset of all path events**; it has final coefficient
`+1` or `-1` and cannot vanish by coalescing. The final dictionary, independent
of processing order, has at least `2^floor(n/3)` terms without an optional
separator. The all-ones model prevents early universal-coverage termination.
The bit length of these dense masks is polynomial in `n`, so this explicit
algorithm has a superpolynomial time/space family, even after the implemented
factorization. The underlying no-adjacent-zeros problem itself is easy by a
two-state path recurrence. This is not a lower bound against other symbolic
representations, variable elimination, SAT decision, or P versus NP.

For arbitrary inputs let `L_j` be the number of nonzero signed terms before
event `j` in a component. The update probe count is at most `Σ_j L_j` per
component, summed over slices. An intersection, its canonicalization, key
comparison and point count cost polynomially many bit operations in explicit
dimension and input size per term (time bounds must also account for dictionary
management, e.g. a deterministic ordered map). Coefficient magnitudes are at
most `2^h` after `h` events by the ordinary subset expansion; counts need only
`O(n+h)` bits. Witness conditioning makes at most `2d` passes over at most the
final number of terms in its component; restriction never increases that
number. Giving `n` only as a binary integer does not make writing a general
`2^n`-sized count constant cost: its representation needs `n+1` *bits*. None
of these bounds controls `L_j` by a polynomial for all inputs.

## Fixed-order overlap cardinalities do not decide coverage

For `N≥2` introduce source bits `x_1,…,x_N` and one bit `z`. For each `i` and
`s∈{0,1}` forbid the event `(x_i=0, z=s)`. Finally, for each `s` also forbid
`(x_1 XOR … XOR x_N=b, z=s)`. Every event has codimension two. Compare `b=0`
and `b=1` on these identically labelled lists. Every subfamily of **at most
N** events has the same intersection size in both arrangements. Mixed values
of `z` give an empty intersection; with one fixed value of `z`, the selected
row normals on the `x` bits are at most `N` distinct elements from the single
circuit `{e_1,…,e_N,e_1+⋯+e_N}`. Each proper subset is independent, so every
choice of affine constants produces the same intersection size. Yet avoiding
the first events forces all `x_i=1`. If `b=N mod 2` the last events cover the
two remaining `z`-points; otherwise both survive. This rules out universally
deciding coverage from bounded-order labelled overlap **cardinalities alone**.
It does not rule out recognizing the circuit, reading the equations, merging
adjacent affine events, or efficiently using some high-order information.

[Tests](../tests/test_overlap_lattice.py) include independent direct point
enumeration, coordinate changes, saturation of the two budgets, witness lifts,
and finite instances of the preceding all-size arguments.

## Reproducible measurements

[`experiments/overlap_lattice.py`](../experiments/overlap_lattice.py) produces
[`results/overlap_lattice.json`](../results/overlap_lattice.json). On 64 axes
in 64 dimensions it finds `2^64-65` survivors with 66 signed entries at peak
and 2,142 signed-update probes. On an 18-vertex path it finds 6,765 survivors
with 9,938 peak entries and 14,287 probes. The latter count agrees with the
independent Fibonacci recurrence. Across `N=2,3,4,5` the experiment directly
compares 2,083 labelled intersection cardinalities in the bounded-order pair
above, as well as enumerating the tiny complements themselves.

For the eight clauses forbidding each original assignment on `x,y,z`, fixing
those three observed source bits creates eight slices. The strict 19-bit
selector encoding closes all eight with count zero: in each slice there is
a false clause whose selector requirements are inconsistent. Removing the
first clause leaves one source model; the three actual encodings yield
**24 strict, 32 relaxed, and 4 compact parameter assignments** projecting
to it. In strict mode, the one model has one, two and three true literals
in three, three and one of the remaining clauses, respectively, hence
`1^3 * 2^3 * 3 = 24` choices. Relaxed odd selectors also allow the all-ones
choice in the all-true clause, giving 32. In the compact construction the
two clauses with their first two literals true each leave the private bit
free, giving 4. These checks separate exact *parameter* counting from
preservation of SAT witnesses; fixing the source bits is not a polynomial
algorithm for arbitrary numbers of source variables.
