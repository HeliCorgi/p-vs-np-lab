# Can the recovered obstruction need a composite modulus?

Yes, even when every prime field admits a solution of the recovered *affine
equations*. This experiment isolates the arithmetic from the separate
[exponential ordinary-resolution comparison](feedback_separation.md). No
resolution lower bound is claimed for the carry example.

**Source relation.** Take a ring of incident variables $a_i$ and one common
bit $x$. Gate $i$ demands $a_i+x-a_{i+1}=c_i$, indices modulo $m$, with
each $c_i$ zero or one and total $q$. Each of its five forbidden Boolean
words supplies one proper ternary clause. Rotate the literal to be hidden
across the five clauses; each coordinate still appears in at least two start
ternaries. Use the [same 16-layer one-way wrapping](feedback_separation.md).
All helper variables are fresh. The solver receives only the scrambled CNF.
This is a new interface to the [earlier carry mechanism](global_integer_fixtures.md),
not a new number-theoretic obstruction.

**Exact arithmetic.** Summing the oriented gates cancels every counter,
leaving $mx=q$. Conversely, once $x$ is fixed to a solution in the domain
of coefficients, start with arbitrary $a_0$ and set
$a_{i+1}=a_i+x-c_i$; closure is precisely $mx=q$. In particular, for
$m=p^k$, $k\ge2$, $q=p^{k-1}$, no integer $x$ exists. Over any prime
field other than characteristic $p$, $m$ is invertible. In characteristic
$p$ both sides are zero. The field solutions need not be Boolean. The
$q=0$ sibling has the all-zero Boolean solution before scrambling and
extends to the shielded input.

**How the coefficient signs and modulus are actually found.** The
[one-column search](../src/pnp_lab/one_column_feedback.py) reconstructs each
group's 8-cell table from learned clauses. For a group with exactly three
allowed points it tests the four unit normals $(1,\pm1,\pm1)$ and keeps an
exact law constant on those points if one exists. In the carry gates the
three points are not collinear, so their normal is unique up to sign;
permuting and negating coordinates preserves this property. No carry labels
or modulus are supplied. Here exactly one column appears more than twice,
and every other column appears exactly twice. For a column with signed
entries $u,v\in\{-1,1\}$, the weights must satisfy $w_j=-uv\,w_i$.
Breadth-first propagation orients the rows. On this ring the orientation
constraints are connected and consistent; they recover the true sum up to
one global sign. A complemented common bit can replace the RHS by $m-q$.
The absolute coefficient of the remaining column gives the modulus.
The final proof consists of ordinary unit-weight integer rows and is
replayed against the learned clauses, whose paths are replayed against
the original input. Failed orientation or a divisible RHS is inconclusive.

For this construction the local scans and sparse incidence visits after
clause recovery are linear in $m$ up to sorting and identifier costs. The
partial integer sums have $O(\log(m+1))$ bits. For fixed shield depth
the raw formula and certificate have $O(m\log(m+1))$ bits in dense
encoding. Distinguish this mathematical construction with growing bit
capacity from the shipped checker, whose integer fields are capped at
512 bits, and from the general integer elimination fallback.

**Measured controls.** The [report](../results/feedback_prime_power.json)
recovers moduli 4, 8, 9 and 25 after signed relabeling. The modulus-25
case uses 4,151 raw variables and 8,125 clauses. On the modulus-4 case
the old integer procedure inspected 1,960 raw scopes and found zero rows.
The SAT sibling was checked with an actual original assignment. The general
feedback refuter returns UNKNOWN on this sibling: the constructive parity
solver covers parity blocks, not arbitrary affine equality blocks.

**What this does not buy.** The recovered ring has a single common bit
and cyclic counters. Guessing the common bit and propagating the counters
is already elementary on the unwrapped representation. The numerical size
of a detected modulus is not a proxy for SAT hardness, nor does prime-field
affine consistency exclude higher-degree polynomial reasoning. See the
[simulation and its first detecting digit](feedback_simulation.md) for the
stronger comparison.
