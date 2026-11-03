# Two options versus three in XOR support selection

Given finite, explicitly listed sets of bit masks \(S_i\) and a target \(t\),
choose one mask \(s_i\in S_i\) from each group so that \(\bigoplus_i s_i=t\).
This is a decision problem; repeated copies of an option do not change the
answer. Let **support size** mean the number of distinct options in a group,
and **mask weight** mean the number of 1 bits in one option. They are different
restrictions.

| Restriction | Decision result | Reason |
|---|---|---|
| At most two options per group, arbitrary mask weights | In P | One binary selector per pair; Gaussian elimination |
| Every mask has weight at most one, arbitrary support sizes | In P | Reduction to general-graph perfect matching |
| At most three options per group **and** mask weight at most two | NP-complete | 3SAT reduction, bounded occurrences, and paired bit translations |

The NP-hard instances in the last row have target zero, with each coordinate
touched by at most two groups. Two constructors implement the direct three-option reduction and its
weight-two refinement. Section 4 gives the matching reduction separately. These are statements about a
particular input language, with no claim of novelty or separation of P and
NP. For context on earlier satisfiability dichotomies see Schaefer,
[*The complexity of satisfiability problems* (STOC 1978)](https://doi.org/10.1145/800133.804350).
We give the reductions explicitly; we do not infer this simultaneous set of
restrictions merely by citing a dichotomy for a different language.

## 1. At most two options: a linear system

Reject an empty group. For each nonempty group choose an anchor \(a_i\);
if the group also contains \(b_i\), its possible values are exactly
\(a_i + y_i(a_i+b_i)\) for \(y_i\in\mathbb F_2\). Singletons just contribute
their anchors. Existence is the linear-system question

\[
  \sum_{i:\,|S_i|=2} y_i(a_i+b_i)=t+\sum_i a_i.
\]

Gaussian elimination decides it and supplies the choices in polynomial bit
time. With no groups it accepts exactly target zero. The affine-absorption
phase of the [frontier algorithm](affine_frontier.md) implements this case
without enumerating a residual frontier.

## 2. Three options suffice to encode general 3SAT

Use a signed 3-CNF \(F\) on an explicit scope of \(n\) variables, with \(m\)
clauses of width at most three and \(\ell\) literal **occurrences**. Write
\(V_j,C_j\) for unit masks on two fresh coordinates for occurrence \(j\).
The intended bits are the *original variable value* and *this occurrence
was chosen as its clause's witness*. Even repeated copies of the same
literal receive distinct coordinates.

Build three types of support on these \(2\ell\) coordinates:

| Group | Options | What the choice records |
|---|---|---|
| One per original variable \(x\) | \(0\), or the mask with all \(V_j\) for occurrences of \(x\) | Broadcast the same bit to every occurrence; unused variables give the singleton zero |
| One per clause \(D\) | One unit mask \(C_j\) for each occurrence \(j\) in \(D\) | Choose exactly one literal witness |
| One per occurrence \(j\) | Positive: \(\{0,V_j,V_j+C_j\}\); negative: \(\{0,V_j,C_j\}\) | Allow precisely the pairs satisfying “chosen implies this signed literal is true” |

Here additions of masks are XOR. The target is zero. Coordinate \(V_j\)
occurs only in its variable and occurrence groups; \(C_j\) occurs only in
its clause and occurrence groups. At each coordinate XOR-to-zero therefore
means *agreement of the two transmitted bits*. Nonlinearity lies inside
the three-element local choices.

**Correctness and witness maps.** From a source model, choose the indicated
broadcasts and select a true occurrence in every clause. The corresponding
pair of bits belongs to each occurrence group, and both copies of every bit
cancel. Conversely, a zero-sum choice selects a single witness per clause.
Agreement at its two coordinates implies that this literal is true under the
broadcast assignment. Hence every clause is true. Unused source variables
may be set false. An empty clause yields an empty support and correctly makes
the target unsatisfiable; an empty formula yields only unused broadcasts.

There are \(n+m+\ell\) groups, each with at most three options. The total bit
length is polynomial even with dense integers: \(O((n+m+\ell)(\ell+1))\)
mask bits, plus polynomially many bits for delimiters, indices and the
explicit input names. No operation on an exponentially long string is
hidden in a constant-cost integer step. The target decision problem belongs
to NP: one option index per group suffices, and all memberships and the XOR
can be checked in polynomial bit time. Standard NP-completeness of 3SAT
([Cook's problem description](https://www.claymath.org/wp-content/uploads/2022/06/pvsnp.pdf))
and the construction prove NP-completeness at support size three.

**This does not preserve model counts.** For one clause \((a\lor b\lor c)\)
on three distinct positive variables there are seven source models. Each
model has as many choices of clause witness as true literals, hence the
target has \(\sum_{k=1}^3 k\binom{3}{k}=12\) accepting choice tuples.
This number is specific to the selector construction; the earlier
[constant-block bridge](constant_block_bridge.md) used different helpers.
Only existence is needed for the P=NP criterion.

## 3. Joint refinement: weight at most two, still three options

The direct translation's only potentially heavy masks are variable
broadcasts. The implemented weight-two constructor replaces a broadcast
by copies linked in a cycle, using no clause padding or global auxiliary
assignment. Keep the same value and clause-selector ports for each of the
\(\ell\) occurrences. If variable \(x\) occurs \(k\ge2\) times, connect its
\(k\) occurrences in cyclic order by \(k\) **distinct** equality ports. With
two occurrences this means two different ports between the same neighbors.
A singleton occurrence needs no cycle.

For occurrence \(j\), provide a binary copy group in place of the global
broadcast. Its **false** option is the single value mask \(V_j\); its
**true** option is the pair of incident equality ports (zero for a
singleton). Translate every option of the occurrence implication group
in Section 2 by XOR with \(V_j\). Clause groups still choose one of their
unit witness ports. The target remains zero.

Each equality port is used exactly by the adjacent pair of copy groups,
and only in their true options. Even parity on those ports therefore
makes all copies of each source variable agree. At \(V_j\) the copy
transmits the *complement* of its bit; translating the implication group
makes its transmitted value the same complement. Agreement at \(C_j\)
still selects one true literal per clause. This proves both directions as
in Section 2. In particular the complement on a value port is independent
of whether its original literal was negated.

There are \(2\ell+m\) groups (copies, then clause selectors, then local
implications) and at most \(3\ell\) coordinates: \(2\ell\) original ports
plus one equality port per occurrence of a variable that occurs at least
twice. Every port belongs to exactly two groups. Each option has at most
two 1 bits, and every support has at most three options. This proves the
joint NP-completeness statement in the opening table; the hardness
does not depend on a dense broadcast. The bound concerns a single option's
weight, not the number of distinct coordinates used by its whole group.

**Alternative via the earlier splitter.** A second proof is to precompose
Section 2 with the [constant-block bridge's](constant_block_bridge.md)
occurrence splitter: pad nonempty clauses before copying, then enforce
agreement with a padded directed implication cycle. Each copy occurs at
most four times in the intermediate formula `expanded_cnf`: once in a
source clause, once in an outgoing implication and twice in an incoming
implication. Hence the unmodified Section 2 construction on this formula
already gives weight at most four. To get two, take any broadcast on \(d\le4\)
ports, XOR a fixed mask marking \(\lfloor d/2\rfloor\) of its ports into
*every option* of this broadcast, and XOR each translated port \(V_j\) into
every option of its corresponding implication group. Each translation bit
occurs twice, so the global sum is unchanged for every choice tuple; the
transformation is its own inverse. The broadcast now selects one of two
complementary halves, each of weight at most two. Each occurrence group
still uses only two coordinates. This alternative is an elementary
composition, distinct from the implemented equality-port cycle above.

## 4. Weight at most one: an ordinary matching problem

Suppose each option is zero or a unit mask. For each group we must select a
row (coordinate) allowed by its support, so that each row \(r\) is selected
\(b_r=t_r\pmod 2\) times. Represent the zero option by an extra row \(*\).
Every group now selects exactly one row; require
\(b_* = (g-\sum_r b_r)\bmod 2\), where \(g\) is the number of groups. This
adds no constraint to feasible original choices: their dummy count equals
\(g\) minus the number of real row choices. Include rows requested by the
target even if they occur in no support.

Build an undirected graph. Each group has a vertex. For every allowed choice
of row \(r\) by group \(i\), make a separate port vertex adjacent to that
group. For each row collect its \(d_r\) ports; add one **internal-only**
padding vertex iff \(d_r\not\equiv b_r\pmod 2\). Make this row's port and
padding vertices a clique, with no edges between row cliques.

In a perfect matching, each group consumes exactly one allowed port. If
\(k_r\) ports have been consumed at a row, its remaining clique has an even
number of vertices iff \(k_r\equiv b_r\pmod 2\), by construction of the
padding. Every even clique, including an empty one, has a perfect matching.
Thus a selection of row choices extends to a perfect matching exactly when
all parities hold. Reading the group-port edges of any perfect matching gives
original choices, with the dummy mapped back to zero. This covers an empty
support (an isolated group vertex), impossible target rows (an isolated
padding vertex), and zero groups.

The number of vertices is linear in the explicitly listed incidences, groups
and considered rows, and even the explicit clique edges are polynomially
many. General-graph maximum matching, hence perfect matching, is computable
in deterministic polynomial time by Edmonds' algorithm; see [*Paths, Trees,
and Flowers* (1965)](https://doi.org/10.4153/CJM-1965-045-4). This polynomial
upper bound has a dedicated implementation in [unit_matching.py](../src/pnp_lab/unit_matching.py):
`reduce_unit_supports` constructs the graph, `decide_unit_supports` runs an
unweighted blossom solver, and `lift_unit_choices` / `project_unit_matching`
check witnesses in both directions. The frontier algorithm does not
automatically select this backend. The Python blossom implementation is not
claimed to be formally verified.

### Why a local matching gadget is not automatic at weight two

When the target is zero and each coordinate joins exactly two groups, the
two occurrences of a bit are constrained to agree. The resulting system is
a Boolean *edge CSP*: groups are vertices, coordinates are edges, and the
allowed masks are local bit tuples. Kazda, Kolmogorov and Rolínek give a
polynomial algorithm for such systems when every local relation is an even
delta-matroid ([paper and precise scope](https://arxiv.org/abs/1602.03124)).
Small support size or small mask weight alone does not imply that hypothesis.

For example, a translated four-port broadcast in Section 3 has feasible
port sets exactly `{1,2}` and `{3,4}`. Suppose a graph with four terminals
realized this relation by admitting a perfect matching after deleting the
selected terminals. Overlay the perfect matchings for the two feasible
deletions, treating shared edges as doubled. Each terminal is on exactly
one matching and hence ends an alternating path; every matched internal
vertex has degree two. Toggle the path starting at terminal 1 in the first
matching. Its other endpoint is one of 2, 3, 4. This gives another perfect
matching after toggling precisely these two terminal deletions. None of the
three resulting deletion sets is allowed, a contradiction. This excludes
only an independent, one-terminal-per-coordinate perfect-matching gadget
with this exact deletion semantics. It does not exclude nonlocal or other
reductions to matching, or algorithms that solve the entire SAT instance
by other means.

## 5. API and scope

[`three_cnf_to_ternary_supports`](../src/pnp_lab/ternary_support.py) builds
the direct, unshifted encoding. The result exposes the original formula
and scope, `supports`, `rhs`, `clause_occurrences` (zero-based identifiers),
and `variable_masks`. Its `lift_witness` maps a source assignment to a
choice tuple; `project_witness` checks an accepting tuple before recovering
a source assignment. `three_cnf_to_weight_two_supports` builds the equality-port
version, with its own lift/project maps and the direct encoding as `.direct`.
`decide_ternary_reduction` calls the exact support decider on either encoding,
returning a source witness on SAT. An exhausted residual search
budget does not justify UNSAT.

This smaller alphabet is a different reduction image from the earlier
five-signature star blocks; their all-orders grid bound does not by itself
transfer to the new encoding. [The integrated solver](../src/pnp_lab/support_solver.py) selects Gaussian elimination for binary supports, then matching for unit weights, otherwise the explicit frontier. The construction sharpens the *generic* support-selection
target: a uniform worst-case polynomial decision algorithm on all instances
in the three-option, weight-two image would imply P=NP. The matching and
linear-algebra cases explain what can already be done in polynomial time.
They do not settle the next case, and NP-completeness by itself gives no
superpolynomial time lower bound.
