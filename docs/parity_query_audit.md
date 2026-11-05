# An explicit parity-query certificate and a polynomial positive control

This note fixes a checkable meaning of **querying a parity of many original
variables**. It also implements a positive control: from any inconsistent
collection of complete parity blocks already present in a CNF, a finder
constructs a parity tree with at most as many leaves as the input has clauses.
Arbitrary extra clauses may be present. Recognizing no such contradiction
returns `UNKNOWN`; it does not decide the remaining CNF.

This is an elementary implementation of a known easy class for parity
branching, with an explicit raw-clause leaf and input-cost accounting.
[Part–Tzameret, *Resolution with Counting: Dag-Like Lower Bounds and Different
Moduli*, Proposition 27 and Theorem 28, printed p. 29](https://www.doc.ic.ac.uk/~itzamere/Res-Lin-Two.pdf)
give polynomial tree-like resolution-over-linear-equations upper bounds for
CNF encodings of inconsistent linear systems and, in particular, matching-
characteristic Tseitin formulas. No priority is claimed for this phenomenon
or the balanced search below. The [literature note](parity_query_prior_work.md)
separates these known upper bounds from the relevant parity-tree lower bounds.

## 1. Exact certificate model

An internal node asks

\[
                  \bigoplus_{v\in S}x_v\in\{0,1\},
\]

where $S$ is a nonempty explicitly listed set of **original** variable IDs.
Both possible answers have children. A leaf cites a single original CNF
clause, and the affine equations on the root-to-leaf path must force every
literal in that clause false. A second permitted leaf declares an
inconsistent path, which must actually be inconsistent over $\mathbb F_2$.
Such a leaf is unreachable by every Boolean assignment. An empty original
clause can be cited without any queries.

The certificate is a flat list of nodes with a root at index zero. Children
have strictly larger indices, each non-root node has exactly one parent,
and all nodes are reached. Sharing a child, cycles, orphan nodes, missing
branches, unrecognized fields, repeated/unsorted query coordinates, and
Boolean values masquerading as integer IDs are rejected. This particular
format records a tree, not a branching program with shared subproofs.

The checker in [the implementation](../src/pnp_lab/parity_query.py) builds a
sparse Gaussian basis from the **questions and their answers only**. For a
consistent path and a candidate leaf literal, it reduces that variable's
unit row to decide whether its falsifying value is forced. It does not
assume any recognized equation from the formula or consult the finder.
The finder separately uses dense integer bitsets on compressed variable
indices. No SAT oracle, unchecked arithmetic premise, extension coordinate,
or hidden case assumption is part of the leaf rule.

**Soundness proof.** Fix any Boolean input word and follow the unique child
matching each query's actual parity. The finite tree ends at a leaf. Its
path equations have that word as a solution, so it cannot be an inconsistent
leaf. In a clause leaf those equations force every cited literal false,
so this word falsifies an original clause. This holds for every word, proving
that a successfully checked certificate refutes the original CNF. This is a
paper argument; the Python checker itself is not formally verified.

## 2. Recognizing the positive class directly from raw clauses

Normalize one clause by deleting repeated literals; ignore tautologies.
Group its distinct variable support $S$ and its unique falsifying word.
For each parity $b$, check whether the group contains all distinct words
on $S$ whose parity is $1-b$. Such a group is a complete parity block,
and its original clauses entail

\[
                     \bigoplus_{v\in S}x_v=b.               \tag{1}
\]

Completeness is checked by the number of distinct forbidden words:
$2^{|S|-1}$. No absent words or arbitrary variable subsets are enumerated.
Computing the binary integer $2^{|S|-1}$ uses $|S|$ bits, not that many
steps. All the words counted were explicitly represented by input clauses.
A repeated clause supplies one pattern, not several. Both parities can be
complete on the same support; their two pattern sets are disjoint. A raw
empty clause is handled first.

Gaussian elimination on the recognized equations either finds a subset
$I$ whose row masks XOR to zero and whose right sides XOR to one, or
reports no contradiction. It uses bitsets indexed by the $K$ variable IDs
actually occurring in the formula, not an array extending to the largest
numerical ID. Extraneous nonlinear clauses are allowed and need not enter
this subsystem. No contradiction in this relaxation means `UNKNOWN`, even
when the full formula might be unsatisfiable for another reason.

## 3. Convert the inconsistent subset to a small raw-clause tree

For a recognized equation $a_i\cdot x=b_i$ over $\mathbb F_2$, define its
discrepancy $d_i(x)=a_i\cdot x+b_i$. Initially,

\[
                         \bigoplus_{i\in I}d_i(x)=1          \tag{2}
\]

for every input word. Maintain a nonempty subset whose discrepancy XOR is
one under the equations on the current path. Split that subset into two
nearly equal sets $A,B$. Query the parity with mask $\bigoplus_{i\in A}a_i$.
The answer, together with the known constant $\bigoplus_{i\in A}b_i$,
tells us whether $A$ has discrepancy one. If so recurse into $A$;
otherwise recurse into $B$, which must have discrepancy one by (2).
If the query mask cancels to zero, the answer is already constant and
the correct part is selected without introducing a node.

After at most $\lceil\log_2|I|\rceil$ such queries, the path entails that
one equation (1) is violated. Let its support have size $k$. Query any
$k-1$ of its variables individually. Its opposite parity fixes the last
one. The resulting full word on this support has precisely one of the
forbidden patterns recognized from an original clause. Cite that clause.
This produces $2^{k-1}$ leaves for this block; for $k=1$ no additional
question is needed.

**Output bound.** Distinct selected blocks use disjoint sets of retained
original pattern IDs: different scopes use different clauses, and the two
possible blocks on the same scope use opposite forbidden parities. If
the raw CNF has $m$ clauses, the final number of leaves is therefore at most

\[
       \sum_{i\in I}2^{|S_i|-1}\le m.                       \tag{3}
\]

Every internal node has two children, so there are at most $2m-1$ nodes.
The depth is at most
$\lceil\log_2|I|\rceil+\max_{i\in I}(|S_i|-1)$.
This is a bound on these constructed trees, not a guarantee that every
UNSAT CNF has such blocks. All raw-clause leaves are independently checked
after construction; the recognized equations are not included as trusted
premises in the certificate.

**Bit cost.** Let $N$ be the full encoded input size, $K$ the number of used
variables, and $n$ the numerical variable bound. Grouping and counting scan
the input; at most two rows are recognized per occurring support. Gaussian
elimination has at most $K$ variable pivots and uses polynomial-size reason
bitsets. The balanced construction explicitly writes at most $m-1$ queries
of support at most $K$. Its certificate description takes

\[
 O\!\left(m\,[K\log(n+2)+\log(m+2)]\right)
\]

bits, including variable IDs and node/clause addresses. Discovery, tree
construction, and checking are all polynomial in the explicit input and
output bit length. This includes parsing large variable IDs. Sparse sets
in the checker and compressed bitsets in the finder prevent a numerical ID
such as $10^{10}$ from becoming an allocation of that many columns.
The full Boolean-cube replay used only in the finite experiment is
exponential; it is not part of the finder or certificate checker.

## 4. Finite audit and limits

The [deterministic experiment](../experiments/parity_query.py) records:

| Control | Check performed |
|---|---|
| Signed and permuted $K_4$ and triangular-prism Tseitin CNFs | Two UNSAT trees are found using only raw CNF. Their SAT siblings retain independently verified original satisfying words and return `UNKNOWN` |
| Three overlapping parity blocks on four variables, plus duplicate clauses/literals, a tautology, and an extra nonlinear clause | A third refutation shows that the discovery argument does not require a graph-star decomposition |
| Opposite complete parity blocks on the same two-variable support | Both blocks can be selected without counting a pattern twice |
| All words of all four UNSAT controls | 596 independent executions of the query tree end at an actually falsified raw clause, without Gaussian elimination |
| Comparison with the earlier solver | Both graph contradictions were already refuted by the existing $\mathbb F_2$ affine-sum implementation |

The largest recorded query has support five and the largest tree has
47 nodes. These are small semantic controls, not expanding graph samples
and not empirical evidence for an asymptotic lower bound. The bounded-degree
Tseitin construction gives a useful conceptual distinction: wide parity
queries can locate a violated vertex equation by balanced search, while
ordinary raw-clause variable trees can be exponentially larger on suitable
expanders. The stronger affine-terminal variable trees from phase 18 already
solve these matching-characteristic formulas at their root, so this is
**not** a separation from that model.

The [unit tests](../tests/test_parity_query.py) exercise incomplete blocks,
consistent relaxations, raw-input rebinding, an actual inconsistent path,
18 malformed-certificate variants, arbitrary extra clauses, empty clauses,
and sparse large labels. No rejected mutation is treated as a mathematical
lower bound. There is no general SAT decision algorithm or P vs NP
resolution here.

```bash
PYTHONPATH=src python -m unittest discover -s tests -p 'test_parity_query.py' -v
PYTHONPATH=src python experiments/parity_query.py --out-dir reproduced/parity-query
```
