# Many incomparable residuals at a single cut of one 3-CNF

This strengthens the [robust two-graph obstruction](robust_ceiling.md)
in one respect: a *single* polynomial-size raw 3-CNF restriction tree
contains a superpolynomial collection of mutually incomparable branches
at the same depth. For all sufficiently large even q, the collection
has at least exp(Ω(q log q)) members. Between any two distinct selected
members, neither direction admits a signed-literal/constant transport with
polynomial-size ordinary-resolution justifications of every nontrivial
pulled target clause, measured in the original input length. In fact the
resolution lower bound is exponential in q, not just the nonexistence of
a fixed-width or fixed-lookahead certificate.

**This is a pairwise obstruction inside the full restriction tree.**
The formula as constructed is itself trivially SAT. The algorithm need
not reach the cut, materialize the selected residuals, or limit its
pruning to pairs in that collection. A third type of residual can
dominate many of them. No lower bound on its actual live frontier, on all
variable orders, or on SAT decision time is asserted.

## One common input

Use q disjoint triples of bits (“ports”). At the first vertex require odd
parity on its three ports, and at the remaining vertices require even
parity, four raw 3-clauses each. For **each** unordered pair of distinct
ports a,b add a fresh tag s and the clauses
`(¬s ∨ ¬a ∨ b), (¬s ∨ a ∨ ¬b)`. The complete formula has
T=binom(3q,2) tags, T+3q variables and 2T+4q clauses. It is ordinary
width-three CNF with O(q² log q) bits under literal-index encoding.
An all-zero tag vector disables every wire, so each star can choose its
own parity model independently.

Fix **all** T tags in a single restriction-tree cut. A selected branch
enables exactly a perfect matching P of the 3q ports; its residual R(P)
consists of the original stars and 3q binary clauses enforcing the
matched equalities. Any labelled simple cubic graph on the q vertices
can be realized: assign its three incidences at each vertex bijectively
to the three local ports, and match the two incidences of each graph
edge. We select only matchings with the graph properties below. The other
tag assignments still exist; this construction does not require a
promise checker for them.

## Why extra port bits do not circumvent the obstruction

Let H(P) be the naked Tseitin formula with **one bit per matched edge**.
Identifying the two source endpoints of every matched edge retracts R(P)
to H(P): every source wire becomes a tautology, and each star becomes the
corresponding naked star. This is a clausewise restriction/substitution
of ordinary resolution with at most one new line per projected inference,
as shown in [the width-transfer proof](width_transfer.md).

In the other direction, fix one named representative port per matched edge
of a *target* matching Q. Every naked target star clause is derivable on
these representatives from R(Q) in at most three resolutions besides the
axioms. To replace a nonrepresentative literal l by its representative
l' with the same polarity, resolve the current clause against the wire's
binary clause (¬l ∨ l'). Its width stays at most three. This derivation
is necessary: the two endpoints of a target wire may have *different*
images under a proposed transport before its wire clauses are justified.
Simply assuming they have the same image would not be sound.

Suppose a transport from R(P) to R(Q) has an ordinary-resolution basis
of total DAG length S for its nontrue pulled clauses. Append the above
short target derivations, transported through its literal/constant map.
Then retract the resulting source proofs onto H(P). The composition takes
each representative target bit to **one signed naked source literal or a
constant**. Unused tag coordinates in the common raw scope may be set to
constants during the retraction. We obtain proofs, of total size
S+O(q) up to a constant factor, of subclauses of the pulled H(Q) axioms
whenever they are nontrue. For the robust cubic graphs in
[the pair theorem](robust_ceiling.md), any such pulled width-at-most-three
clause that is neither true nor contains an original H(P) clause costs
exp(Ω(q)) resolution lines. If every pull is cheap, the result is thus an
ordinary direct transport. Equal clause counts and widths, minimal
unsatisfiability and equal active-variable counts force this to be a
signed permutation isomorphism of the two naked clause sets, hence an
isomorphism of the graphs. Choose pairwise nonisomorphic graphs and
repeat the argument in either direction. All constants in the robust
lower bound can be chosen uniformly by fixing the expansion/girth
thresholds. In particular any fixed polynomial in the full O(q² log q)
input length is eventually too small.

## Counting the branches

For completeness, the needed class contains many nonisomorphic graphs,
not just two. In the uniform labelled simple cubic model, with probability
tending to 1 the second eigenvalue is <2.9 by [Bordenave's proof of
Friedman's theorem](https://arxiv.org/abs/1502.04482). Thus every vertex
set of size s≤q/2 has at least 0.05s outgoing edges (apply the Rayleigh
bound to its centered indicator). With probability bounded away from
zero there are no cycles of any length 3,...,61, by the fixed-length
short-cycle distribution of [McKay, Wormald and Wysocka](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v11i1r66).
The intersection therefore has a positive fraction for sufficiently large
even q; no independence with the spectral event is needed. A cut of at
most three edges has smaller side at most 60. That side induces a forest
by the girth property; on s vertices with c components its boundary in
a cubic graph has size s+2c. Consequently only singleton sides can have
such a cut. These properties suffice for the robust pair theorem.

An elementary lower bound on the number of labelled simple cubic graphs
avoids any graph enumeration oracle. Choose a labelled undirected Hamilton
cycle in (q−1)!/2 ways. Deterministically orient and start it, divide it
into two consecutive halves of m=q/2 vertices, and add a perfect matching
between the two halves disjoint from the cycle. At most two crossing cycle
edges need to be avoided, so at least m!−2(m−1)! matchings work. For a
fixed output graph, at most 3^q Hamilton cycles could have produced it:
choose at every vertex the unique incident edge omitted by the cycle;
the remaining edges are then determined. The matching is the complement
of that cycle. Thus the total number of labelled graphs is at least
`(q−1)!(m!−2(m−1)!)/(2·3^q)`. Only a fixed positive fraction is needed,
and quotienting by vertex labels costs at most q!. This still leaves
exp(Ω(q log q)) robust isomorphism types for the one common input.
No efficient recognition/enumeration of every selected type is needed
for the counting statement.

## Executable control

[The constructor](../src/pnp_lab/port_antichain.py) builds the same
465-variable, 910-clause formula for the 10-vertex Petersen graph and
pentagonal prism. Two distinct 435-tag words each restrict it to 70
clauses. [Tests](../tests/test_port_antichain.py) re-evaluate the actual
restricted literals, independently replay the representative-star
resolution proofs, and compare every pulled star to the naked input.
A 4-cycle distinguishes the two controls, and all proper non-singleton
cuts were checked to have size at least four. These finite cases test the
encoding, not the asymptotic high-girth or exponential-size bound.
