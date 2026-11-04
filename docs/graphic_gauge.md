# Exactly when a global change of XOR coordinates makes ternary supports matchable

The [phase-six selection problem](support_threshold.md) asks for one mask
from each independently listed support whose XOR is a prescribed target.
Unit-weight supports can be solved by ordinary perfect matching. The question
here is whether **one common invertible linear change of coordinates**, followed
by **one freely chosen translation per support**, can bring a wider instance
into that class. For supports of at most three distinct options, the answer
is equivalent to a classical graph-realization problem. There are actual
3SAT reduction images for which no such coordinates exist.

## 1. Use the differences, not just the listed weights

Work over \(\mathbb F_2^d\). Regard an empty support as immediate UNSAT;
remove repeated options within a support. For each nonempty support \(S_i\),
form one labelled column \(a+b\) for each unordered pair of distinct options.
Keep labels even when columns agree in different groups. Let \(D\) be this
matrix and \(W\) its column span. Its **column matroid** records which labelled
subsets are linearly independent. We call it *graphic* if there exists a
multigraph on those labelled edges in which independent sets are precisely
the forests. Equal nonzero columns can be represented by parallel edges.

**Theorem.** Suppose every support has at most three distinct options. There
are an invertible linear map \(L\) of the ambient space and translations
\(c_i\) such that every member of \(L(S_i)+c_i\) has Hamming weight zero or one
**if and only if** the column matroid of \(D\) is graphic.

**Forward implication.** Name a root vertex by the zero mask and each other
vertex by a different unit mask. A pair difference between low-weight options
is the reduced incidence vector of their edge: it has one bit for a root
edge, two otherwise. The translations cancel in every pair difference. An XOR
of edges vanishes exactly when every vertex has even degree in the selection;
the omitted root parity follows from all others. Thus the independent edge
sets are exactly forests. Invertible coordinate changes preserve all binary
dependencies.

**Reverse implication and how to construct a map.** Choose any basis of
labelled columns, of size \(r=\dim W\). In a graph realizing the matroid,
these edges form a spanning forest. Choose one root per connected component,
sending its vertex label to zero; give each other vertex its own unit label.
Equivalently, identify the chosen roots to make a connected graph. There are
exactly \(r\) nonroot vertices. Map each basis column to the reduced incidence
of its corresponding forest edge; these images are a basis of the reduced
incidence space. Every other column is an XOR of a unique subset of this
basis. In the graph, this subset is the unique forest path between the
nonbasis edge's endpoints: together they form its fundamental circuit.
Over the binary field the coefficients on a circuit are all one. It follows
by linearity that *each* column maps to its own edge incidence; graph
realization of the abstract matroid suffices.

Pad the output coordinates with zeros to dimension \(d\), and extend the
map on \(W\) to an invertible map on the ambient space by completing bases.
For a singleton, translate its image to zero. For a pair, its difference is
an edge, so a translation sends its two options to that edge's vertex labels.
For a triple, the three pair differences are nonzero, distinct, and sum to
zero. Their edges form a triangle, since three distinct, nonparallel nonloop
edges with zero incidence must form a 3-cycle. Write the two edges from the
first option's pair labels as \(uv,uw\), sharing vertex \(u\). Translate the
first option's image to the vertex label of \(u\); the other two then go to
the labels of \(v,w\). Each group may use its own translation. This proves
the reverse implication. With no differences the rank is zero and singleton
translations suffice. The restriction to triples is used in the triangle
argument, not in necessity.

**SAT decision and original witnesses.** The unit solver uses target
\(L(t)+\sum_i c_i\). Recover each selected original option by its local
lookup; recheck membership and XOR. It is unnecessary to build a basis
on unused ambient coordinates: first anchor each group at one original
option \(a_i\). If \(t+\sum_i a_i\notin W\), return UNSAT immediately.
Otherwise every translated option and the shifted target lies in \(W\);
one can solve there. This target test is a statement about feasibility, not
a negative answer to the structural recognition problem.

## 2. What recognizing this class costs

Reduce the labelled columns to fundamental coordinates \([I\mid N]\) relative
to any independent basis. A graph realization is equivalent to a tree with
the identity columns as its labelled edges and with the support of each
column of \(N\) forming a path in that tree. For a realizing forest, first
identify its component roots as above. Conversely, give a path its chord
joining the two ends: the XOR of the path's tree columns is the incidence
of that chord. A one-edge path gives a parallel edge. This proves the
equivalence for any chosen basis. The matrix and basis computation are
polynomial in the explicit input bit length.

This is the graph-realization problem solved constructively by Robert E.
Bixby and Donald K. Wagner, [*An Almost Linear-Time Algorithm for Graph
Realization*, Mathematics of Operations Research 13 (1988), 99–123](https://doi.org/10.1287/moor.13.1.99).
Applying their recognition result and the [phase-six matching reduction](support_threshold.md)
gives a polynomial recognition and decision route on the graphic subclass.
This is an application of known graph realization, not a claim to invent
matroid recognition. Verifying a supplied tree, finding one by a bounded
search, and implementing the full polynomial recognizer are distinct tasks.
Exhausting a bounded search need not prove that no realization exists.

## 3. A Fano minor on the lab's actual sparse 3SAT reduction

Use the phase-six constructor
[`three_cnf_to_weight_two_supports`](../src/pnp_lab/ternary_support.py)
on this connected formula, with three distinct variables per clause:

\[
 (x\lor a\lor b)\land(x\lor a\lor c)\land(x\lor b\lor c).
\]

This formula is satisfied by setting every variable true. The obstruction
below concerns the representation of its local choices, **not** a failure
of satisfiability. The [numeric fixture](../examples/graphic_fano_minor.json)
uses the constructor's original option order.

Index its nine literal occurrences consecutively, starting at zero. Write
\(V_j,C_j\) for the occurrence's value and clause-selection ports. In each copy
group the only pair difference is \(d_j=V_j+E_{\rm in}+E_{\rm out}\), where the
two equality ports are incident to the occurrence in its variable's copy
cycle. Local implication groups contribute *all three* of \(V_j,C_j,V_j+C_j\).
A clause selector contributes the pairwise sums of its three \(C_j\)'s. This
description of the **difference sets** also holds for negative literals,
although their option labels can change.

Contracting independent binary columns means quotienting by their span.
Delete all columns except the ones named for the minor.

1. Contract all nine copy differences. This substitutes the incident pair
   of equality ports for each \(V_j\). For the three occurrences of \(x\),
   \(V_0,V_3,V_6\) become the three distinct nonzero points of a plane: they
   are consecutive pairs on a triangle of equality ports. The two occurrences
   of each auxiliary variable have the same nonzero value vector (their two
   parallel cycle ports), independent between variables.
2. Contract two independent selector differences in each clause. This
   identifies all \(C_j\)'s of a clause with a common coordinate, initially
   independent between clauses. Next contract \(V_j+C_j\) at both occurrences
   of \(a\) and both of \(b\): indices \(1,4,2,7\). The shared value of \(a\)
   equates the first and second clause coordinates; the value of \(b\)
   equates the first and third. Their common value \(z\) is nonzero and
   independent of the private \(x\) plane. Indeed, four identifications set
   five previously independent quantities (two auxiliary value vectors and
   three clause coordinates) equal, without annihilating the common value.
3. Retain seven labelled columns: the three \(V_j\)'s for \(x\), one \(C_0\),
   and all three \(V_j+C_j\)'s for \(x\). In quotient basis
   \((V_0,V_3,z)\), they have masks `1,2,3,4,5,6,7` in order.

These are **all seven nonzero vectors of rank three**, the Fano matroid
\(F_7\). This minor cannot be graphic: seven distinct nonzero binary columns
would require seven edges without loops or parallel pairs, whereas a simple
graphic matroid of rank three has at most six edges. For example, identify
one root per component; this preserves simple edges and gives a simple graph
on four vertices. Graphicness is preserved by deletion and contraction:
deleting an edge deletes its column, and identifying its endpoints
quotients out its incidence vector. Thus the original matroid cannot be
graphic. By Section 1 **no** invertible common basis change and per-group
translations can send all its supports to weight at most one. Even padding
into a larger space by an injective common linear map leaves its matroid
unchanged, so that alone does not help either.

This survives the [implemented affine presolve](../src/pnp_lab/frontier.py).
All nine copy groups are binary with independent directions (each has its
own \(V_j\)); they are absorbed. In that quotient each local group still
spans its two independent directions \(V_j,C_j\), since the former is a
nonzero equality-port pair and the latter an independent selector port.
Each clause group still has its three options too. An affine coset cannot
have cardinality three, so no further group is absorbed. The remaining
selector and local contractions above give exactly the same Fano minor.

**A minimally UNSAT companion.** On three variables take all eight
three-literal sign patterns; each assignment falsifies exactly one clause.
After absorbing the 24 copy differences, the eight value vectors for each
variable are the consecutive edges of its private eight-cycle. Retain three
edges for \(x\) (in clauses 0, 1, 2), two for \(y\) (0, 1), and two for
\(z\) (0, 2). Contract the 17 other value vectors using local pairs. This
contracts edges in each cycle, leaving one triangle and two parallel pairs.
Identify all selector ports within each of the three designated clauses;
contract the four retained auxiliary value-plus-selector differences.
The same seven local \(x\) columns then give the same rank-three minor.
These comparisons use vectors, not sign-sensitive option indices. The
obstruction thus occurs on both truth values of the SAT decision.

## 4. A connected family with many group-disjoint obstructions

Take \(g\ge3\) disjoint copies of the three-clause gadget, with private
variables \(x_i,a_i,b_i,c_i\). Join them by the extra positive clauses
\((c_i\lor c_{i+1}\lor c_{i+2})\) for \(1\le i\le g-2\). Each source variable
occurs at most five times. The source is connected and has no duplicate
clause or repeated literal within a clause. Write all gadgets before these
extra clauses so the compact index recipes remain simple.

For gadget \(i\) we do **not** need any difference from the new bridge clauses
or from groups propagating the connector variable \(c_i\).
Contract only the seven copy differences for \(x_i,a_i,b_i\). In its first
selector contract both independent differences, identifying \(C_x,C_a,C_b\);
in its second and third contract only \(C_x+C_a\) and \(C_x+C_b\),
respectively. Contract the same four auxiliary local differences for
\(a_i,b_i\). The previous seven retained private labels give \(F_7\) again.
The 15 contractions are independent; their total rank together with the
retained labels is 18. The only value and equality ports used are private
to \(x_i,a_i,b_i\). The selector differences used involve no occurrence of
\(c_i\). Each certificate consequently occupies groups belonging to its
own gadget only, disjoint from the groups of every other certificate.
Equivalently, first quotient out all copy groups of the **original** input;
the eight remaining contractions per gadget and its seven private retained
columns still certify the minor. As before, this initial affine presolve
does not absorb any further groups.

In particular, just deleting or restricting options in **fewer than \(g\)
groups** leaves a complete untouched obstruction in at least one gadget.
If all remaining groups are required to have one simultaneous unit
representation, no global coordinate change can repair it. The statement
holds for the original supports and for the once-presolved supports just
described. This is a structural lower bound on how many groups must be
modified in this particular repair model. It is not a search-time lower
bound for arbitrary conditioning, additional quotient operations after
conditioning, symbolic combinations of several matchings, a different
encoding, or SAT itself. Indeed the whole family has the all-true witness.

For the distinction from a possible P versus NP result, the remaining
target is a method that handles **many interacting** obstructions on general
inputs in total polynomial bit time. A graph realization, a small defect
parameter, or a Fano certificate alone does not supply such a method.
