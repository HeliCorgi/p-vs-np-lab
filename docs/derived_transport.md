# Witness transport with independently proved target clauses

Let A be the proposed branch to discard and B the branch to retain. A map
assigns to each target variable a signed source variable or a Boolean
constant. Write Cσ for a target clause after substitution. If A entails Cσ
for *each* target clause C, evaluating the map on any A-model yields a
B-model. This is sufficient for replacing the disjunction A∨B by B;
computing either branch's SAT status is unnecessary. The earlier
[direct checker](transport_discovery.md) required each non-tautological
Cσ to contain an input clause of A. The new [checker and finder](../src/pnp_lab/derived_transport.py)
accept multiple original clauses as the reason for a single goal.

## Reasons and their interpretation

For each target clause the checker reconstructs the assignment required to
make it false. Inconsistent required bits (including an incompatible constant)
make it automatically true; otherwise the checker accepts a contained input
clause or a refutation under those required bits. A refutation node contains
an ordered list of original 0-based clause IDs. Each cited clause must be
unsatisfied so far and have exactly one unassigned literal; the checker
assigns that literal true. At a leaf, a final cited original clause must
have all its literals false. An internal node instead names an unassigned
variable and supplies proofs under **both** values. No unproved learned
clause is inserted into the premise list. The checker uses its own
literal-set evaluator and does not rely on search order or search statistics.

For soundness take a source model falsifying the pulled-back goal. Each unit
step is forced in that model; at a split one of the two children retains
it. A leaf therefore contradicts that it satisfied an original clause.
Applying this separately to each target clause proves witness transport,
including when A itself has no model. The [Lean development](../Formal/DerivedTransport.lean)
proves the corresponding structural rule, not correctness of the Python parser
or a bound on the search. The depth-zero rule is standard reverse unit
propagation (RUP); ordered clause hints are familiar from
[Cruz-Filipe et al., *Efficient Certified RAT Verification*](https://www.cs.cmu.edu/~mheule/publications/lrat.pdf).
The higher levels here bound the number of case splits down a proof path;
they are **not** the fixed-point nested failed-literal hierarchy of
[Gwynne–Kullmann](https://arxiv.org/abs/1204.6529). No novelty is claimed
for unit resolution, case splits or substitution reasoning.

## Discovery, charged resources, and stopping

With a supplied image map, try to prove all goals; otherwise try identity
and/or a diagonal sign flip. For each unsigned target support, query the at
most eight possible sign words, obtaining a table of independently proved
source consequences. For a flip mask to work, the translated target clauses
must be among these consequences (or contain a proved subclause). The
[local affine / 2-CNF / Horn routines](transport_discovery.md) propose a
global shift without enumerating all 2ⁿ masks. Only after fresh verification
on raw clauses is the resulting map returned. The finder is incomplete even
with no explicit budget. UNKNOWN, with or without budget exhaustion, never
justifies a merge. A supplied map can also represent constants, renamings
and many-to-one folds; the default strategies do not search all such maps.

The search propagates units until stable and then tries each unassigned
variable occurring in unresolved clauses as the next split. At residual
split depth d it can visit at most 1+2n+...+(2n)^d propagation nodes per
nontrivial query. At any such node at most n bits are forced before stable
or conflict; naive scanning is polynomial in n and the input length. The
implemented depth is capped at 3 (hence a uniform polynomial bound for this
*partial finder*, not for SAT). Each **successful** reason tree has at most
2^(d+1)−1 nodes; unsuccessful search work is separately charged. Repeated
literal goals are cached, including failures. Statistics distinguish unique
non-syntactic queries, propagation nodes, attempted splits, unit steps,
clause scans, syntactic/cache hits and candidate maps. Query and node caps
apply across an entire finder call, not per clause. They bound those
counters, not the cost of hash tables, input processing, shift discovery,
or the final verification. Goal truth by a contained clause or tautology
need not spend a propagation node.

## A separation from *all* direct maps, not just a poor choice of map

Start with any clause-minimal UNSAT B having m nonempty clauses. Privately
split each C=P∨q into (P∨w_C) and (¬w_C∨q) to form A with 2m clauses.
Projection of A is equivalent to B. Moreover, A is still clause-minimal
UNSAT: deleting either half, take the critical assignment satisfying all
other original clauses and falsifying C; choose w_C to violate only the
deleted half and all other helpers to satisfy their pairs. In a purported
direct certificate A→B at most m input clauses of A can be used: each
target clause is tautological after the substitution or chooses a single
subsuming source clause. Delete one unused A-clause; the same certificate
would map a model of the now satisfiable A to the impossible B. Thus **no
direct certificate of *any* allowed constant/literal map exists**. In contrast
the identity on the original variables works under RUP. Falsifying C
makes its two private clauses require opposite values of w_C. One unit and
one conflict reference per C suffice, independent of assignments to the other
variables. For satisfiable B the same construction gives an actual model
map too, but the nonexistence of *every* direct map was only proved on the
specified minimally UNSAT family (a satisfiable target always admits a
constant model map). The encoded width remains at most three when the
original width was at most three.

[Tests](../tests/test_derived_transport.py) also plant a forced nonidentity
flip invisible to raw clause matching; verify transported assignments and
reject altered reasons, maps and conflicts. On the previous simple-support
six-bit [forcing gadget](split_parity.md), RUP alone cannot prove any of
its three pins. The deterministic depth-1 search proves pins 4 and 5 in
3 and 4 propagation nodes, and depth 2 proves pin 6 in 8 nodes. This is
a fixed gadget, not a method for finding every entailed unit.
