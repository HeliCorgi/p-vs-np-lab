# Finding and checking one-way maps between residual 3-CNFs

Let A be the branch to drop and B the branch to keep. A certificate specifies each **target** bit as a Boolean constant or a signed literal on the source bits. The same explicit named scope of n bits is used on both sides; variables need not occur in either formula. Different target bits may use the same source bit. A substitution need not be reversible.

## The proof obligation

Pull each original clause of B back through the substitution. It must either contain a true constant, contain both signs of a variable, or (after removing false constants and duplicates) contain an entire original clause of A. In the last case that source clause implies the pulled-back clause. Thus the image of every A-model satisfies every B-clause. If A has no models the implication is vacuous, but we still require the same syntactic checks. In a disjunction of live branches containing both, replacing A or B by B preserves satisfiability. This is conditional witness transport: it does not generate a source witness or certify that either branch is SAT.

The [implementation](../src/pnp_lab/witness_transport.py) exposes:

* `find_transport(n,A,B,*,strategies=...)` returns a JSON-compatible certificate or `None`. Defaults: `identity,flip,rename,single,constants`. An explicit list isolates strategies for experiments.
* `check_transport(n,A,B,cert)` is independent of discovery, its Gaussian elimination, and its color refinement. It scans raw signed clauses, compares complete literal sets and tests at most eight source-clause subsets per pulled-back clause. It ignores the claimed discovery method. A malformed certificate is rejected.
* `apply_transport(n,cert,source_mask)` computes the target word. Literals are signed one-based integers; constants are JSON true/false, distinct from integer 1. The certificate kind is `signed-substitution-v1`.

A failed search/certificate is never evidence against satisfiability. Even a *sound* map can fail the syntactic test if its validity requires a nontrivial semantic consequence of A.

## Sign flips: exact reductions to small local relations

For a diagonal substitution write y_i=x_i XOR t_i. Canonicalize clause order, duplicate literals, tautologies and subsumed clauses for discovery. Let S be the support of a target clause, with |S|<=3. Use a word u in {0,1}^S to record its signs, 1 meaning a negative literal. A flip takes the sign word to u XOR t|S. Compute T_S, all target sign words on S; and G_S, those words whose signed clause contains a canonical source clause (the source clause need not have support S). The exact local condition for our checker on diagonal maps is

    U_S = {v : for every u in T_S, u XOR v belongs to G_S}.

Canonicalization does not strengthen this condition: a removed target clause either is tautological or contains a smaller remaining clause, and a removed redundant source clause has a remaining subclause. A conjunction potentially equal to false is represented by an empty clause when that clause is syntactically present; no satisfiability oracle is used. For completeness on the empty-clause case, an explicit empty source clause subsumes every target clause. We must find a **single global t** whose restrictions lie in every U_S. Nonempty local sets alone do not settle that global problem.

For exact equality of the sign profiles of two canonical formulas (identical supports and multiplicities of distinct sign words), separately use the shifts V_S carrying T_S exactly to the same-support source set. If v0 is one such shift, all others are v0 plus the translation stabilizer of T_S: differences of valid shifts stabilize the set, and stabilizers form a linear space. Thus V_S is empty or affine. The code enumerates its at most eight points and expresses it by all parity equations constant on it. A single Gaussian-elimination pass solves the global compatibility problem, including constraints shared across many scopes. **If any diagonal sign flip makes the two canonical clause sets identical, this algorithm finds one.** Matching the size profile alone need not yield a solution.

For one-way subsumption the U_S are more general. The implemented global solvers have the following guarantees (uniform class means all local relations simultaneously):

| Local condition | Discovery |
|---|---|
| Every U_S is affine | Solve the exact global GF(2) system. For arbitrary U_S first try the affine hulls and directly validate the candidate; an inconsistent hull system rules out any flip. |
| Every U_S equals its unary/binary projection constraints | Forbid missing unary/binary patterns; check the resulting local truth set has the same size as U_S. Solve their conjunction as a single 2-SAT instance by strongly connected components. |
| All U_S are closed under componentwise AND | Start at the zero word. For each relation intersect all local extensions of the current required ones, force their common bits, and repeat. An empty list of extensions refutes the candidate system. Each new one is forced in every compatible model; at a fixed point each local projection is its own allowed minimum. |
| All U_S are closed under componentwise OR | Complement the bits, run the preceding Horn computation, and complement the answer. |
| Other mixtures | Try two choices of an inscribed affine space per local set (largest dimension, deterministic opposite tie breaks), then solve globally. Sufficient only. |

Each scope table has at most eight entries; even the search for an inscribed local flat has a fixed constant bound. There is no global enumeration of 2^n flips. Elimination has polynomial bit cost on n-bit rows; the closure scans strictly increase a subset of n bits. A polynomial amount of work per call does not itself bound the number of comparisons in a SAT search tree.

## Non-diagonal strategies and their scope

The `rename` strategy constructs the two signed literal/clause incidence graphs, joining opposite literal vertices, refines colors simultaneously, and proposes one pairing within matching color classes (prefer the identity where possible, then pair remaining indices in order). Colors include the literal/clause vertex type and the previous color. Distinct colors only split the partition; after at most linearly many strict refinements it is stable. This is a candidate generator, **not** a complete colored-graph-isomorphism algorithm. The raw clause checker validates its proposed substitution.

The `single` strategy is complete for maps differing from the identity on at most one target coordinate. That coordinate must appear in *every* currently failed target clause, so there are at most three candidates unless the identity already works. Try both constants and all signed source literals, testing the affected clauses. The `constants` strategy tries the two uniform target assignments; it does not call a SAT oracle. All discovery strategies run in deterministic polynomial time in the explicitly represented input, including its n listed variables.

## A hardness boundary with easy SAT inputs on both sides

For any finite simple 3-uniform hypergraph H, put six 3-clauses on each edge of A, forbidding its six nonmonochromatic words. Thus every edge of any source model is monochromatic. In B put the single all-positive clause on each edge. A has the all-zero and all-one models; B has the all-one model. Neither side requires difficult SAT search just to know its yes/no answer.

A diagonal shift by t maps **every** A-model to a B-model if and only if **no edge of t is monochromatic**. On a mixed edge either monochromatic source word produces a target containing a one. Conversely, if t is constant on an edge, use the matching constant source assignment to make that edge all zero after the shift. The same equivalence holds for the syntactic checker: a pulled-back edge clause has a sign pattern present in A exactly when it is mixed. All clauses have three distinct variables, so no shorter unrelated clause can justify it.

Proper 2-colorability of 3-uniform hypergraphs is NP-complete (even stronger gap hardness: [Dinur, Regev and Smyth, *The Hardness of 3-Uniform Hypergraph Coloring*](https://cims.nyu.edu/~regev/papers/hyper_color.pdf); see also [Schaefer's dichotomy](https://doi.org/10.1145/800133.804350)). Hence deciding whether a *syntactically checkable* diagonal shift exists is NP-complete; membership follows by checking n proposed bits. Semantic diagonal transport is at least NP-hard; we do not claim semantic checking is in P on arbitrary inputs. The hardness examples may be made connected: join components by edges (u,v,w) using old vertices from different components and a fresh w; any coloring of the old graph extends across each added edge. A then has **exactly two** source models. This is not hardness for every kind of witness map: a constant all-one map always works on this particular target. It also says nothing against polynomially finding useful but incomplete maps.

The [test suite](../tests/test_witness_transport.py) enumerates all 128 proposed shifts on the seven-vertex Fano plane and its one-edge deletion. Both give two source models; the first has no successful diagonal shift, whereas the second does. It also exercises a pinned 137-bit translation, the separate 2-SAT/Horn/dual-Horn paths, malformed certificates, and transport of actual small source witnesses.

## Prior work and scope

Szeider's [*Homomorphisms of conjunctive normal forms*](https://www.ac.tuwien.ac.at/files/pub/szeider-2003.pdf) studies complement-preserving literal maps between clause sets. In our orientation the syntactic map is from the **target** variables to source literals and its model map runs from source to target. Our checker also accepts constants, true or tautological images, and a pulled-back target clause containing a source clause. [Buss and Thapen](https://lmcs.episciences.org/7400) study substitution redundancy in propositional proof systems; that rule concerns adding a redundant clause to one formula and can use propagation. Here we compare two separate frontier residuals and test a more restrictive clause-containment justification. We claim neither the substitution concept nor the general idea of a checkable witness map as new.
