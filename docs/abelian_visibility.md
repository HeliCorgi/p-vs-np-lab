# Exactly which finite abelian charge defects can prime-field linear laws see?

Fix a finite abelian group A, written additively. On an oriented connected graph require an A-valued edge flow whose divergence (outgoing minus incoming) equals qᵥ at each vertex. Let c=∑ᵥ qᵥ denote the **total defect**. Define the subgroup

    D = intersection of pA over primes p dividing |A|,     pA = {pa : a ∈ A}.

**Classification.** With the scope and encoding conventions below:

* If c∉D, there is a single prime p and one field-valued affine equation per complete vertex star whose sum proves a contradiction.
* If 0≠c∈D, there is a single Boolean word, not a model of the input, which satisfies **every** affine equation over **every** field that follows from the raw clauses in any permitted local scope. Even subsequently combining these equations by arbitrary sound reasoning, while using only the equations and the Boolean domains, cannot refute the instance.
* If c=0, the network has a flow, by a spanning-tree solve. Consequently there cannot be a sound refutation.

Thus local prime-field equations see precisely whether c is nonzero in A/D. This does **not** assert that A/D is the full local solution relation, or that an individual preprocessor can identify A, the representation or its stars.

## Encoding, locality and graph hypotheses

Use one named indicator per state on each edge; the names may be independently permuted, and all Boolean coordinates may then be signed/permuted globally. Edge-domain constraints enforce exactly one state. Additional edge-private helpers are allowed provided they have a known simultaneous valid extension as unary functions of that edge's state (in particular, unique such helpers suffice). There are no unconstrained communication channels between distant vertices. The charge at a vertex is encoded by forbidding each incompatible tuple of incident edge states; each such raw clause mentions all its incident edges. On a cubic graph these are width-three clauses. Edge-block clauses themselves do not depend on any charge. These hypotheses specify why changing a charge at an unobserved vertex does not change the raw local problem. Merely having an equisatisfiable Boolean encoding is insufficient.

For the negative direction assume every edge e belongs to two cycles whose edge intersection is exactly {e}. This holds in a loopless three-edge-connected graph: after deleting e there are two edge-disjoint paths between its endpoints. Every allowed Boolean scope must omit all coordinates of some edge; an arbitrary scope of fewer than |E| bits does so. For the positive direction, the learner is permitted the entire local encoding on each complete star, and all its locally valid affine equations. For a fixed group and fixed-size edge representation, the number of bits in a cubic star is constant. On sufficiently large graphs the two requirements are compatible: a complete star fits in a bounded scope and still misses an edge elsewhere. If a particular scan only visits smaller scopes, the positive theorem is not by itself a claim about that scan.

## A homomorphism can detect a visible defect

When c∉D, choose p dividing |A| such that c∉pA. The quotient A/pA is a vector space over Fₚ. A linear functional on this space can be chosen nonzero on the class of c, for instance by extending that nonzero vector to a basis. Compose it with the quotient map to get χ:A→(Fₚ,+) with χ(c)≠0. On the legal edge block e, χ(tₑ) is the linear combination ∑ₐ χ(a)I[e,a] of its state indicators. Thus the oriented sum of these linear forms around v equals χ(qᵥ), an affine equation entailed by the complete raw star. Summing over v cancels every edge and leaves 0=χ(c). There are |V| local terms. Independent state renamings or signed Boolean coordinates merely change their coefficient lists or constants. The certificate requires no global enumeration of flows. Finding a hidden state encoding on an arbitrary CNF is a separate problem.

## One common word defeats every field on an invisible defect

Fix c∈D. Project all charges to A/D; their sum there is zero. Solve for a quotient flow by assigning nontree edges zero and solving for tree-edge values from leaves to a root. Pick any representative t*ₑ∈A for each quotient edge state and encode its edge word (including the chosen unary helper values). This single Boolean word depends on the input and the chosen representatives, **not** on a field, a local row, or a scope. When c≠0 it cannot satisfy the full CNF.

Take any candidate field K, local scope S, and an affine equation valid on its local raw models. Choose an edge of which S contains no bit, and at an endpoint subtract c from the prescribed charge. No charge-specific clause at that vertex lies wholly in S, so every flow respecting the repaired charges satisfies the original clauses on S. The repaired charge sum is zero in A. It is possible, moreover, to find a repaired flow t agreeing with the same t* modulo D on **every** edge: the difference between the repaired demands and div(t*) lies in D at every vertex and has zero total in D. Solve this difference by a spanning-tree flow valued in the subgroup D and add it to t*. This argument applies even if D has no direct-summand complement in A.

Evaluate the proposed linear form on legal edge words. Its left side is ∑ₑ fₑ(tₑ) for some unary K-valued functions (add all contributions from coordinates and helpers on that edge). The sum is constant on the entire repaired flow coset. For an edge e, choose two oriented cycle circulations C₁,C₂ meeting only at e, with both orientations positive on e. Compare the row on t, t+aC₁, t+bC₂ and t+aC₁+bC₂. All four are repaired flows for any a,b∈A. In the alternating sum every other edge cancels. By first translating the flow on one cycle, any starting edge state x is possible. Therefore

    fₑ(x+a+b) − fₑ(x+a) − fₑ(x+b) + fₑ(x) = 0     for all x,a,b ∈ A.

At x=0 this says fₑ−fₑ(0) is a group homomorphism A→(K,+). In characteristic zero a finite group has zero image in the torsion-free additive group of K. In positive characteristic p, every such map kills pA; if p does not divide |A| then pA=A. In **all** cases the homomorphism kills D. Thus each entire edge contribution fₑ(tₑ) equals fₑ(t*ₑ). A helper bit viewed separately need not be constant on D-cosets; it is the contribution of all that edge's coordinates to the locally valid row which has this property. Since t satisfies the row, so does t*. This works simultaneously for all rows and fields. The total argument uses neither division by the number of repaired flows nor uniform random sampling in a problematic characteristic.

## What the classification says for concrete groups

Write A as the product of its p-primary components A₍ₚ₎. Multiplication by p is an automorphism on every other prime's component, so D is the product of the subgroups pA₍ₚ₎. Equivalently D=rad(|A|)A, where rad is the product of the distinct prime divisors. For the trivial group use D=A={0}. Hence D=0 iff **the group exponent is squarefree** (exponent 1 included). The group *order* is not the relevant criterion.

| Edge group | D | Consequence for total charge |
|---|---|---|
| Z/4 | {0,2} | Characteristic two sees odd charge; total 2 is invisible locally over all fields. |
| Z/6 | {0} | A nonzero defect is seen modulo two or modulo three. |
| Z/8 | {0,2,4,6} | Even the union of all fields sees only parity; e.g. 2 and 4 are invisible defects. |
| Z/2 × Z/2 | {0} | The order is four but the exponent is two; the two coordinate functionals over F₂ distinguish all defects collectively. |

The [Z/3 experiment](ternary_flow.md) and [Z/4 construction](four_flow.md) exemplify the two outcomes. For charge 2 in Z/4 the [native ring solver](../src/pnp_lab/cyclic_four.py) escapes because the **additive** ring itself has an element of order four, whereas the additive group of no field does. This result concerns a specific conservation-law class and a specific local linear interface; it is not an impossibility theorem for other algebraic proof systems, fresh encodings, combined use of raw nonlinear clauses, or polynomial-time SAT.
