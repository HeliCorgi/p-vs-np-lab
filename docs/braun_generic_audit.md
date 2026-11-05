# The phase-20 extension of the Braun source audit

**Status, 2026-11-05: bounded static source inspection, with independently
reconstructed paper arguments.** No upstream installer, script, workflow,
Lean build, compiled artifact, or kernel checker was run. The full bit-PHP
theorem and its complete imported axiom set remain outside this audit.

This extends [the phase-19 audit](braun_resoplus_audit.md), using the same
upstream revision:

[kbr-/math-research at 25239211058ef718402a908b3272f01480c159c4](https://github.com/kbr-/math-research/tree/25239211058ef718402a908b3272f01480c159c4).

The question this time was specific: what does the generic separated-space
criterion require, and can its mathematical mechanism be checked without
assuming the preprint's advertised bit-PHP lower bound?

## 1. What the next dependency slice actually does

The additional source reads resolve the following parts of the chain.

| Piece | Mathematical content found in the source |
|---|---|
| GenericAffineSubspaceConsequence | A joint linear map sends a degree-$k$ polynomial to its ordinary affine restrictions on all proper high-rank blocks. Rank-nullity gives a dimension budget after showing that the joint kernel consists of old-base PC consequences. |
| AffineBlockRestriction and AffineRestrictionIdeal | A consistent affine system of rank $r$ can be made the first $r$ coordinates by an affine bijection. A polynomial whose **ordinary** restriction is zero is a literal sum of the original affine generators with coefficients of degree at most $k-1$. |
| LowRankENS | If an affine-input span has rank at most $h(k+1)$, divide a basis into $h$ groups of size at most $k+1$. Product telescoping produces coefficient substitutions of degree at most $k$, making the ENS product an exact zero-set indicator. |
| AffineFamilyRemovalWithUnits | Use the low-rank substitutions on low blocks. A high block either has a constant-unit span, or a supplied representation of the target polynomial in its affine-input ideal. A weighted substitution replay removes all fresh blocks together. |
| PolynomialCalculusSubstitution and PolynomialCalculusReuse | The weighted replay costs $kD+\deg f$. Multiplication of an already completed line costs the maximum of its old proof bound and its new product degree; it does not multiply the entire preceding proof. |
| BooleanReduction | Squarefree reduction comes with ordinary Boolean-axiom multiples at the original polynomial degree. Boolean-zero polynomials therefore have explicit degree-controlled ordinary certificates. |
| AffineClauseWeakening and AffineClauseResolution | The clause registry simulates semantic weakening through degree $\max(K,4h)$ and complementary resolution through $\max(K,4h+1)$, using completed premise values. |
| BinarySemanticAffineCover | A sound binary semantic inference reduces to one weakening, or two weakenings followed by complementary resolution. The latter needs at most two auxiliary clauses. |
| MpTelescoping | The registry identities and their degree upper bounds are explicit algebraic telescoping identities. |

The generic statement uses the actual inductive ordinary-PC consequence
space. It does not identify it with a bounded Nullstellensatz span.
Nullstellensatz certificates are used for particular Boolean-zero
polynomials and then embedded in ordinary PC by explicit derivation rules.

### The two removal cases

For a block with affine forms $g_i$ and accuracy $h$, the fresh product is

\[
                  V=\prod_{u=1}^{h}
                         \left(1-\sum_i z_{u,i}g_i\right).
\]

Its companion axioms are $g_iV=0$.
For a low-rank block, the substituted product becomes the indicator of the
common zero set of the $g_i$. Thus every companion is Boolean-zero, with
an ordinary degree bound given in the source.

For a proper high-rank block, the supplied witness
$f=\sum_i a_i g_i$, with $\deg a_i\le k-1$, lets the first coefficient row
be set to the $a_i$ and the remaining rows to zero. The product becomes
$1-f$. After weighting by $f$, every companion is
$fg_i(1-f)$, which vanishes on the Boolean cube over $\mathbb F_2$.
If the affine span contains $1$, a constant coefficient substitution makes
the product zero instead. These explain the precise high-block
alternatives; no unproved block values are inserted as old axioms.

The simultaneous replay has degree at most $k(D+1)$ when
$h,k\ge1$ and $D\ge2h+1$. The inspected proof accounts separately for
old axioms, substituted Boolean axioms, and companions.

## 2. Registry transfer: the algebra behind the degree bound

For a registered affine clause $A$, its value $V_A$ has degree at most
$2h$, and there are cofactors $P_{A,i}$ of degree at most $2h-1$ such that

\[
                      1-V_A=\sum_i P_{A,i}g_{A,i}.
\]

The complete registry contains the companion axioms $g_{A,i}V_A$.
The values $V_A$ are derived; they are not themselves extra input axioms.

If $A$ implies $T$ and the falsity flat of $T$ is nonempty, every affine
form of $A$ lies in the span of the affine forms of $T$. Thus the
companions of $T$ derive $g_{A,i}V_T$. From a completed derivation of
$V_A$, the identity

\[
              V_T=V_A V_T+\sum_i P_{A,i}(g_{A,i}V_T)
\]

costs at most $\max(K,4h)$. If $T$ is a tautology, its affine span contains
$1$, and a linear combination of its companions derives $V_T$ directly.

For complementary resolution, the source derives residuals

\[
 R_A=V_T-P_{A,u}uV_T,\qquad
 R_B=V_T-P_{B,1-u}(1-u)V_T
\]

through degree $\max(K,4h)$. Multiplying the first residual by $1-u$ and
correcting with the Boolean consequence $u^2-u$ yields $(1-u)V_T$
through degree $\max(K,4h+1)$. Multiplying this completed small-degree
line by $P_{B,1-u}$ and adding $R_B$ gives $V_T$ at the same bound.
The degree cost does not depend on the number of preceding source nodes.

For a width-$w$ raw input clause, its falsity product
$E_A=\prod_i(1-g_{A,i})$ is an old axiom. Product telescoping for
$1-E_A$ and the companions give $V_A$ through degree $2h+w$.
The fixed registry therefore transfers a source DAG through
$D=\max(2h+w,4h+1)$.

For the stronger binary semantic rule, restrict attention to the falsity
flat of the conclusion. The two premise falsity sets cover it. Either
one contains the whole flat, giving weakening, or the two intersections
are disjoint complementary hyperplanes. A separating affine form then
gives two weakenings and one complementary resolution. This is the
finite-dimensional content of the inspected normalization proof.

These algebraic reconstructions support the visible transfer mechanism.
They do not report a successful Lean build or validate every imported
formal dependency.

## 3. Why the new lab argument can be checked separately

The audit prompted a shorter route, recorded completely in
[the common-annihilator theorem](affine_dag_annihilator.md).
Choose a rank threshold $R$, and one polynomial $f$ vanishing on the
falsity flat of every proof line whose rank exceeds $R$. For low-rank
lines, use their ordinary falsity indicators $q_A$ of degree at most $R$.
Sound semantic inference replays the weighted indicators $fq_A$ through
degree $k+3R$, where $\deg f\le k$. The high-rank indicators do not have
to be expanded in that replay.

Rank-nullity now uses squarefree restrictions to affine flats, giving
the dimension bound

\[
 \dim U\le\dim\bigl(U\cap C_{k+3R}(F)\bigr)
             +\sum_{\text{distinct high flats }Z}
                  \sum_{j=0}^{\min(k,\dim Z)}\binom{\dim Z}{j}.
\]

The entire derivation, including Boolean-ideal correction and
ordinary-PC multiplication, is written in that note. It is a locally
paper-proved criterion, not a consequence adopted solely on the authority
of the upstream formal statement.

There is also a useful distinction between the two restriction budgets.
The upstream generic theorem uses **ordinary** restriction images and
the bound $\binom{n-r+k}{k}$. Replacing that number by the smaller Boolean
dimension is not merely a numerical simplification of its formal
statement: the kernel hypothesis changes from formal zero restriction
to zero as a Boolean function. The direct weighted-indicator proof
explicitly handles that latter hypothesis. The new note does not silently
change the definition inside the upstream theorem.

No priority claim is made for this mechanism or its eventual
combinatorial applications. The general separated-space viewpoint came
from the inspected work, and ordinary PC reduction methods have a
substantial earlier literature.

## 4. Exact additional source inventory

All paths below are under the pinned repository's
[formalization/claims directory](https://github.com/kbr-/math-research/tree/25239211058ef718402a908b3272f01480c159c4/formalization/claims).
The directory tree object was
$\texttt{0a76776d19637376eeb49f488845b59b95d24bcc}$.
The 17 new files total **109,875 bytes**. Each fetched file's byte length
and Git blob SHA-1 were recomputed locally and matched the directory
entry. Temporary audit inputs and their manifest are excluded from
publication as repository source.

| Additional source read | Verified Git blob SHA-1 |
|---|---|
| GenericAffineSubspaceConsequence.lean | 0f618ebfdbd484571dc0e995db69127c102fadbb |
| AffineBlockRestriction.lean | a7d5e37daab9d804a7cfc8278ea6ba7382d9bfa2 |
| AffineFamilyRemovalWithUnits.lean | 0cb44c60e439cce79b53116418a152140ffd93ff |
| AffineRestrictionIdeal.lean | 698b6a95ec289e393955220e48282ba62587d217 |
| LowRankENS.lean | b53bbaa651e67ef81d6ee7d7271f375afcc23a88 |
| FreshENSBlock.lean | 092a8fdd5cec256e38a018b3478e3ed354fd4811 |
| BooleanReduction.lean | 8770c6535d726173d149631c4b7bb53ccfc7aede |
| PolynomialCalculusSubstitution.lean | d3ebf1708788dee3469d4c5c9a41f9923c808454 |
| PolynomialCalculusReuse.lean | 41aaa239578395688fec35c9622fe7dc3d6d287f |
| CoordinateRestrictionIdeal.lean | 1bc00e9ed4c5798d31c857c05c4be5656ae92175 |
| AffineClauseWeakening.lean | dce3b9db3c83f554d55568f9e28b9414296d1ff3 |
| AffineClauseResolution.lean | b7dfd442535a77bf56a4a7a0b9b2737ba54854de |
| BinarySemanticAffineCover.lean | 87e4e4e88ee6b0b68db02c5ead2a68f996edfe1f |
| MpTelescoping.lean | 3e12134d32633e0d911a3ddee05e35af6e6cb243 |
| FiniteAffineSpan.lean | 19d783285cc44e097ca742818429321ce2f7a8dc |
| FiniteAffineCoordinates.lean | b5e05c0652b34542b45f457fb8c4216b77e02845 |
| AffineClauseCompression.lean | f088c30c2b794036a29c183fab1d7c2702b4db80 |

Together with phase 19 this is a bounded read of 29 distinct Lean files,
186,092 bytes. It is still not the complete transitive import closure.
In particular, complete source-to-build correspondence, all imported
axiom dependencies, and a fresh kernel replay have not been checked.
No conclusion about the correctness or incorrectness of the full
bit-PHP claim follows merely from this inventory.
