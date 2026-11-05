import ProofLab.DimensionBudget
import ProofLab.MaskedDAG

/-!
# From semantic DAGs to dimension budgets

This module composes the actual ordinary-PC replay theorem with the
finite-dimensional kernel argument. The hypothesis on the linear maps is
pointwise: a polynomial in their joint kernel vanishes wherever a discarded
node evaluates nonzero. Derivability of that polynomial is proved internally,
using the semantic DAG and the explicit Boolean axioms.

The finite indexing type may index distinct discarded loci, rather than
occurrences of proof nodes. No affine structure, codimension, squarefree
restriction-image formula, or separated-space construction is assumed without
an explicit hypothesis. In particular, the supplied numerical image bounds
must be established for the actual chosen maps before applying these theorems.
-/

set_option autoImplicit false

namespace BoundaryLab.DAGDimension

noncomputable section

open MvPolynomial MathResearch.PolynomialCalculus
open scoped BigOperators

variable {V ι : Type} [Fintype V] [DecidableEq V] [Fintype ι]
variable {S k R : ℕ}
variable {E : ι → Type*}
variable [∀ a, AddCommGroup (E a)] [∀ a, Module (ZMod 2) (E a)]

/-- A semantic unary/binary DAG produces the ordinary-PC joint-kernel
containment, hence the dimension budget. The source space is finite-dimensional
because all its polynomials have ordinary total degree at most `k`. -/
theorem dag_dimension_budget
    {F : Set (Poly (ZMod 2) V)}
    (hbool : (booleanBase : Set (Poly (ZMod 2) V)) ⊆ F)
    {q : Fin S → Poly (ZMod 2) V} (dag : MaskedDAG.SemanticDAG F q)
    (Low : Fin S → Prop)
    (hdegree : ∀ i, Low i → (q i).totalDegree ≤ R)
    (finish : Fin S) (hfinish : q finish = 1)
    (U : Submodule (ZMod 2) (Poly (ZMod 2) V))
    (hU : ∀ p ∈ U, p.totalDegree ≤ k)
    (L : ∀ a, U →ₗ[ZMod 2] E a)
    (hrestriction : ∀ p : U, (∀ a, L a p = 0) →
      ∀ i, ¬ Low i → ∀ x : V → ZMod 2,
        eval x (q i) ≠ 0 → eval x p.val = 0)
    (budget : ι → ℕ)
    (hbudget : ∀ a, Module.finrank (ZMod 2) (L a).range ≤ budget a) :
    Module.finrank (ZMod 2) U ≤
      Module.finrank (ZMod 2) ↥(U ⊓ pcSpace F (k + 3 * R)) +
        ∑ a, budget a := by
  refine DimensionBudget.pc_family_budget F (k + 3 * R) k U hU L
    ?_ budget hbudget
  intro p hp
  exact MaskedDAG.masked_dag_replay hbool dag Low
    (hU p.val p.property) hdegree (hrestriction p hp) finish hfinish

/-- If the source subspace is separated from actual ordinary-PC consequences,
the same semantic DAG forces the full dimension into the restriction images.
Separation from static NS alone is not a hypothesis of this theorem. -/
theorem dag_separated_dimension_budget
    {F : Set (Poly (ZMod 2) V)}
    (hbool : (booleanBase : Set (Poly (ZMod 2) V)) ⊆ F)
    {q : Fin S → Poly (ZMod 2) V} (dag : MaskedDAG.SemanticDAG F q)
    (Low : Fin S → Prop)
    (hdegree : ∀ i, Low i → (q i).totalDegree ≤ R)
    (finish : Fin S) (hfinish : q finish = 1)
    (U : Submodule (ZMod 2) (Poly (ZMod 2) V))
    (hU : ∀ p ∈ U, p.totalDegree ≤ k)
    (L : ∀ a, U →ₗ[ZMod 2] E a)
    (hrestriction : ∀ p : U, (∀ a, L a p = 0) →
      ∀ i, ¬ Low i → ∀ x : V → ZMod 2,
        eval x (q i) ≠ 0 → eval x p.val = 0)
    (budget : ι → ℕ)
    (hbudget : ∀ a, Module.finrank (ZMod 2) (L a).range ≤ budget a)
    (hsep : ∀ p ∈ U, Derives F (k + 3 * R) p → p = 0) :
    Module.finrank (ZMod 2) U ≤ ∑ a, budget a := by
  refine DimensionBudget.pc_separated_family_budget F (k + 3 * R) k U hU L
    ?_ budget hbudget hsep
  intro p hp
  exact MaskedDAG.masked_dag_replay hbool dag Low
    (hU p.val p.property) hdegree (hrestriction p hp) finish hfinish

end

end BoundaryLab.DAGDimension
