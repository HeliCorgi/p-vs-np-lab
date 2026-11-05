import ProofLab.AffineRestriction
import ProofLab.AffineClauseDAG
import ProofLab.DAGDimension

/-!
# Explicit Boolean restriction budgets for semantic DAGs

The finite family of affine parameterizations below covers the nonzero loci of
all discarded polynomial nodes, or the zero-sets of discarded affine clauses.
The restriction maps and their kernels are constructed, and their image budgets
are proved by the squarefree Boolean function-space theorem. Numerical image
dimension bounds and final PC derivability are not hypotheses.

The parameter counts are explicit data. This module does not construct an
optimal parameterization from arbitrary affine equations, identify parameter
counts with codimension complements, or construct the separated source space.
The parameterizations may be noninjective and may cover additional points.
-/

set_option autoImplicit false

namespace BoundaryLab.ParametrizedDAGDimension

noncomputable section

open MvPolynomial MathResearch.PolynomialCalculus
open scoped BigOperators

variable {V ι : Type} [Fintype V] [DecidableEq V] [Fintype ι]
variable {S k R : ℕ}

/-- Concrete affine restrictions replace the numerical image-bound hypothesis
of the generic dimension theorem. Only their stated pointwise cover is needed. -/
theorem dag_restriction_budget
    {F : Set (Poly (ZMod 2) V)}
    (hbool : (booleanBase : Set (Poly (ZMod 2) V)) ⊆ F)
    {q : Fin S → Poly (ZMod 2) V} (dag : MaskedDAG.SemanticDAG F q)
    (Low : Fin S → Prop)
    (hdegree : ∀ i, Low i → (q i).totalDegree ≤ R)
    (finish : Fin S) (hfinish : q finish = 1)
    (U : Submodule (ZMod 2) (Poly (ZMod 2) V))
    (hU : ∀ p ∈ U, p.totalDegree ≤ k)
    (t : ι → ℕ)
    (g : ∀ a, V → MvPolynomial (Fin (t a)) (ZMod 2))
    (hg : ∀ a v, (g a v).totalDegree ≤ 1)
    (hcover : ∀ i, ¬ Low i → ∀ x : V → ZMod 2,
      eval x (q i) ≠ 0 →
        ∃ a, ∃ y : Fin (t a) → ZMod 2, AffineRestriction.coordinateMap (g a) y = x) :
    Module.finrank (ZMod 2) U ≤
      Module.finrank (ZMod 2) ↥(U ⊓ pcSpace F (k + 3 * R)) +
        ∑ a, BooleanFunctionSpace.booleanBudget k (t a) := by
  let L : ∀ a, U →ₗ[ZMod 2] ((Fin (t a) → ZMod 2) → ZMod 2) :=
    fun a => AffineRestriction.restrictionOn U (g a)
  have hrestriction : ∀ p : U, (∀ a, L a p = 0) →
      ∀ i, ¬ Low i → ∀ x : V → ZMod 2,
        eval x (q i) ≠ 0 → eval x p.val = 0 := by
    intro p hp i hi x hx
    obtain ⟨a, y, hy⟩ := hcover i hi x hx
    have hzero := (AffineRestriction.restrictionOn_eq_zero_iff U (g a) p).mp (hp a) y
    simpa only [hy] using hzero
  have hbudget : ∀ a, Module.finrank (ZMod 2) (L a).range ≤
      BooleanFunctionSpace.booleanBudget k (t a) := by
    intro a
    simpa only [L, Fintype.card_fin] using
      AffineRestriction.finrank_restrictionOn_le U (g a) (hg a) k hU
  exact DAGDimension.dag_dimension_budget hbool dag Low hdegree finish hfinish
    U hU L hrestriction (fun a => BooleanFunctionSpace.booleanBudget k (t a)) hbudget

/-- A separated source space must fit into the proved Boolean restriction
budget. The separation hypothesis refers to actual ordinary PC. -/
theorem dag_separated_restriction_budget
    {F : Set (Poly (ZMod 2) V)}
    (hbool : (booleanBase : Set (Poly (ZMod 2) V)) ⊆ F)
    {q : Fin S → Poly (ZMod 2) V} (dag : MaskedDAG.SemanticDAG F q)
    (Low : Fin S → Prop)
    (hdegree : ∀ i, Low i → (q i).totalDegree ≤ R)
    (finish : Fin S) (hfinish : q finish = 1)
    (U : Submodule (ZMod 2) (Poly (ZMod 2) V))
    (hU : ∀ p ∈ U, p.totalDegree ≤ k)
    (t : ι → ℕ)
    (g : ∀ a, V → MvPolynomial (Fin (t a)) (ZMod 2))
    (hg : ∀ a v, (g a v).totalDegree ≤ 1)
    (hcover : ∀ i, ¬ Low i → ∀ x : V → ZMod 2,
      eval x (q i) ≠ 0 →
        ∃ a, ∃ y : Fin (t a) → ZMod 2, AffineRestriction.coordinateMap (g a) y = x)
    (hsep : ∀ p ∈ U, Derives F (k + 3 * R) p → p = 0) :
    Module.finrank (ZMod 2) U ≤
      ∑ a, BooleanFunctionSpace.booleanBudget k (t a) := by
  have hdim := dag_restriction_budget hbool dag Low hdegree finish hfinish U hU t g hg hcover
  have hinter : U ⊓ pcSpace F (k + 3 * R) = ⊥ := by
    apply le_antisymm
    · intro p hp
      simpa using hsep p hp.1 hp.2
    · exact bot_le
  rw [hinter, finrank_bot, zero_add] at hdim
  exact hdim

/-- The complete source-clause interface: actual raw initial polynomials,
clause-level soundness, and affine covers construct all maps and derivations
needed for the numerical dimension inequality. -/
theorem affine_clause_restriction_budget
    {F : Set (Poly (ZMod 2) V)}
    (hbool : (booleanBase : Set (Poly (ZMod 2) V)) ⊆ F)
    (clauses : Fin S → AffineIndicators.Clause V) (initial : Fin S → Bool)
    (dag : AffineClauseDAG.ClauseDAG F clauses initial)
    (hAffine : ∀ i, AffineIndicators.IsAffineClause (clauses i))
    (Low : Fin S → Prop)
    (hinputWidth : ∀ i, initial i = true → (clauses i).card ≤ R)
    (hderivedRank : ∀ i, initial i = false → Low i → AffineIndicators.spanRank (clauses i) ≤ R)
    (finish : Fin S) (hfinish : clauses finish = ∅)
    (U : Submodule (ZMod 2) (Poly (ZMod 2) V))
    (hU : ∀ p ∈ U, p.totalDegree ≤ k)
    (t : ι → ℕ)
    (g : ∀ a, V → MvPolynomial (Fin (t a)) (ZMod 2))
    (hg : ∀ a v, (g a v).totalDegree ≤ 1)
    (hcover : ∀ i, ¬ Low i → ∀ x : V → ZMod 2,
      AffineIndicators.clauseZero (clauses i) x →
        ∃ a, ∃ y : Fin (t a) → ZMod 2, AffineRestriction.coordinateMap (g a) y = x) :
    Module.finrank (ZMod 2) U ≤
      Module.finrank (ZMod 2) ↥(U ⊓ pcSpace F (k + 3 * R)) +
        ∑ a, BooleanFunctionSpace.booleanBudget k (t a) := by
  apply dag_restriction_budget hbool
    (AffineClauseDAG.polynomialDag_of_clauseDag clauses initial dag) Low
    (AffineClauseDAG.retained_degree_bound clauses initial hAffine Low hinputWidth hderivedRank)
    finish (AffineClauseDAG.nodePolynomial_of_empty clauses initial finish hfinish)
    U hU t g hg
  intro i hi x hx
  exact hcover i hi x
    ((AffineClauseDAG.nodePolynomial_eval_ne_zero_iff clauses initial i x).mp hx)

/-- Separated version of the source-clause theorem, with every restriction
image budget supplied by the proved binomial formula. -/
theorem affine_clause_separated_restriction_budget
    {F : Set (Poly (ZMod 2) V)}
    (hbool : (booleanBase : Set (Poly (ZMod 2) V)) ⊆ F)
    (clauses : Fin S → AffineIndicators.Clause V) (initial : Fin S → Bool)
    (dag : AffineClauseDAG.ClauseDAG F clauses initial)
    (hAffine : ∀ i, AffineIndicators.IsAffineClause (clauses i))
    (Low : Fin S → Prop)
    (hinputWidth : ∀ i, initial i = true → (clauses i).card ≤ R)
    (hderivedRank : ∀ i, initial i = false → Low i → AffineIndicators.spanRank (clauses i) ≤ R)
    (finish : Fin S) (hfinish : clauses finish = ∅)
    (U : Submodule (ZMod 2) (Poly (ZMod 2) V))
    (hU : ∀ p ∈ U, p.totalDegree ≤ k)
    (t : ι → ℕ)
    (g : ∀ a, V → MvPolynomial (Fin (t a)) (ZMod 2))
    (hg : ∀ a v, (g a v).totalDegree ≤ 1)
    (hcover : ∀ i, ¬ Low i → ∀ x : V → ZMod 2,
      AffineIndicators.clauseZero (clauses i) x →
        ∃ a, ∃ y : Fin (t a) → ZMod 2, AffineRestriction.coordinateMap (g a) y = x)
    (hsep : ∀ p ∈ U, Derives F (k + 3 * R) p → p = 0) :
    Module.finrank (ZMod 2) U ≤
      ∑ a, BooleanFunctionSpace.booleanBudget k (t a) := by
  apply dag_separated_restriction_budget hbool
    (AffineClauseDAG.polynomialDag_of_clauseDag clauses initial dag) Low
    (AffineClauseDAG.retained_degree_bound clauses initial hAffine Low hinputWidth hderivedRank)
    finish (AffineClauseDAG.nodePolynomial_of_empty clauses initial finish hfinish)
    U hU t g hg
  · intro i hi x hx
    exact hcover i hi x
      ((AffineClauseDAG.nodePolynomial_eval_ne_zero_iff clauses initial i x).mp hx)
  · exact hsep

end

end BoundaryLab.ParametrizedDAGDimension
