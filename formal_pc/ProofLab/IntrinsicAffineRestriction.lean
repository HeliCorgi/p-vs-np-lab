import ProofLab.OptimalAffineParameters
import ProofLab.ParametrizedDAGDimension

/-!
# Restriction budgets from the intrinsic rank of affine clauses

For every nonempty affine clause zero-set, the coordinate map is now constructed
with exactly `card V - spanRank C` parameters. Its restriction kernel is exactly
vanishing on that zero-set and its image has the proved Boolean binomial budget.

The DAG corollary chooses one chart per nonempty discarded node. Empty zero-sets
contribute no index and hence no spurious singleton cube. No chart or coverage
hypothesis remains. The ordinary-PC separation hypothesis remains explicit.
Repeated nodes are counted separately; no distinct-flat counting is asserted.
-/

namespace BoundaryLab.IntrinsicAffineRestriction

noncomputable section

open MvPolynomial AffineIndicators
open scoped BigOperators

variable {V : Type} [Fintype V]

/-- A chosen optimal chart, whose full properties are proved below. -/
def optimalCoordinates (C : Clause V) (hC : IsAffineClause C)
    (hne : ∃ a, clauseZero C a) :
    V → Poly (Fin (Fintype.card V - spanRank C)) :=
  Classical.choose (OptimalAffineParameters.exists_optimal_parameterization C hC hne)

theorem optimalCoordinates_spec (C : Clause V) (hC : IsAffineClause C)
    (hne : ∃ a, clauseZero C a) :
    (∀ v, (optimalCoordinates C hC hne v).totalDegree ≤ 1) ∧
      Function.Injective (AffineRestriction.coordinateMap (optimalCoordinates C hC hne)) ∧
      ∀ x, (∃ y, AffineRestriction.coordinateMap (optimalCoordinates C hC hne) y = x) ↔
        clauseZero C x :=
  Classical.choose_spec (OptimalAffineParameters.exists_optimal_parameterization C hC hne)

/-- The restriction kernel is the actual vanishing condition on the clause's
zero-set. Both directions use the exact image theorem for the constructed chart. -/
theorem optimalRestriction_eq_zero_iff
    (U : Submodule BinaryField (Poly V))
    (C : Clause V) (hC : IsAffineClause C) (hne : ∃ a, clauseZero C a) (p : U) :
    AffineRestriction.restrictionOn U (optimalCoordinates C hC hne) p = 0 ↔
      ∀ x, clauseZero C x → eval x p.val = 0 := by
  rw [AffineRestriction.restrictionOn_eq_zero_iff]
  constructor
  · intro hp x hx
    obtain ⟨y, hy⟩ := ((optimalCoordinates_spec C hC hne).2.2 x).mpr hx
    simpa only [hy] using hp y
  · intro hp y
    apply hp
    exact ((optimalCoordinates_spec C hC hne).2.2 _).mp ⟨y, rfl⟩

/-- The image budget is expressed in the intrinsic codimension complement,
with neither a supplied chart nor a numerical image-dimension hypothesis. -/
theorem finrank_optimalRestriction_le
    (U : Submodule BinaryField (Poly V))
    (C : Clause V) (hC : IsAffineClause C) (hne : ∃ a, clauseZero C a)
    (k : ℕ) (hU : ∀ p ∈ U, p.totalDegree ≤ k) :
    Module.finrank BinaryField
        (AffineRestriction.restrictionOn U (optimalCoordinates C hC hne)).range ≤
      BooleanFunctionSpace.booleanBudget k (Fintype.card V - spanRank C) := by
  simpa only [Fintype.card_fin] using
    AffineRestriction.finrank_restrictionOn_le U (optimalCoordinates C hC hne)
      (optimalCoordinates_spec C hC hne).1 k hU

/-- High rank gives the smaller parameter count used by the lower-bound route.
The consistency premise also ensures that natural subtraction does not conceal
a rank larger than the number of original variables. -/
theorem parameterCount_le_of_high_rank
    (C : Clause V) (hC : IsAffineClause C) (hne : ∃ a, clauseZero C a)
    (R : ℕ) (hR : R < spanRank C) :
    R < Fintype.card V ∧
      Fintype.card V - spanRank C ≤ Fintype.card V - R - 1 := by
  have hr := OptimalAffineParameters.spanRank_le_card_variables C hC hne
  omega

/-- Exactly the discarded DAG nodes whose zero-sets are nonempty. This is a
finite mathematical selection; it is not an algorithmic emptiness test. -/
def nonemptyDiscardedNodes {S : ℕ}
    (clauses : Fin S → Clause V) (Low : Fin S → Prop) : Finset (Fin S) := by
  classical
  exact Finset.univ.filter (fun i => ¬ Low i ∧ ∃ a, clauseZero (clauses i) a)

@[simp]
theorem mem_nonemptyDiscardedNodes {S : ℕ}
    (clauses : Fin S → Clause V) (Low : Fin S → Prop) (i : Fin S) :
    i ∈ nonemptyDiscardedNodes clauses Low ↔
      ¬ Low i ∧ ∃ a, clauseZero (clauses i) a := by
  classical
  simp [nonemptyDiscardedNodes]

variable [DecidableEq V] {S k R : ℕ}

/-- An intrinsic rank-profile inequality for the actual source-clause DAG.
The affine charts, their coverage, and all numerical restriction budgets are
constructed internally. Empty discarded zero-sets contribute nothing. -/
theorem affine_clause_intrinsic_budget
    {F : Set (Poly V)}
    (hbool : (MathResearch.PolynomialCalculus.booleanBase : Set (Poly V)) ⊆ F)
    (clauses : Fin S → Clause V) (initial : Fin S → Bool)
    (dag : AffineClauseDAG.ClauseDAG F clauses initial)
    (hAffine : ∀ i, IsAffineClause (clauses i))
    (Low : Fin S → Prop)
    (hinputWidth : ∀ i, initial i = true → (clauses i).card ≤ R)
    (hderivedRank : ∀ i, initial i = false → Low i → spanRank (clauses i) ≤ R)
    (finish : Fin S) (hfinish : clauses finish = ∅)
    (U : Submodule BinaryField (Poly V))
    (hU : ∀ p ∈ U, p.totalDegree ≤ k) :
    Module.finrank BinaryField U ≤
      Module.finrank BinaryField
        ↥(U ⊓ MathResearch.PolynomialCalculus.pcSpace F (k + 3 * R)) +
      ∑ i : nonemptyDiscardedNodes clauses Low,
        BooleanFunctionSpace.booleanBudget k (Fintype.card V - spanRank (clauses i.val)) := by
  classical
  let A := ↥(nonemptyDiscardedNodes clauses Low)
  let hne (i : A) : ∃ a, clauseZero (clauses i.val) a :=
    ((mem_nonemptyDiscardedNodes clauses Low i.val).mp i.property).2
  let t (i : A) := Fintype.card V - spanRank (clauses i.val)
  let g (i : A) : V → Poly (Fin (t i)) :=
    optimalCoordinates (clauses i.val) (hAffine i.val) (hne i)
  have hg : ∀ i v, (g i v).totalDegree ≤ 1 :=
    fun i => (optimalCoordinates_spec (clauses i.val) (hAffine i.val) (hne i)).1
  have hcover : ∀ i, ¬ Low i → ∀ x : V → BinaryField,
      clauseZero (clauses i) x →
        ∃ a : A, ∃ y : Fin (t a) → BinaryField, AffineRestriction.coordinateMap (g a) y = x := by
    intro i hi x hx
    let a : A := ⟨i, (mem_nonemptyDiscardedNodes clauses Low i).mpr ⟨hi, x, hx⟩⟩
    refine ⟨a, ?_⟩
    exact ((optimalCoordinates_spec (clauses a.val) (hAffine a.val) (hne a)).2.2 x).mpr hx
  exact ParametrizedDAGDimension.affine_clause_restriction_budget hbool
    clauses initial dag hAffine Low hinputWidth hderivedRank finish hfinish U hU t g hg hcover

/-- If the source space is separated from actual ordinary PC at the replay
degree, it must fit into the intrinsic rank-profile sum. -/
theorem affine_clause_separated_intrinsic_budget
    {F : Set (Poly V)}
    (hbool : (MathResearch.PolynomialCalculus.booleanBase : Set (Poly V)) ⊆ F)
    (clauses : Fin S → Clause V) (initial : Fin S → Bool)
    (dag : AffineClauseDAG.ClauseDAG F clauses initial)
    (hAffine : ∀ i, IsAffineClause (clauses i))
    (Low : Fin S → Prop)
    (hinputWidth : ∀ i, initial i = true → (clauses i).card ≤ R)
    (hderivedRank : ∀ i, initial i = false → Low i → spanRank (clauses i) ≤ R)
    (finish : Fin S) (hfinish : clauses finish = ∅)
    (U : Submodule BinaryField (Poly V))
    (hU : ∀ p ∈ U, p.totalDegree ≤ k)
    (hsep : ∀ p ∈ U, MathResearch.PolynomialCalculus.Derives F (k + 3 * R) p → p = 0) :
    Module.finrank BinaryField U ≤
      ∑ i : nonemptyDiscardedNodes clauses Low,
        BooleanFunctionSpace.booleanBudget k (Fintype.card V - spanRank (clauses i.val)) := by
  have hdim := affine_clause_intrinsic_budget hbool clauses initial dag hAffine Low
    hinputWidth hderivedRank finish hfinish U hU
  have hinter : U ⊓ MathResearch.PolynomialCalculus.pcSpace F (k + 3 * R) = ⊥ := by
    apply le_antisymm
    · intro p hp
      simpa using hsep p hp.1 hp.2
    · exact bot_le
  rw [hinter, finrank_bot, zero_add] at hdim
  exact hdim

end

end BoundaryLab.IntrinsicAffineRestriction
