import ProofLab.IntrinsicAffineRestriction
import Mathlib.Data.Set.Card

/-!
# Counting distinct falsity flats of the source DAG

The index set is the image of the actual nonempty discarded zero-sets, so
semantically equivalent clauses contribute once, even if their syntax differs.
Representatives and optimal affine charts are constructed internally. The
degree-bounded ordinary-PC separation hypothesis is still explicit: this module
does not construct the expander separator or an asymptotic CNF family.
-/

namespace BoundaryLab.DistinctAffineFlats

noncomputable section

open MvPolynomial AffineIndicators IntrinsicAffineRestriction
open scoped BigOperators

variable {V : Type} [Fintype V]

/-- The actual falsifying assignments, rather than a syntactic clause key. -/
def zeroSet (C : Clause V) : Set (V → BinaryField) := {x | clauseZero C x}

/-- A nonempty affine zero-flat has exactly the number of points prescribed by
its intrinsic rank. This also makes the rank independent of clause syntax. -/
theorem zeroSet_ncard (C : Clause V) (hC : IsAffineClause C)
    (hne : ∃ x, clauseZero C x) :
    (zeroSet C).ncard = 2 ^ (Fintype.card V - spanRank C) := by
  classical
  let g := optimalCoordinates C hC hne
  have hg := optimalCoordinates_spec C hC hne
  have himage : Set.range (AffineRestriction.coordinateMap g) = zeroSet C := by
    ext x
    exact hg.2.2 x
  rw [← himage, Set.ncard_range_of_injective hg.2.1]
  simp [Nat.card_eq_fintype_card]

theorem spanRank_eq_of_zeroSet_eq (C D : Clause V)
    (hC : IsAffineClause C) (hD : IsAffineClause D)
    (hne : ∃ x, clauseZero C x) (heq : zeroSet C = zeroSet D) :
    spanRank C = spanRank D := by
  have hneD : ∃ x, clauseZero D x := by
    obtain ⟨x, hx⟩ := hne
    refine ⟨x, ?_⟩
    change x ∈ zeroSet D
    rw [← heq]
    exact hx
  have hpow : 2 ^ (Fintype.card V - spanRank C) =
      2 ^ (Fintype.card V - spanRank D) := by
    rw [← zeroSet_ncard C hC hne, ← zeroSet_ncard D hD hneD, heq]
  have hdiff := Nat.pow_right_injective (by decide : 2 ≤ 2) hpow
  have hcr := OptimalAffineParameters.spanRank_le_card_variables C hC hne
  have hdr := OptimalAffineParameters.spanRank_le_card_variables D hD hneD
  omega

/-- The distinct nonempty discarded falsity flats. -/
def distinctFlats {S : ℕ} (clauses : Fin S → Clause V) (Low : Fin S → Prop) :
    Finset (Set (V → BinaryField)) := by
  classical
  exact (nonemptyDiscardedNodes clauses Low).image (fun i => zeroSet (clauses i))

theorem mem_distinctFlats {S : ℕ} (clauses : Fin S → Clause V)
    (Low : Fin S → Prop) (Z : Set (V → BinaryField)) :
    Z ∈ distinctFlats clauses Low ↔
      ∃ i, (¬ Low i ∧ ∃ x, clauseZero (clauses i) x) ∧ zeroSet (clauses i) = Z := by
  classical
  simp [distinctFlats]

/-- One source node for each distinct flat; no enumeration algorithm is claimed. -/
def representative {S : ℕ} (clauses : Fin S → Clause V) (Low : Fin S → Prop)
    (Z : distinctFlats clauses Low) : Fin S :=
  Classical.choose ((mem_distinctFlats clauses Low Z.val).mp Z.property)

theorem representative_spec {S : ℕ} (clauses : Fin S → Clause V) (Low : Fin S → Prop)
    (Z : distinctFlats clauses Low) :
    (¬ Low (representative clauses Low Z) ∧
      ∃ x, clauseZero (clauses (representative clauses Low Z)) x) ∧
      zeroSet (clauses (representative clauses Low Z)) = Z.val :=
  Classical.choose_spec ((mem_distinctFlats clauses Low Z.val).mp Z.property)

theorem card_distinctFlats_le {S : ℕ} (clauses : Fin S → Clause V)
    (Low : Fin S → Prop) : (distinctFlats clauses Low).card ≤ S := by
  classical
  calc
    (distinctFlats clauses Low).card ≤ (nonemptyDiscardedNodes clauses Low).card :=
      Finset.card_image_le
    _ ≤ Fintype.card (Fin S) := Finset.card_le_univ _
    _ = S := Fintype.card_fin S

/-- The Boolean dimension budget is monotone in the number of coordinates,
including degrees above either coordinate count. -/
theorem booleanBudget_mono (k : ℕ) {n m : ℕ} (hnm : n ≤ m) :
    BooleanFunctionSpace.booleanBudget k n ≤ BooleanFunctionSpace.booleanBudget k m := by
  classical
  have hn := BooleanFunctionSpace.card_lowSupports (W := Fin n) k
  have hm := BooleanFunctionSpace.card_lowSupports (W := Fin m) k
  simp only [Fintype.card_fin] at hn hm
  rw [← hn, ← hm]
  apply Finset.card_le_card_of_injOn (fun A : Finset (Fin n) => A.image (Fin.castLE hnm))
  · intro A hA
    simp only [Finset.mem_coe, BooleanFunctionSpace.mem_lowSupports] at hA ⊢
    exact Finset.card_image_le.trans hA
  · intro A _ B _ h
    exact Finset.image_injective (Fin.castLE_injective hnm) h

variable [DecidableEq V] {S k R : ℕ}

/-- The paper's rank-profile dimension bound, now indexed by actual distinct
falsity flats. All coverage and chart hypotheses are discharged internally. -/
theorem affine_clause_distinct_budget
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
      ∑ Z : distinctFlats clauses Low,
        BooleanFunctionSpace.booleanBudget k
          (Fintype.card V - spanRank (clauses (representative clauses Low Z))) := by
  classical
  let A := ↥(distinctFlats clauses Low)
  let rep (Z : A) := representative clauses Low Z
  let hne (Z : A) : ∃ x, clauseZero (clauses (rep Z)) x :=
    (representative_spec clauses Low Z).1.2
  let t (Z : A) := Fintype.card V - spanRank (clauses (rep Z))
  let g (Z : A) : V → Poly (Fin (t Z)) :=
    optimalCoordinates (clauses (rep Z)) (hAffine (rep Z)) (hne Z)
  have hg : ∀ Z v, (g Z v).totalDegree ≤ 1 :=
    fun Z => (optimalCoordinates_spec (clauses (rep Z)) (hAffine (rep Z)) (hne Z)).1
  have hcover : ∀ i, ¬ Low i → ∀ x : V → BinaryField,
      clauseZero (clauses i) x →
        ∃ Z : A, ∃ y : Fin (t Z) → BinaryField,
          AffineRestriction.coordinateMap (g Z) y = x := by
    intro i hi x hx
    let Z : A := ⟨zeroSet (clauses i),
      (mem_distinctFlats clauses Low _).mpr ⟨i, ⟨hi, x, hx⟩, rfl⟩⟩
    refine ⟨Z, ?_⟩
    apply ((optimalCoordinates_spec (clauses (rep Z)) (hAffine (rep Z)) (hne Z)).2.2 x).mpr
    change x ∈ zeroSet (clauses (rep Z))
    rw [(representative_spec clauses Low Z).2]
    exact hx
  exact ParametrizedDAGDimension.affine_clause_restriction_budget hbool clauses initial dag
    hAffine Low hinputWidth hderivedRank finish hfinish U hU t g hg hcover

/-- Separation gives a distinct-flat rank-profile bound, not merely a count of
node occurrences. Separation is not inferred from a refutation-degree bound. -/
theorem affine_clause_separated_distinct_budget
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
      ∑ Z : distinctFlats clauses Low,
        BooleanFunctionSpace.booleanBudget k
          (Fintype.card V - spanRank (clauses (representative clauses Low Z))) := by
  have hdim := affine_clause_distinct_budget hbool clauses initial dag hAffine Low
    hinputWidth hderivedRank finish hfinish U hU
  have hinter : U ⊓ MathResearch.PolynomialCalculus.pcSpace F (k + 3 * R) = ⊥ := by
    apply le_antisymm
    · intro p hp
      simpa using hsep p hp.1 hp.2
    · exact bot_le
  rw [hinter, finrank_bot, zero_add] at hdim
  exact hdim

/-- A uniform bound on the number of distinct nonempty high-rank zero-flats.
The multiplication form remains meaningful even for an empty variable type. -/
theorem affine_clause_separated_distinct_count
    {F : Set (Poly V)}
    (hbool : (MathResearch.PolynomialCalculus.booleanBase : Set (Poly V)) ⊆ F)
    (clauses : Fin S → Clause V) (initial : Fin S → Bool)
    (dag : AffineClauseDAG.ClauseDAG F clauses initial)
    (hAffine : ∀ i, IsAffineClause (clauses i))
    (hinputWidth : ∀ i, initial i = true → (clauses i).card ≤ R)
    (finish : Fin S) (hfinish : clauses finish = ∅)
    (U : Submodule BinaryField (Poly V))
    (hU : ∀ p ∈ U, p.totalDegree ≤ k)
    (hsep : ∀ p ∈ U, MathResearch.PolynomialCalculus.Derives F (k + 3 * R) p → p = 0) :
    Module.finrank BinaryField U ≤
      (distinctFlats clauses (fun i => spanRank (clauses i) ≤ R)).card *
        BooleanFunctionSpace.booleanBudget k (Fintype.card V - R - 1) := by
  classical
  let Low := fun i => spanRank (clauses i) ≤ R
  have hdim := affine_clause_separated_distinct_budget hbool clauses initial dag hAffine Low
    hinputWidth (fun _ _ h => h) finish hfinish U hU hsep
  calc
    Module.finrank BinaryField U ≤ _ := hdim
    _ ≤ ∑ _Z : distinctFlats clauses Low,
        BooleanFunctionSpace.booleanBudget k (Fintype.card V - R - 1) := by
      apply Finset.sum_le_sum
      intro Z _
      have hs := representative_spec clauses Low Z
      have hr : R < spanRank (clauses (representative clauses Low Z)) :=
        Nat.lt_of_not_ge hs.1.1
      exact booleanBudget_mono k
        (parameterCount_le_of_high_rank _ (hAffine _) hs.1.2 R hr).2
    _ = _ := by simp [Low]

/-- The distinct-flat bound also lower-bounds the total number of source lines. -/
theorem affine_clause_separated_line_count
    {F : Set (Poly V)}
    (hbool : (MathResearch.PolynomialCalculus.booleanBase : Set (Poly V)) ⊆ F)
    (clauses : Fin S → Clause V) (initial : Fin S → Bool)
    (dag : AffineClauseDAG.ClauseDAG F clauses initial)
    (hAffine : ∀ i, IsAffineClause (clauses i))
    (hinputWidth : ∀ i, initial i = true → (clauses i).card ≤ R)
    (finish : Fin S) (hfinish : clauses finish = ∅)
    (U : Submodule BinaryField (Poly V))
    (hU : ∀ p ∈ U, p.totalDegree ≤ k)
    (hsep : ∀ p ∈ U, MathResearch.PolynomialCalculus.Derives F (k + 3 * R) p → p = 0) :
    Module.finrank BinaryField U ≤
      S * BooleanFunctionSpace.booleanBudget k (Fintype.card V - R - 1) := by
  exact (affine_clause_separated_distinct_count hbool clauses initial dag hAffine
    hinputWidth finish hfinish U hU hsep).trans
    (Nat.mul_le_mul_right _ (card_distinctFlats_le clauses _))

end

end BoundaryLab.DistinctAffineFlats
