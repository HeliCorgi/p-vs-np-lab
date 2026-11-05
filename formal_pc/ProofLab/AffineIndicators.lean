/-
Phase 21: actual ordinary-polynomial indicators for finite binary affine clauses.

Every clause is a finite set of ordinary polynomials in the original variable
type.  Affineness means total degree at most one.  The indicator is constructed
as a product, and its semantics and degree are proved rather than assumed.

`spanRank` is the dimension of the span of the affine polynomials, including
their constant coordinates.  This file does not identify that rank with the
codimension of an affine zero-flat, and does not assert any P versus NP result.

The finite-basis extraction uses Mathlib's `exists_linearIndependent` and
`finrank_span_finset_eq_card`.  The ordinary-PC correction uses the explicitly
vendored MIT-licensed Boolean-reduction and PC-reuse theorems.
-/
import claims.BooleanReduction
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.FinCases

namespace BoundaryLab.AffineIndicators

noncomputable section
open MvPolynomial
open scoped BigOperators

abbrev BinaryField := ZMod 2
abbrev Poly (V : Type*) := MvPolynomial V BinaryField
abbrev Clause (V : Type*) := Finset (Poly V)

-- The pinned Boolean-reduction theorem is stated for universe-zero variables.
-- This includes every finite variable type used by the research construction.
variable {V : Type}

/-- A finite disjunction of affine forms over the original variables. -/
def IsAffineClause (C : Clause V) : Prop :=
  ∀ p ∈ C, p.totalDegree ≤ 1

/-- A clause is true when at least one of its binary affine forms is one. -/
def clauseHolds (C : Clause V) (x : V → BinaryField) : Prop :=
  ∃ p ∈ C, eval x p = 1

/-- The zero-flat of a clause, with no nonemptiness assumption. -/
def clauseZero (C : Clause V) (x : V → BinaryField) : Prop :=
  ∀ p ∈ C, eval x p = 0

/-- The raw, unreduced ordinary polynomial.  Repeated powers are retained. -/
def falsityPolynomial (C : Clause V) : Poly V :=
  ∏ p ∈ C, (1 - p)

/-- Rank of the span of the affine polynomials, with constants retained. -/
def spanRank (C : Clause V) : ℕ :=
  Module.finrank BinaryField (Submodule.span BinaryField (C : Set (Poly V)))

theorem binary_eq_zero_or_one (a : BinaryField) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem eval_falsityPolynomial_eq_zero (C : Clause V) (x : V → BinaryField) :
    eval x (falsityPolynomial C) = 0 ↔ clauseHolds C x := by
  classical
  change eval x (∏ p ∈ C, (1 - p)) = 0 ↔ ∃ p ∈ C, eval x p = 1
  rw [map_prod]
  simp only [map_sub, map_one, Finset.prod_eq_zero_iff, sub_eq_zero]
  constructor
  · rintro ⟨p, hp, h⟩
    exact ⟨p, hp, h.symm⟩
  · rintro ⟨p, hp, h⟩
    exact ⟨p, hp, h.symm⟩

theorem eval_falsityPolynomial_of_zero (C : Clause V) (x : V → BinaryField)
    (h : clauseZero C x) : eval x (falsityPolynomial C) = 1 := by
  classical
  simp only [falsityPolynomial, map_prod, map_sub, map_one]
  apply Finset.prod_eq_one
  intro p hp
  rw [h p hp, sub_zero]

theorem eval_falsityPolynomial_eq_one (C : Clause V) (x : V → BinaryField) :
    eval x (falsityPolynomial C) = 1 ↔ clauseZero C x := by
  constructor
  · intro h p hp
    rcases binary_eq_zero_or_one (eval x p) with hz | ho
    · exact hz
    · have he := (eval_falsityPolynomial_eq_zero C x).mpr ⟨p, hp, ho⟩
      exact False.elim (one_ne_zero (h.symm.trans he))
  · exact eval_falsityPolynomial_of_zero C x

theorem eval_falsityPolynomial (C : Clause V) (x : V → BinaryField)
    [Decidable (clauseZero C x)] :
    eval x (falsityPolynomial C) = if clauseZero C x then 1 else 0 := by
  classical
  by_cases h : clauseZero C x
  · simpa only [if_pos h] using eval_falsityPolynomial_of_zero C x h
  · simp only [if_neg h]
    rcases binary_eq_zero_or_one (eval x (falsityPolynomial C)) with hz | ho
    · exact hz
    · exact False.elim (h ((eval_falsityPolynomial_eq_one C x).mp ho))

theorem falsityPolynomial_degree (C : Clause V) (hC : IsAffineClause C) :
    (falsityPolynomial C).totalDegree ≤ C.card := by
  classical
  calc
    (falsityPolynomial C).totalDegree ≤ ∑ p ∈ C, (1 - p).totalDegree :=
      totalDegree_finsetProd C (fun p => 1 - p)
    _ ≤ ∑ _p ∈ C, 1 := by
      apply Finset.sum_le_sum
      intro p hp
      exact (totalDegree_sub 1 p).trans (max_le (by simp) (hC p hp))
    _ = C.card := by simp

/-- Evaluation is linear in an ordinary polynomial, so common zeros survive
passing from generators to their entire linear span. -/
theorem clauseZero_span (C : Clause V) (x : V → BinaryField)
    (h : clauseZero C x) (p : Poly V)
    (hp : p ∈ Submodule.span BinaryField (C : Set (Poly V))) : eval x p = 0 := by
  let ev : Poly V →ₗ[BinaryField] BinaryField := {
    toFun := fun q => eval x q
    map_add' := by intros; simp
    map_smul' := by intros; simp [MvPolynomial.smul_eq_C_mul]
  }
  have hs : Submodule.span BinaryField (C : Set (Poly V)) ≤ ev.ker := by
    apply Submodule.span_le.mpr
    intro q hq
    exact h q hq
  exact hs hp

theorem clauseZero_iff_of_span_eq (B C : Clause V)
    (hspan : Submodule.span BinaryField (B : Set (Poly V)) =
      Submodule.span BinaryField (C : Set (Poly V))) (x : V → BinaryField) :
    clauseZero B x ↔ clauseZero C x := by
  constructor
  · intro h p hp
    apply clauseZero_span B x h p
    rw [hspan]
    exact Submodule.subset_span hp
  · intro h p hp
    apply clauseZero_span C x h p
    rw [← hspan]
    exact Submodule.subset_span hp

theorem eval_falsityPolynomial_of_span_eq (B C : Clause V)
    (hspan : Submodule.span BinaryField (B : Set (Poly V)) =
      Submodule.span BinaryField (C : Set (Poly V))) (x : V → BinaryField) :
    eval x (falsityPolynomial B) = eval x (falsityPolynomial C) := by
  classical
  simp only [eval_falsityPolynomial, clauseZero_iff_of_span_eq B C hspan x]

/-- A finite clause has a spanning subclause of exactly its span rank.
This is proved in the actual ordinary-polynomial vector space. -/
theorem exists_basis_subclause (C : Clause V) :
    ∃ B : Clause V, B ⊆ C ∧
      Submodule.span BinaryField (B : Set (Poly V)) =
        Submodule.span BinaryField (C : Set (Poly V)) ∧
      B.card = spanRank C := by
  classical
  obtain ⟨s, hs, hspan, hli⟩ :=
    exists_linearIndependent BinaryField (C : Set (Poly V))
  have hfinite : s.Finite := C.finite_toSet.subset hs
  let B : Clause V := hfinite.toFinset
  have hBC : B ⊆ C := by simpa [B] using hs
  have hspanB : Submodule.span BinaryField (B : Set (Poly V)) =
      Submodule.span BinaryField (C : Set (Poly V)) := by
    simpa [B] using hspan
  have hliSet : LinearIndepOn BinaryField id s := hli
  have hliB : LinearIndepOn BinaryField id (B : Set (Poly V)) := by
    simpa [B] using hliSet
  have hcard : Module.finrank BinaryField
      (Submodule.span BinaryField (B : Set (Poly V))) = B.card :=
    finrank_span_finset_eq_card hliB
  refine ⟨B, hBC, hspanB, ?_⟩
  rw [← hcard, hspanB]
  rfl

/-- A chosen basis subclause.  Its correctness is the preceding theorem. -/
def basisSubclause (C : Clause V) : Clause V :=
  Classical.choose (exists_basis_subclause C)

theorem basisSubclause_spec (C : Clause V) :
    basisSubclause C ⊆ C ∧
      Submodule.span BinaryField (basisSubclause C : Set (Poly V)) =
        Submodule.span BinaryField (C : Set (Poly V)) ∧
      (basisSubclause C).card = spanRank C :=
  Classical.choose_spec (exists_basis_subclause C)

/-- The compressed indicator remains an ordinary polynomial over V. -/
def compressedPolynomial (C : Clause V) : Poly V :=
  falsityPolynomial (basisSubclause C)

theorem compressedPolynomial_degree (C : Clause V) (hC : IsAffineClause C) :
    (compressedPolynomial C).totalDegree ≤ spanRank C := by
  have hs := basisSubclause_spec C
  have hB : IsAffineClause (basisSubclause C) := fun p hp => hC p (hs.1 hp)
  simpa only [compressedPolynomial, hs.2.2] using
    falsityPolynomial_degree (basisSubclause C) hB

theorem compressedPolynomial_eval (C : Clause V) (x : V → BinaryField) :
    eval x (compressedPolynomial C) = eval x (falsityPolynomial C) :=
  eval_falsityPolynomial_of_span_eq (basisSubclause C) C
    (basisSubclause_spec C).2.1 x

theorem compressedPolynomial_eq_zero_iff (C : Clause V) (x : V → BinaryField) :
    eval x (compressedPolynomial C) = 0 ↔ clauseHolds C x := by
  rw [compressedPolynomial_eval, eval_falsityPolynomial_eq_zero]

theorem compressedPolynomial_eq_one_iff (C : Clause V) (x : V → BinaryField) :
    eval x (compressedPolynomial C) = 1 ↔ clauseZero C x := by
  rw [compressedPolynomial_eval, eval_falsityPolynomial_eq_one]

theorem spanRank_le_card (C : Clause V) : spanRank C ≤ C.card :=
  finrank_span_finset_le_card C

@[simp] theorem compressedPolynomial_empty :
    compressedPolynomial (∅ : Clause V) = 1 := by
  have h : basisSubclause (∅ : Clause V) = ∅ :=
    Finset.subset_empty.mp (basisSubclause_spec (∅ : Clause V)).1
  simp [compressedPolynomial, h, falsityPolynomial]

/-- Replacing a raw initial clause polynomial by its compressed indicator
costs at most the raw clause width in actual ordinary PC.  The Boolean
correction is derived from explicit Boolean axioms; equality of Boolean
functions is not treated as an ordinary-polynomial identity. -/
theorem compressedPolynomial_derivable [Fintype V]
    (F : Set (Poly V))
    (hbool : MathResearch.PolynomialCalculus.booleanBase ⊆ F)
    (C : Clause V) (hC : IsAffineClause C)
    (hinit : falsityPolynomial C ∈ F) :
    MathResearch.PolynomialCalculus.Derives F C.card (compressedPolynomial C) := by
  classical
  have hraw := falsityPolynomial_degree C hC
  have hcompressed := (compressedPolynomial_degree C hC).trans (spanRank_le_card C)
  have hdiff : (compressedPolynomial C - falsityPolynomial C).totalDegree ≤ C.card :=
    (totalDegree_sub _ _).trans (max_le hcompressed hraw)
  have heval : ∀ x : V → BinaryField,
      eval x (compressedPolynomial C - falsityPolynomial C) = 0 := by
    intro x
    rw [map_sub, compressedPolynomial_eval, sub_self]
  have hns := MathResearch.PolynomialCalculus.boolean_vanishing_ns_bound
    (compressedPolynomial C - falsityPolynomial C) C.card hdiff heval
  have hpc : MathResearch.PolynomialCalculus.Derives F C.card
      (compressedPolynomial C - falsityPolynomial C) :=
    MathResearch.PolynomialCalculus.nsSpace_le_pcSpace F C.card
      (MathResearch.PolynomialCalculus.nsSpace_mono hbool le_rfl hns)
  have hinput : MathResearch.PolynomialCalculus.Derives F C.card (falsityPolynomial C) :=
    .hyp hinit hraw
  simpa only [sub_add_cancel] using
    MathResearch.PolynomialCalculus.Derives.add hpc hinput

section Coefficients

variable [Fintype V]

/-- Explicit affine coefficient data produce an ordinary polynomial in V. -/
def affinePolynomial (constant : BinaryField) (coeff : V → BinaryField) : Poly V :=
  C constant + ∑ v, coeff v • X v

theorem affinePolynomial_eval (constant : BinaryField) (coeff x : V → BinaryField) :
    eval x (affinePolynomial constant coeff) = constant + ∑ v, coeff v * x v := by
  simp [affinePolynomial, MvPolynomial.smul_eq_C_mul]

theorem affinePolynomial_degree (constant : BinaryField) (coeff : V → BinaryField) :
    (affinePolynomial constant coeff).totalDegree ≤ 1 := by
  apply (totalDegree_add _ _).trans
  apply max_le
  · simp
  · apply totalDegree_finsetSum_le
    intro v _
    exact (totalDegree_smul_le _ _).trans (by simp)

end Coefficients

section CNF

/-- Positive literals are tagged `true`, negative literals `false`. -/
def literalForm (l : V × Bool) : Poly V :=
  if l.2 then X l.1 else 1 - X l.1

theorem literalForm_degree (l : V × Bool) : (literalForm l).totalDegree ≤ 1 := by
  rcases l with ⟨v, b⟩
  cases b
  · exact (totalDegree_sub 1 (X v)).trans (by simp)
  · simp [literalForm]

theorem literalForm_injective : Function.Injective (literalForm (V := V)) := by
  have hX : Function.Injective (X : V → Poly V) := MvPolynomial.X_injective
  rintro ⟨v, b⟩ ⟨w, c⟩ h
  cases b <;> cases c
  · change (1 - X v : Poly V) = 1 - X w at h
    have hv : (X v : Poly V) = X w := by
      have hcomp := congrArg (fun p : Poly V => 1 - p) h
      simpa only [sub_sub_cancel] using hcomp
    exact congrArg (fun u : V => (u, false)) (hX hv)
  · change (1 - X v : Poly V) = X w at h
    have hbad : (1 : BinaryField) = 0 := by
      simpa only [map_sub, map_one, eval_X, sub_zero] using
        congrArg (eval (fun _ : V => (0 : BinaryField))) h
    exact False.elim (one_ne_zero hbad)
  · change (X v : Poly V) = 1 - X w at h
    have hbad : (0 : BinaryField) = 1 := by
      simpa only [map_sub, map_one, eval_X, sub_zero] using
        congrArg (eval (fun _ : V => (0 : BinaryField))) h
    exact False.elim (zero_ne_one hbad)
  · change (X v : Poly V) = X w at h
    exact congrArg (fun u : V => (u, true)) (hX h)

/-- The finite affine clause corresponding to an ordinary CNF clause. -/
def cnfClause (L : Finset (V × Bool)) : Clause V := by
  classical
  exact L.image literalForm

theorem cnfClause_affine (L : Finset (V × Bool)) : IsAffineClause (cnfClause L) := by
  classical
  intro p hp
  obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hp
  exact literalForm_degree l

/-- Exact source-clause encoding, before any Boolean reduction. -/
theorem ordinary_cnf_initial_polynomial (L : Finset (V × Bool)) :
    (∏ l ∈ L, (1 - literalForm l)) =
      ∏ l ∈ L, (if l.2 then 1 - X l.1 else X l.1 : Poly V) := by
  classical
  apply Finset.prod_congr rfl
  intro l _
  rcases l with ⟨v, b⟩
  cases b <;> simp [literalForm]

/-- The generic affine-clause product is exactly the standard ordinary CNF
axiom.  This is an equality of unreduced polynomials, even for a clause
containing both polarities of a variable. -/
theorem cnfClause_falsityPolynomial (L : Finset (V × Bool)) :
    falsityPolynomial (cnfClause L) =
      ∏ l ∈ L, (if l.2 then 1 - X l.1 else X l.1 : Poly V) := by
  classical
  unfold falsityPolynomial cnfClause
  rw [Finset.prod_image]
  · exact ordinary_cnf_initial_polynomial L
  · intro a _ b _ h
    exact literalForm_injective h

end CNF
end
end BoundaryLab.AffineIndicators
