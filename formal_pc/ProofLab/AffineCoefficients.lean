/-
Phase 23: recover the actual linear coefficients of affine polynomials.

The polynomial identity below is an identity in the ordinary polynomial ring,
not merely an equality of functions on the Boolean cube.  If a finite affine
clause has a common zero, discarding the constant coefficient is injective on
its polynomial span.  Its slope space therefore has exactly `spanRank C`
dimensions.  No such assertion is made for an inconsistent clause.
-/
import ProofLab.AffineIndicators
import Mathlib.Data.Finsupp.Weight
import Mathlib.LinearAlgebra.Dual.Defs

namespace BoundaryLab.AffineCoefficients

noncomputable section
open MvPolynomial
open AffineIndicators
open scoped BigOperators

variable {V : Type} [Fintype V]

/-- The degree-one coefficient vector, acting as a linear functional on points. -/
def linearPart (p : Poly V) : Module.Dual BinaryField (V → BinaryField) where
  toFun x := ∑ v, p.coeff (Finsupp.single v 1) * x v
  map_add' x y := by
    simp [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm, mul_assoc]

/-- Taking the linear part is itself linear in the ordinary polynomial. -/
def linearPartMap : Poly V →ₗ[BinaryField] Module.Dual BinaryField (V → BinaryField) where
  toFun := linearPart
  map_add' p q := by
    ext x
    simp [linearPart, add_mul, Finset.sum_add_distrib]
  map_smul' a p := by
    ext x
    simp [linearPart, smul_eq_mul, Finset.mul_sum, mul_assoc]

@[simp] theorem linearPartMap_apply (p : Poly V) :
    linearPartMap p = linearPart p := rfl

@[simp] theorem linearPart_apply (p : Poly V) (x : V → BinaryField) :
    linearPart p x = ∑ v, p.coeff (Finsupp.single v 1) * x v := rfl

/-- Every degree-at-most-one ordinary polynomial is exactly its affine
coefficient reconstruction, including on the empty variable type. -/
theorem eq_affinePolynomial (p : Poly V) (hp : p.totalDegree ≤ 1) :
    p = affinePolynomial (p.coeff 0) (fun v => p.coeff (Finsupp.single v 1)) := by
  classical
  apply MvPolynomial.ext
  intro d
  rcases lt_or_ge 1 d.degree with hd | hd
  · have hp0 : p.coeff d = 0 :=
      coeff_eq_zero_of_totalDegree_lt (hp.trans_lt hd)
    have hq0 :
        (affinePolynomial (p.coeff 0)
          (fun v => p.coeff (Finsupp.single v 1))).coeff d = 0 :=
      coeff_eq_zero_of_totalDegree_lt
        ((affinePolynomial_degree _ _).trans_lt hd)
    exact hp0.trans hq0.symm
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd with hd | hd
    · have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp hd
      subst d
      simp [affinePolynomial, coeff_sum]
    · change d.sum (fun _ k => k) = 1 at hd
      obtain ⟨v, rfl⟩ := (Finsupp.sum_eq_one_iff d).mp hd
      have hne : (0 : V →₀ ℕ) ≠ Finsupp.single v 1 := by
        intro h
        have hval : (0 : ℕ) = 1 := by
          simpa using congrArg (fun e : V →₀ ℕ => e v) h
        exact Nat.zero_ne_one hval
      simp [affinePolynomial, coeff_sum, coeff_single_X, smul_eq_mul, hne]

/-- Evaluation of a general affine polynomial is its constant plus its slope. -/
theorem eval_affine (p : Poly V) (hp : p.totalDegree ≤ 1) (x : V → BinaryField) :
    eval x p = p.coeff 0 + linearPart p x := by
  calc
    eval x p = eval x
        (affinePolynomial (p.coeff 0) (fun v => p.coeff (Finsupp.single v 1))) :=
      congrArg (eval x) (eq_affinePolynomial p hp)
    _ = p.coeff 0 + linearPart p x := affinePolynomial_eval _ _ _

/-- Translating the argument changes only the value of the linear part. -/
theorem eval_translate (p : Poly V) (hp : p.totalDegree ≤ 1)
    (a z : V → BinaryField) :
    eval (a + z) p = eval a p + linearPart p z := by
  rw [eval_affine p hp, eval_affine p hp, map_add, add_assoc]

/-- Total degree at most one is preserved by taking the clause's linear span. -/
theorem affine_span_degree (C : Clause V) (hC : IsAffineClause C) (p : Poly V)
    (hp : p ∈ Submodule.span BinaryField (C : Set (Poly V))) :
    p.totalDegree ≤ 1 := by
  have hs : Submodule.span BinaryField (C : Set (Poly V)) ≤
      restrictTotalDegree V BinaryField 1 := by
    apply Submodule.span_le.mpr
    intro q hq
    exact (mem_restrictTotalDegree _ _ _).mpr (hC q hq)
  exact (mem_restrictTotalDegree _ _ _).mp (hs hp)

private theorem coeff_single_of_linearPart_zero (p : Poly V)
    (hp : linearPart p = 0) (v : V) : p.coeff (Finsupp.single v 1) = 0 := by
  classical
  have h := congrArg
    (fun f : Module.Dual BinaryField (V → BinaryField) =>
      f (fun w => if v = w then 1 else 0)) hp
  simpa [linearPart, mul_ite] using h

/-- An affine polynomial with zero slope and a zero at one point is zero as
an ordinary polynomial.  Function equality alone is not used as a proxy. -/
theorem eq_zero_of_linearPart_zero_of_eval_zero (p : Poly V)
    (hp : p.totalDegree ≤ 1) (a : V → BinaryField)
    (hlinear : linearPart p = 0) (ha : eval a p = 0) : p = 0 := by
  have hc : p.coeff 0 = 0 := by
    simpa [eval_affine p hp a, hlinear] using ha
  have hcoeff : ∀ v, p.coeff (Finsupp.single v 1) = 0 :=
    coeff_single_of_linearPart_zero p hlinear
  rw [eq_affinePolynomial p hp]
  simp [affinePolynomial, hc, hcoeff]

/-- At a common zero, the constant is determined by the slope on the entire
affine polynomial span; hence the slope projection is injective there. -/
theorem linearPartMap_span_injective (C : Clause V) (hC : IsAffineClause C)
    (a : V → BinaryField) (ha : clauseZero C a) :
    Function.Injective
      (linearPartMap.domRestrict (Submodule.span BinaryField (C : Set (Poly V)))) := by
  intro p q hpq
  apply Subtype.ext
  apply sub_eq_zero.mp
  have hmem : (p : Poly V) - (q : Poly V) ∈
      Submodule.span BinaryField (C : Set (Poly V)) :=
    Submodule.sub_mem _ p.property q.property
  apply eq_zero_of_linearPart_zero_of_eval_zero _ (affine_span_degree C hC _ hmem) a
  · change linearPartMap ((p : Poly V) - (q : Poly V)) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hpq
  · exact clauseZero_span C a ha _ hmem

/-- The actual span of the slope functionals of the clause. -/
def slopeSpace (C : Clause V) : Submodule BinaryField (Module.Dual BinaryField (V → BinaryField)) :=
  (Submodule.span BinaryField (C : Set (Poly V))).map linearPartMap

theorem mem_slopeSpace_iff (C : Clause V)
    (f : Module.Dual BinaryField (V → BinaryField)) :
    f ∈ slopeSpace C ↔
      ∃ p ∈ Submodule.span BinaryField (C : Set (Poly V)), linearPart p = f := Iff.rfl

theorem linearPart_mem_slopeSpace (C : Clause V) (p : Poly V) (hp : p ∈ C) :
    linearPart p ∈ slopeSpace C :=
  ⟨p, Submodule.subset_span hp, rfl⟩

/-- For a consistent affine clause, its full polynomial span and its slope
space have equal finite dimensions.  Constants cause no extra rank. -/
theorem finrank_slopeSpace (C : Clause V) (hC : IsAffineClause C)
    (a : V → BinaryField) (ha : clauseZero C a) :
    Module.finrank BinaryField (slopeSpace C) = spanRank C := by
  let f := linearPartMap.domRestrict
    (Submodule.span BinaryField (C : Set (Poly V)))
  have hf : Function.Injective f := linearPartMap_span_injective C hC a ha
  have hrange : f.range = slopeSpace C := by
    ext y
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p, p.property, rfl⟩
    · rintro ⟨p, hp, hpy⟩
      exact ⟨⟨p, hp⟩, hpy⟩
  change Module.finrank BinaryField (slopeSpace C) =
    Module.finrank BinaryField (Submodule.span BinaryField (C : Set (Poly V)))
  rw [← hrange]
  exact (LinearEquiv.ofInjective f hf).finrank_eq.symm

end
end BoundaryLab.AffineCoefficients
