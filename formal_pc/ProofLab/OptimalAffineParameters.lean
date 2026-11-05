import ProofLab.AffineCoefficients
import ProofLab.DualKernelCoordinates
import ProofLab.AffineRestriction
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.Pi

/-!
# Exact affine coordinates for a nonempty clause zero-set

For an affine clause with a common zero, the rank of its full polynomial span
equals the rank of its linear constraints. Their common kernel has dimension
`Fintype.card V - spanRank C`. Translating a linear coordinate equivalence on
that kernel by the chosen common zero gives an injective affine map whose
image is exactly the clause's zero-set.

The same map is encoded by actual degree-at-most-one ordinary coordinate
polynomials, so it can be passed to the existing restriction theorems.
The construction uses a chosen basis and does not claim an executable
Gaussian-elimination algorithm. Empty variable types and zero-dimensional
zero-sets are included. No parameterization is asserted for an empty zero-set.
-/

set_option autoImplicit false

namespace BoundaryLab.OptimalAffineParameters

noncomputable section

open MvPolynomial AffineIndicators AffineCoefficients
open scoped BigOperators

variable {V W : Type}

section LinearEncoding

/-- Translation of an actual linear map, bundled as an affine map. -/
def translatedLinearMap (a : V → BinaryField)
    (L : (W → BinaryField) →ₗ[BinaryField] (V → BinaryField)) :
    (W → BinaryField) →ᵃ[BinaryField] (V → BinaryField) where
  toFun y := a + L y
  linear := L
  map_vadd' p v := by
    change a + L (v + p) = L v + (a + L p)
    rw [L.map_add]
    exact add_left_comm _ _ _

variable [Fintype W]

/-- The columns of `L`, together with the translation `a`, encoded as
ordinary affine coordinate polynomials on the parameter variables. -/
def coordinatePolynomials (a : V → BinaryField)
    (L : (W → BinaryField) →ₗ[BinaryField] (V → BinaryField)) : V → Poly W := by
  classical
  exact fun v => affinePolynomial (a v)
    (fun j => L (fun i => if j = i then 1 else 0) v)

theorem coordinatePolynomials_degree (a : V → BinaryField)
    (L : (W → BinaryField) →ₗ[BinaryField] (V → BinaryField)) (v : V) :
    (coordinatePolynomials a L v).totalDegree ≤ 1 := by
  classical
  exact affinePolynomial_degree _ _

/-- The polynomial encoding represents the actual translated linear map. -/
theorem coordinateMap_coordinatePolynomials (a : V → BinaryField)
    (L : (W → BinaryField) →ₗ[BinaryField] (V → BinaryField))
    (y : W → BinaryField) :
    AffineRestriction.coordinateMap (coordinatePolynomials a L) y = a + L y := by
  classical
  funext v
  change eval y (affinePolynomial (a v)
    (fun j => L (fun i => if j = i then 1 else 0) v)) = a v + L y v
  rw [affinePolynomial_eval]
  have hv := congrFun (LinearMap.pi_apply_eq_sum_univ L y) v
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hv
  rw [hv]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

end LinearEncoding

section ConsistentClause

variable [Fintype V]

/-- The translation directions satisfying every linear constraint of `C`. -/
abbrev direction (C : Clause V) : Submodule BinaryField (V → BinaryField) :=
  DualKernelCoordinates.commonKernel (slopeSpace C)

/-- Around any common zero, the clause zero-set is exactly a translate of
the common kernel of its slope space. -/
theorem clauseZero_add_iff (C : Clause V) (hC : IsAffineClause C)
    (a : V → BinaryField) (ha : clauseZero C a) (z : V → BinaryField) :
    clauseZero C (a + z) ↔ z ∈ direction C := by
  constructor
  · intro hz
    apply (DualKernelCoordinates.mem_commonKernel (slopeSpace C) z).mpr
    intro φ hφ
    obtain ⟨p, hp, rfl⟩ := (mem_slopeSpace_iff C φ).mp hφ
    have he := clauseZero_span C (a + z) hz p hp
    rw [eval_translate p (affine_span_degree C hC p hp) a z,
      clauseZero_span C a ha p hp, zero_add] at he
    exact he
  · intro hz p hp
    have he : linearPart p z = 0 :=
      (DualKernelCoordinates.mem_commonKernel (slopeSpace C) z).mp hz
        (linearPart p) (linearPart_mem_slopeSpace C p hp)
    rw [eval_translate p (hC p hp) a z, ha p hp, he, add_zero]

/-- Membership in the zero-set is tested by subtracting the chosen anchor. -/
theorem clauseZero_iff_sub_mem (C : Clause V) (hC : IsAffineClause C)
    (a : V → BinaryField) (ha : clauseZero C a) (x : V → BinaryField) :
    clauseZero C x ↔ x - a ∈ direction C := by
  have hx : a + (x - a) = x := by
    rw [add_comm a (x - a), sub_add_cancel]
  simpa only [hx] using clauseZero_add_iff C hC a ha (x - a)

/-- Consistency prevents the constant coordinate from contributing an extra
independent constraint beyond the number of variables. -/
theorem spanRank_le_card_variables_of_zero (C : Clause V) (hC : IsAffineClause C)
    (a : V → BinaryField) (ha : clauseZero C a) :
    spanRank C ≤ Fintype.card V := by
  simpa only [finrank_slopeSpace C hC a ha, Module.finrank_pi] using
    DualKernelCoordinates.finrank_le (slopeSpace C)

theorem spanRank_le_card_variables (C : Clause V) (hC : IsAffineClause C)
    (hne : ∃ a, clauseZero C a) : spanRank C ≤ Fintype.card V := by
  obtain ⟨a, ha⟩ := hne
  exact spanRank_le_card_variables_of_zero C hC a ha

/-- The exact intrinsic dimension, derived from polynomial rank preservation
and finite-dimensional duality. -/
theorem finrank_direction (C : Clause V) (hC : IsAffineClause C)
    (a : V → BinaryField) (ha : clauseZero C a) :
    Module.finrank BinaryField (direction C) = Fintype.card V - spanRank C := by
  simpa only [finrank_slopeSpace C hC a ha, Module.finrank_pi] using
    DualKernelCoordinates.finrank_commonKernel (slopeSpace C)

/-- Linear coordinates on the direction space with the required parameter
count. The codimension formula is proved before this equivalence is chosen. -/
def parameterLinearEquiv (C : Clause V) (hC : IsAffineClause C)
    (a : V → BinaryField) (ha : clauseZero C a) :
    (Fin (Fintype.card V - spanRank C) → BinaryField) ≃ₗ[BinaryField] direction C := by
  simpa only [finrank_slopeSpace C hC a ha, Module.finrank_pi] using
    DualKernelCoordinates.coordinateEquiv (slopeSpace C)

/-- Include the direction coordinates into the original assignment space. -/
def parameterLinearMap (C : Clause V) (hC : IsAffineClause C)
    (a : V → BinaryField) (ha : clauseZero C a) :
    (Fin (Fintype.card V - spanRank C) → BinaryField) →ₗ[BinaryField]
      (V → BinaryField) :=
  (direction C).subtype.comp (parameterLinearEquiv C hC a ha).toLinearMap

@[simp]
theorem parameterLinearMap_apply (C : Clause V) (hC : IsAffineClause C)
    (a : V → BinaryField) (ha : clauseZero C a)
    (y : Fin (Fintype.card V - spanRank C) → BinaryField) :
    parameterLinearMap C hC a ha y = (parameterLinearEquiv C hC a ha y).val := rfl

/-- The constructed affine map into the original assignment space. -/
def optimalAffineMap (C : Clause V) (hC : IsAffineClause C)
    (a : V → BinaryField) (ha : clauseZero C a) :
    (Fin (Fintype.card V - spanRank C) → BinaryField) →ᵃ[BinaryField]
      (V → BinaryField) :=
  translatedLinearMap a (parameterLinearMap C hC a ha)

/-- Ordinary affine coordinate polynomials for the constructed map. -/
def optimalCoordinates (C : Clause V) (hC : IsAffineClause C)
    (a : V → BinaryField) (ha : clauseZero C a) :
    V → Poly (Fin (Fintype.card V - spanRank C)) :=
  coordinatePolynomials a (parameterLinearMap C hC a ha)

theorem optimalCoordinates_degree (C : Clause V) (hC : IsAffineClause C)
    (a : V → BinaryField) (ha : clauseZero C a) (v : V) :
    (optimalCoordinates C hC a ha v).totalDegree ≤ 1 :=
  coordinatePolynomials_degree a (parameterLinearMap C hC a ha) v

theorem coordinateMap_optimalCoordinates (C : Clause V) (hC : IsAffineClause C)
    (a : V → BinaryField) (ha : clauseZero C a)
    (y : Fin (Fintype.card V - spanRank C) → BinaryField) :
    AffineRestriction.coordinateMap (optimalCoordinates C hC a ha) y =
      a + (parameterLinearEquiv C hC a ha y).val :=
  coordinateMap_coordinatePolynomials a (parameterLinearMap C hC a ha) y

/-- The constructed polynomial chart is the underlying function of the
constructed affine map, not merely an unrelated set parameterization. -/
theorem coordinateMap_eq_optimalAffineMap (C : Clause V) (hC : IsAffineClause C)
    (a : V → BinaryField) (ha : clauseZero C a) :
    AffineRestriction.coordinateMap (optimalCoordinates C hC a ha) =
      ⇑(optimalAffineMap C hC a ha) := by
  funext y
  exact coordinateMap_optimalCoordinates C hC a ha y

/-- Distinct parameter vectors produce distinct assignments. -/
theorem optimalCoordinates_injective (C : Clause V) (hC : IsAffineClause C)
    (a : V → BinaryField) (ha : clauseZero C a) :
    Function.Injective (AffineRestriction.coordinateMap (optimalCoordinates C hC a ha)) := by
  intro y z hyz
  rw [coordinateMap_optimalCoordinates, coordinateMap_optimalCoordinates] at hyz
  apply (parameterLinearEquiv C hC a ha).injective
  apply Subtype.ext
  exact add_left_cancel hyz

/-- The image is exactly the clause zero-set: no omitted assignments and no
additional assignments. -/
theorem optimalCoordinates_range (C : Clause V) (hC : IsAffineClause C)
    (a : V → BinaryField) (ha : clauseZero C a) (x : V → BinaryField) :
    (∃ y, AffineRestriction.coordinateMap (optimalCoordinates C hC a ha) y = x) ↔
      clauseZero C x := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [coordinateMap_optimalCoordinates]
    exact (clauseZero_add_iff C hC a ha _).mpr
      (parameterLinearEquiv C hC a ha y).property
  · intro hx
    let z : direction C := ⟨x - a, (clauseZero_iff_sub_mem C hC a ha x).mp hx⟩
    refine ⟨(parameterLinearEquiv C hC a ha).symm z, ?_⟩
    rw [coordinateMap_optimalCoordinates, LinearEquiv.apply_symm_apply]
    change a + (x - a) = x
    rw [add_comm a (x - a), sub_add_cancel]

/-- Each counterexample has exactly one parameter vector. -/
theorem optimalCoordinates_existsUnique (C : Clause V) (hC : IsAffineClause C)
    (a : V → BinaryField) (ha : clauseZero C a) (x : V → BinaryField) :
    clauseZero C x ↔
      ∃! y, AffineRestriction.coordinateMap (optimalCoordinates C hC a ha) y = x := by
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (optimalCoordinates_range C hC a ha x).mpr hx
    refine ⟨y, hy, ?_⟩
    intro z hz
    exact optimalCoordinates_injective C hC a ha (hz.trans hy.symm)
  · rintro ⟨y, hy, _⟩
    exact (optimalCoordinates_range C hC a ha x).mp ⟨y, hy⟩

/-- The requested exact affine parameterization by ordinary coordinate
polynomials. The zero-set's nonemptiness is the only existence premise. -/
theorem exists_optimal_parameterization (C : Clause V) (hC : IsAffineClause C)
    (hne : ∃ a, clauseZero C a) :
    ∃ g : V → Poly (Fin (Fintype.card V - spanRank C)),
      (∀ v, (g v).totalDegree ≤ 1) ∧
      Function.Injective (AffineRestriction.coordinateMap g) ∧
      ∀ x, (∃ y, AffineRestriction.coordinateMap g y = x) ↔ clauseZero C x := by
  obtain ⟨a, ha⟩ := hne
  exact ⟨optimalCoordinates C hC a ha, optimalCoordinates_degree C hC a ha,
    optimalCoordinates_injective C hC a ha, optimalCoordinates_range C hC a ha⟩

/-- The same result stated with a bundled affine map. -/
theorem exists_optimal_affineMap (C : Clause V) (hC : IsAffineClause C)
    (hne : ∃ a, clauseZero C a) :
    ∃ f : (Fin (Fintype.card V - spanRank C) → BinaryField) →ᵃ[BinaryField]
        (V → BinaryField),
      Function.Injective f ∧ ∀ x, (∃ y, f y = x) ↔ clauseZero C x := by
  obtain ⟨a, ha⟩ := hne
  refine ⟨optimalAffineMap C hC a ha, ?_, ?_⟩
  · rw [← coordinateMap_eq_optimalAffineMap C hC a ha]
    exact optimalCoordinates_injective C hC a ha
  · intro x
    rw [← coordinateMap_eq_optimalAffineMap C hC a ha]
    exact optimalCoordinates_range C hC a ha x

end ConsistentClause

end

end BoundaryLab.OptimalAffineParameters
