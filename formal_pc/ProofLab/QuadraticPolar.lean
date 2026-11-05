import ProofLab.DualKernelCoordinates
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Tactic.Ring

/-!
# Polar rank of the binary inner-product quadratic

The function `quadratic (x,y) = sum i, x i * y i` has an explicit
nondegenerate polar pairing. Every affine subspace on which the function is
constant has a totally isotropic direction space, hence dimension at most
the number of coordinate pairs.

This module constructs the pairing and proves its injectivity. Nondegeneracy,
the isotropic property, and the dimension bound are not supplied as numerical
hypotheses. The bound here is valid for either constant level, including zero;
the sharper nonzero-level bound requires an additional argument.
-/

set_option autoImplicit false

namespace BoundaryLab.QuadraticPolar

noncomputable section

open scoped BigOperators

abbrev F2 := ZMod 2
abbrev Point (W : Type) := (W → F2) × (W → F2)

variable {W : Type} [Fintype W]

/-- The binary inner-product quadratic, as an actual function on assignments. -/
def quadratic (z : Point W) : F2 := ∑ i, z.1 i * z.2 i

/-- Its explicit symmetric polar pairing. -/
def polar (a b : Point W) : F2 :=
  ∑ i, a.1 i * b.2 i + b.1 i * a.2 i

theorem quadratic_add (a b : Point W) :
    quadratic (a + b) = quadratic a + quadratic b + polar a b := by
  unfold quadratic polar
  change (∑ i, (a.1 i + b.1 i) * (a.2 i + b.2 i)) =
    (∑ i, a.1 i * a.2 i) + (∑ i, b.1 i * b.2 i) +
      ∑ i, a.1 i * b.2 i + b.1 i * a.2 i
  simp only [add_mul, mul_add, Finset.sum_add_distrib]
  ring

/-- Fixing the first argument gives a genuine linear functional. -/
def polarFunctional (a : Point W) : Module.Dual F2 (Point W) where
  toFun := polar a
  map_add' b c := by
    simp [polar, add_mul, mul_add, Finset.sum_add_distrib,
      add_assoc, add_left_comm, add_comm]
  map_smul' c b := by
    simp [polar, smul_eq_mul, mul_add, Finset.mul_sum,
      mul_assoc, mul_left_comm]

/-- The polar pairing as a linear map into the actual dual assignment space. -/
def polarDual : Point W →ₗ[F2] Module.Dual F2 (Point W) where
  toFun := polarFunctional
  map_add' a b := by
    ext z
    simp [polarFunctional, polar, add_mul, mul_add, Finset.sum_add_distrib,
      add_assoc, add_left_comm, add_comm]
  map_smul' c a := by
    ext z
    simp [polarFunctional, polar, smul_eq_mul, mul_add, Finset.mul_sum,
      mul_assoc, mul_left_comm]

@[simp]
theorem polarDual_apply (a b : Point W) : polarDual a b = polar a b := rfl

theorem polar_add_right (a b c : Point W) :
    polar a (b + c) = polar a b + polar a c :=
  (polarFunctional a).map_add b c

/-- Unit-coordinate probes recover both halves of an assignment. -/
theorem polarDual_injective : Function.Injective (polarDual (W := W)) := by
  classical
  intro a b hab
  apply Prod.ext
  · funext j
    have h := congrArg
      (fun φ : Module.Dual F2 (Point W) =>
        φ (0, fun i => if j = i then 1 else 0)) hab
    simpa [polar, mul_ite, ite_mul] using h
  · funext j
    have h := congrArg
      (fun φ : Module.Dual F2 (Point W) =>
        φ ((fun i => if j = i then 1 else 0), 0)) hab
    simpa [polar, mul_ite, ite_mul] using h

/-- The explicit polar map is a linear equivalence onto the whole dual. -/
def polarEquiv : Point W ≃ₗ[F2] Module.Dual F2 (Point W) :=
  LinearEquiv.ofInjectiveOfFinrankEq polarDual polarDual_injective (by simp)

@[simp]
theorem polarEquiv_apply (a : Point W) : polarEquiv a = polarDual a := rfl

theorem polarDual_surjective : Function.Surjective (polarDual (W := W)) :=
  (polarEquiv (W := W)).surjective

/-- The second finite difference is the explicit polar pairing. -/
theorem quadratic_second_difference (a u v : Point W) :
    quadratic (a + (u + v)) - quadratic (a + u) - quadratic (a + v) +
      quadratic a = polar u v := by
  rw [quadratic_add a (u + v), quadratic_add u v, quadratic_add a u,
    quadratic_add a v, polar_add_right]
  ring

/-- Constancy on an affine translate forces its direction to be totally
isotropic. The value may be zero or one. -/
theorem constant_on_translate_isotropic
    (U : Submodule F2 (Point W)) (a : Point W) (c : F2)
    (hconstant : ∀ u ∈ U, quadratic (a + u) = c) :
    ∀ u ∈ U, ∀ v ∈ U, polar u v = 0 := by
  have hzero : quadratic a = c := by
    simpa using hconstant 0 U.zero_mem
  intro u hu v hv
  have h := quadratic_second_difference a u v
  rw [hconstant (u + v) (U.add_mem hu hv), hconstant u hu,
    hconstant v hv, hzero] at h
  simpa using h.symm

/-- The polar image of a direction space, inside the ambient dual. -/
def polarImage (U : Submodule F2 (Point W)) :
    Submodule F2 (Module.Dual F2 (Point W)) := U.map polarDual

theorem finrank_polarImage (U : Submodule F2 (Point W)) :
    Module.finrank F2 (polarImage U) = Module.finrank F2 U := by
  let f := polarDual.domRestrict U
  have hf : Function.Injective f := by
    intro u v huv
    apply Subtype.ext
    exact polarDual_injective huv
  have hrange : f.range = polarImage U := by
    ext φ
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u.val, u.property, rfl⟩
    · rintro ⟨u, hu, hφ⟩
      exact ⟨⟨u, hu⟩, hφ⟩
  rw [← hrange]
  exact LinearMap.finrank_range_of_inj hf

/-- Isotropy is the precise containment needed for the common-kernel
dimension theorem. -/
theorem le_commonKernel_polarImage (U : Submodule F2 (Point W))
    (hiso : ∀ u ∈ U, ∀ v ∈ U, polar u v = 0) :
    U ≤ DualKernelCoordinates.commonKernel (polarImage U) := by
  intro v hv
  apply (DualKernelCoordinates.mem_commonKernel (polarImage U) v).mpr
  intro φ hφ
  obtain ⟨u, hu, rfl⟩ := hφ
  exact hiso u hu v hv

theorem finrank_point : Module.finrank F2 (Point W) = 2 * Fintype.card W := by
  simp [Point, Module.finrank_pi, two_mul]

/-- A totally isotropic subspace has at most half the ambient dimension. -/
theorem finrank_le_of_isotropic (U : Submodule F2 (Point W))
    (hiso : ∀ u ∈ U, ∀ v ∈ U, polar u v = 0) :
    Module.finrank F2 U ≤ Fintype.card W := by
  have hdim := DualKernelCoordinates.finrank_add_finrank_commonKernel (polarImage U)
  have hle := Submodule.finrank_mono (le_commonKernel_polarImage U hiso)
  rw [finrank_polarImage, finrank_point] at hdim
  omega

/-- Any affine flat of either constant quadratic value has direction dimension
at most the number of input pairs. -/
theorem finrank_le_of_constant_translate
    (U : Submodule F2 (Point W)) (a : Point W) (c : F2)
    (hconstant : ∀ u ∈ U, quadratic (a + u) = c) :
    Module.finrank F2 U ≤ Fintype.card W :=
  finrank_le_of_isotropic U (constant_on_translate_isotropic U a c hconstant)

/-- The same geometric obstruction for an actual injective affine chart. -/
theorem parameterCount_le_of_constant_affine {t : ℕ}
    (f : (Fin t → F2) →ᵃ[F2] Point W) (hf : Function.Injective f)
    (c : F2) (hconstant : ∀ y, quadratic (f y) = c) :
    t ≤ Fintype.card W := by
  let U := f.linear.range
  have hU : ∀ u ∈ U, quadratic (f 0 + u) = c := by
    rintro u ⟨y, rfl⟩
    have he : f 0 + f.linear y = f y := by
      have h := congrFun f.decomp y
      change f y = f.linear y + f 0 at h
      rw [add_comm]
      exact h.symm
    rw [he]
    exact hconstant y
  have hi : Function.Injective f.linear := f.linear_injective_iff.mpr hf
  have hdim : Module.finrank F2 f.linear.range = t := by
    rw [LinearMap.finrank_range_of_inj hi, Module.finrank_pi, Fintype.card_fin]
  have hbound := finrank_le_of_constant_translate U (f 0) c hU
  simpa only [U, hdim] using hbound

end

end BoundaryLab.QuadraticPolar
