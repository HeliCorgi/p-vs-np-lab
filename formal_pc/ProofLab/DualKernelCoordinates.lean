import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Coordinates for the common kernel of a dual subspace

For a subspace `S` of the dual of a finite-dimensional vector space `E`,
the common kernel has dimension `finrank E - finrank S`. This module exposes
that standard annihilator theorem together with a linear equivalence from a
coordinate space of exactly that dimension.

The equivalence uses a chosen basis. It is a mathematical construction, not an
implementation of Gaussian elimination. Zero-dimensional spaces are included.
No finiteness assumption on the field or a nonzero-dimension assumption is used.
-/

namespace BoundaryLab.DualKernelCoordinates

noncomputable section

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

/-- The vectors annihilated by every linear functional in `S`. -/
abbrev commonKernel (S : Submodule K (Module.Dual K E)) : Submodule K E :=
  S.dualCoannihilator

@[simp]
theorem mem_commonKernel (S : Submodule K (Module.Dual K E)) (x : E) :
    x ∈ commonKernel S ↔ ∀ φ ∈ S, φ x = 0 :=
  Submodule.mem_dualCoannihilator x

variable [FiniteDimensional K E]

/-- The independent dual constraints and their common kernel account for the
entire ambient dimension. -/
theorem finrank_add_finrank_commonKernel (S : Submodule K (Module.Dual K E)) :
    Module.finrank K S + Module.finrank K (commonKernel S) = Module.finrank K E :=
  Subspace.finrank_add_finrank_dualCoannihilator_eq S

/-- A dual subspace has rank at most the ambient dimension. -/
theorem finrank_le (S : Submodule K (Module.Dual K E)) :
    Module.finrank K S ≤ Module.finrank K E := by
  calc
    Module.finrank K S ≤ Module.finrank K S +
        Module.finrank K (commonKernel S) := Nat.le_add_right _ _
    _ = Module.finrank K E := finrank_add_finrank_commonKernel S

/-- The exact common-kernel dimension, with natural subtraction justified by
the preceding rank bound. -/
theorem finrank_commonKernel (S : Submodule K (Module.Dual K E)) :
    Module.finrank K (commonKernel S) = Module.finrank K E - Module.finrank K S := by
  rw [← finrank_add_finrank_commonKernel S, Nat.add_sub_cancel_left]

/-- Linear coordinates on the common kernel, using exactly the ambient
dimension minus the independent-constraint rank. -/
def coordinateEquiv (S : Submodule K (Module.Dual K E)) :
    (Fin (Module.finrank K E - Module.finrank K S) → K) ≃ₗ[K] commonKernel S :=
  (Module.finBasisOfFinrankEq K (commonKernel S) (finrank_commonKernel S)).equivFun.symm

/-- Every coordinate vector gives a solution to all dual constraints. -/
theorem coordinateEquiv_annihilates (S : Submodule K (Module.Dual K E))
    (y : Fin (Module.finrank K E - Module.finrank K S) → K) :
    ∀ φ ∈ S, φ (coordinateEquiv S y).val = 0 :=
  (mem_commonKernel S _).mp (coordinateEquiv S y).property

/-- Every solution of the dual constraints has a unique coordinate vector. -/
theorem existsUnique_coordinates (S : Submodule K (Module.Dual K E)) (x : E)
    (hx : ∀ φ ∈ S, φ x = 0) :
    ∃! y : Fin (Module.finrank K E - Module.finrank K S) → K,
      (coordinateEquiv S y).val = x := by
  let z : commonKernel S := ⟨x, (mem_commonKernel S x).mpr hx⟩
  refine ⟨(coordinateEquiv S).symm z, ?_, ?_⟩
  · exact congrArg Subtype.val ((coordinateEquiv S).apply_symm_apply z)
  · intro y hy
    apply (coordinateEquiv S).injective
    apply Subtype.ext
    simpa only [LinearEquiv.apply_symm_apply] using hy

end

end BoundaryLab.DualKernelCoordinates
