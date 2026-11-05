import ProofLab.BooleanFunctionSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Actual Boolean restrictions along affine coordinate polynomials

Coordinate polynomials `g v` give a concrete map from parameter assignments to
original-variable assignments. Restriction is a genuine linear map into Boolean
functions. Its kernel is proved to mean pointwise vanishing on the image, and
its image on degree-at-most-k polynomials has the squarefree Boolean budget.

The total-degree estimate uses Mathlib's ordinary substitution expansion and
ordinary product degrees. Boolean reduction is used only in the imported
function-space theorem. In particular, raw ordinary affine substitution is not
silently assigned a squarefree polynomial dimension.

No injectivity is required of the coordinate map. The numerical budget uses
the parameter count, with affineness explicitly required in the image-bound
theorems. This file does not identify that count with the intrinsic dimension
of a clause zero-flat, or identify any codimension with affine-clause rank.
-/

set_option autoImplicit false

namespace BoundaryLab.AffineRestriction

noncomputable section

open MvPolynomial
open scoped BigOperators

abbrev Poly (V : Type) := MvPolynomial V (ZMod 2)

variable {V W : Type}

/-- The actual assignment map represented by the coordinate polynomials. -/
def coordinateMap (g : V → Poly W) (y : W → ZMod 2) : V → ZMod 2 :=
  fun v => eval y (g v)

/-- Ordinary polynomial substitution, before Boolean reduction. -/
def ordinarySubstitution (g : V → Poly W) : Poly V →ₐ[ZMod 2] Poly W :=
  aeval g

/-- Substitution by degree-at-most-one coordinate polynomials does not increase
ordinary total degree. No finite variable-type hypothesis is needed here. -/
theorem ordinarySubstitution_degree (g : V → Poly W)
    (hg : ∀ v, (g v).totalDegree ≤ 1) (p : Poly V) :
    (ordinarySubstitution g p).totalDegree ≤ p.totalDegree := by
  classical
  change (eval₂ C g p).totalDegree ≤ p.totalDegree
  rw [eval₂_eq]
  apply totalDegree_finsetSum_le
  intro d hd
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add]
  apply (totalDegree_finsetProd _ _).trans
  calc
    (∑ v ∈ d.support, (g v ^ d v).totalDegree) ≤ ∑ v ∈ d.support, d v := by
      apply Finset.sum_le_sum
      intro v _
      exact (totalDegree_pow (g v) (d v)).trans
        (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (d v) (hg v))
    _ = d.sum (fun _ n => n) := rfl
    _ ≤ p.totalDegree := le_totalDegree hd

/-- Evaluating the substituted ordinary polynomial is exactly evaluation at
the represented assignment. This identity does not require affineness. -/
theorem ordinarySubstitution_eval (g : V → Poly W) (p : Poly V)
    (y : W → ZMod 2) :
    eval y (ordinarySubstitution g p) = eval (coordinateMap g y) p := by
  change aeval y (aeval g p) = _
  rw [comp_aeval_apply]
  rfl

/-- Restriction into actual functions on the parameter cube. Linearity comes
from ordinary algebra substitution followed by pointwise Boolean evaluation. -/
def restrictionLinear (g : V → Poly W) :
    Poly V →ₗ[ZMod 2] ((W → ZMod 2) → ZMod 2) :=
  BooleanFunctionSpace.booleanEval.comp (ordinarySubstitution g).toLinearMap

@[simp] theorem restrictionLinear_apply (g : V → Poly W) (p : Poly V)
    (y : W → ZMod 2) :
    restrictionLinear g p y = eval (coordinateMap g y) p :=
  ordinarySubstitution_eval g p y

/-- Zero in the function codomain means vanishing at every parameter point. -/
theorem restrictionLinear_eq_zero_iff (g : V → Poly W) (p : Poly V) :
    restrictionLinear g p = 0 ↔
      ∀ y : W → ZMod 2, eval (coordinateMap g y) p = 0 := by
  constructor
  · intro h y
    have hy := congrFun h y
    simpa only [restrictionLinear_apply, Pi.zero_apply] using hy
  · intro h
    funext y
    exact (restrictionLinear_apply g p y).trans (h y)

/-- The actual restriction kernel is exactly pointwise vanishing on the image
of the represented assignment map, including noninjective parameterizations. -/
theorem mem_ker_restrictionLinear_iff (g : V → Poly W) (p : Poly V) :
    p ∈ (restrictionLinear g).ker ↔
      ∀ x ∈ Set.range (coordinateMap g), eval x p = 0 := by
  rw [LinearMap.mem_ker, restrictionLinear_eq_zero_iff]
  constructor
  · rintro h x ⟨y, rfl⟩
    exact h y
  · intro h y
    exact h (coordinateMap g y) ⟨y, rfl⟩

/-- The same concrete restriction map with domain a chosen polynomial
subspace. This is the map used in the joint-kernel dimension argument. -/
def restrictionOn (U : Submodule (ZMod 2) (Poly V)) (g : V → Poly W) :
    U →ₗ[ZMod 2] ((W → ZMod 2) → ZMod 2) :=
  (restrictionLinear g).comp U.subtype

@[simp] theorem restrictionOn_apply (U : Submodule (ZMod 2) (Poly V))
    (g : V → Poly W) (p : U) (y : W → ZMod 2) :
    restrictionOn U g p y = eval (coordinateMap g y) p.val :=
  restrictionLinear_apply g p.val y

theorem restrictionOn_eq_zero_iff (U : Submodule (ZMod 2) (Poly V))
    (g : V → Poly W) (p : U) :
    restrictionOn U g p = 0 ↔
      ∀ y : W → ZMod 2, eval (coordinateMap g y) p.val = 0 :=
  restrictionLinear_eq_zero_iff g p.val

section FiniteParameters

variable [Fintype W] [DecidableEq W]

/-- Degree-bounded original polynomials restrict into the actual low-degree
Boolean function space. Squarefree reduction is accounted for by its proved
evaluation theorem, rather than an assumption about ordinary substitution. -/
theorem restrictionOn_range_le (U : Submodule (ZMod 2) (Poly V))
    (g : V → Poly W) (hg : ∀ v, (g v).totalDegree ≤ 1) (k : ℕ)
    (hU : ∀ p ∈ U, p.totalDegree ≤ k) :
    (restrictionOn U g).range ≤
      BooleanFunctionSpace.lowDegreeFunctions (W := W) k := by
  rintro z ⟨p, rfl⟩
  change BooleanFunctionSpace.booleanEval (ordinarySubstitution g p.val) ∈ _
  exact BooleanFunctionSpace.eval_mem_lowDegreeFunctions
    (ordinarySubstitution g p.val) k
    ((ordinarySubstitution_degree g hg p.val).trans (hU p.val p.property))

/-- The actual restriction-image dimension satisfies the squarefree Boolean
budget. Affineness and the source degree bound are hypotheses; the numerical
image bound itself is proved. The parameterization need not be injective. -/
theorem finrank_restrictionOn_le (U : Submodule (ZMod 2) (Poly V))
    (g : V → Poly W) (hg : ∀ v, (g v).totalDegree ≤ 1) (k : ℕ)
    (hU : ∀ p ∈ U, p.totalDegree ≤ k) :
    Module.finrank (ZMod 2) (restrictionOn U g).range ≤
      BooleanFunctionSpace.booleanBudget k (Fintype.card W) := by
  exact (Submodule.finrank_mono (restrictionOn_range_le U g hg k hU)).trans
    (BooleanFunctionSpace.finrank_lowDegreeFunctions_le (W := W) k)

end FiniteParameters

end

end BoundaryLab.AffineRestriction
