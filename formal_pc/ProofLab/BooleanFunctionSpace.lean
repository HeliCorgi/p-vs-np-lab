import claims.BooleanReduction
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Low-degree Boolean functions and their dimension budget

The target is the actual vector space of functions on the Boolean cube.
An ordinary polynomial of total degree at most `k` evaluates into the span
of squarefree support monomials involving at most `k` variables. The explicit
squarefree reduction from the pinned Boolean-reduction foundation proves this
membership; ordinary polynomials are not identified with their functions.

The dimension upper bound is proved by counting the finite set of supports,
partitioned by cardinality. It is valid for every natural degree and every
finite variable type, including zero variables and degree above the variable
count. No affine geometry or separated-space hypothesis occurs in this file.
-/

namespace BoundaryLab.BooleanFunctionSpace

noncomputable section

open MvPolynomial MathResearch.PolynomialCalculus
open scoped BigOperators

/-- The number of squarefree monomials of degree at most `k` on `t` variables. -/
def booleanBudget (k t : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (min k t + 1), t.choose j

variable {W : Type}

/-- Evaluation as a linear map to actual Boolean functions. -/
def booleanEval : MvPolynomial W (ZMod 2) →ₗ[ZMod 2] ((W → ZMod 2) → ZMod 2) where
  toFun p x := eval x p
  map_add' p q := by
    funext x
    exact map_add (eval x) p q
  map_smul' a p := by
    funext x
    simp [MvPolynomial.smul_eq_C_mul]

@[simp] theorem booleanEval_apply (p : MvPolynomial W (ZMod 2)) (x : W → ZMod 2) :
    booleanEval p x = eval x p := rfl

variable [Fintype W] [DecidableEq W]

/-- All variable supports of size at most `k`. -/
def lowSupports (k : ℕ) : Finset (Finset W) :=
  (Finset.univ : Finset W).powerset.filter (fun S => S.card ≤ k)

@[simp] theorem mem_lowSupports (S : Finset W) (k : ℕ) :
    S ∈ lowSupports (W := W) k ↔ S.card ≤ k := by
  simp [lowSupports]

/-- The support count is the explicit truncated binomial sum. -/
theorem card_lowSupports (k : ℕ) :
    (lowSupports (W := W) k).card = booleanBudget k (Fintype.card W) := by
  classical
  have hlayers : lowSupports (W := W) k =
      (Finset.range (min k (Fintype.card W) + 1)).biUnion
        (fun j => (Finset.univ : Finset W).powersetCard j) := by
    ext S
    simp only [mem_lowSupports, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_powersetCard]
    constructor
    · intro hS
      refine ⟨S.card, ?_, Finset.subset_univ S, rfl⟩
      have hcard : S.card ≤ Fintype.card W := Finset.card_le_univ S
      omega
    · rintro ⟨j, hj, _, hcard⟩
      omega
  rw [hlayers, Finset.card_biUnion
    ((Finset.univ : Finset W).pairwise_disjoint_powersetCard.set_pairwise _)]
  simp [booleanBudget]

/-- The span of evaluated squarefree monomials on the allowed supports. -/
def lowDegreeFunctions (k : ℕ) :
    Submodule (ZMod 2) ((W → ZMod 2) → ZMod 2) := by
  classical
  exact Submodule.span (ZMod 2)
    (((lowSupports (W := W) k).image
      (fun S => booleanEval (supportMonomial S))) : Set ((W → ZMod 2) → ZMod 2))

theorem supportMonomial_mem_lowDegreeFunctions (S : Finset W) (k : ℕ)
    (hS : S.card ≤ k) :
    booleanEval (supportMonomial S) ∈ lowDegreeFunctions (W := W) k := by
  classical
  apply Submodule.subset_span
  exact Finset.mem_image.mpr ⟨S, (mem_lowSupports S k).mpr hS, rfl⟩

private theorem support_card_le_sum (d : W →₀ ℕ) :
    d.support.card ≤ d.sum (fun _ n => n) := by
  classical
  change d.support.card ≤ ∑ i ∈ d.support, d i
  calc
    d.support.card = ∑ _i ∈ d.support, 1 := by simp
    _ ≤ ∑ i ∈ d.support, d i := Finset.sum_le_sum (fun i hi =>
      Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))

/-- Degree-at-most-`k` ordinary polynomials give low-degree Boolean functions.
The proof uses the explicit squarefree expansion and its evaluation theorem. -/
theorem eval_mem_lowDegreeFunctions (p : MvPolynomial W (ZMod 2)) (k : ℕ)
    (hp : p.totalDegree ≤ k) :
    booleanEval p ∈ lowDegreeFunctions (W := W) k := by
  classical
  have heval : booleanEval p = booleanEval (squarefreePart p) := by
    funext x
    exact (squarefreePart_eval p x).symm
  rw [heval, squarefreePart, map_sum]
  apply Submodule.sum_mem
  intro d hd
  rw [map_smul]
  apply Submodule.smul_mem
  apply supportMonomial_mem_lowDegreeFunctions
  exact ((support_card_le_sum d).trans (le_totalDegree hd)).trans hp

/-- A finite spanning family supplies the truncated binomial dimension bound.
The bound is proved, not supplied as an image-dimension hypothesis. -/
theorem finrank_lowDegreeFunctions_le (k : ℕ) :
    Module.finrank (ZMod 2) (lowDegreeFunctions (W := W) k) ≤
      booleanBudget k (Fintype.card W) := by
  classical
  calc
    Module.finrank (ZMod 2) (lowDegreeFunctions (W := W) k) ≤
        ((lowSupports (W := W) k).image
          (fun S => booleanEval (supportMonomial S))).card :=
      finrank_span_finset_le_card _
    _ ≤ (lowSupports (W := W) k).card := Finset.card_image_le
    _ = booleanBudget k (Fintype.card W) := card_lowSupports k

end

end BoundaryLab.BooleanFunctionSpace
