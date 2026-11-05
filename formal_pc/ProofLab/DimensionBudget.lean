import claims.PolynomialCalculus
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Dimension budgets for joint restriction kernels

This module proves the finite-dimensional linear algebra step of the affine-DAG
argument. The ambient vector space and the individual restriction codomains may
be infinite-dimensional: only the source subspace is finite-dimensional. The
joint map takes values in the product of the individual images.

The PC specialization uses the ordinary derivation relation and `pcSpace` from
the vendored foundations. A kernel-to-PC implication is an explicit hypothesis;
it is not replaced with an equality between PC and static Nullstellensatz.

No affine restriction image formula or separated-space construction is asserted
here. Such results must discharge the image bounds and separation hypotheses.

The kernel embedding and product-of-images argument follows standard
rank-nullity. Its application to ordinary PC also occurs in
`kbr-/math-research`, `claims/GenericAffineSubspaceConsequence.lean`, commit
`25239211058ef718402a908b3272f01480c159c4` (MIT).
-/

namespace BoundaryLab.DimensionBudget

noncomputable section

open scoped BigOperators

section LinearAlgebra

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- If the kernel of a map on `U` lies in `W`, only the part of `U` outside `W`
needs to fit in the codomain. No finiteness assumption is made on `V` or `W`. -/
theorem kernel_budget (U W : Submodule K V) [FiniteDimensional K U]
    {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    (T : U →ₗ[K] E)
    (hker : ∀ u : U, T u = 0 → (u : V) ∈ W) :
    Module.finrank K U ≤
      Module.finrank K ↥(U ⊓ W) + Module.finrank K E := by
  let J : LinearMap.ker T →ₗ[K] ↥(U ⊓ W) :=
    { toFun := fun u => ⟨u.val.val, Submodule.mem_inf.mpr
        ⟨u.val.property, hker u.val (LinearMap.mem_ker.mp u.property)⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hJ : Function.Injective J := by
    intro u v huv
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥(U ⊓ W) => z.val) huv
  have hkerdim := LinearMap.finrank_le_finrank_of_injective hJ
  calc
    Module.finrank K U =
        Module.finrank K (LinearMap.range T) +
          Module.finrank K (LinearMap.ker T) :=
      (LinearMap.finrank_range_add_finrank_ker T).symm
    _ ≤ Module.finrank K E + Module.finrank K ↥(U ⊓ W) :=
      Nat.add_le_add (Submodule.finrank_le _) hkerdim
    _ = Module.finrank K ↥(U ⊓ W) + Module.finrank K E := Nat.add_comm _ _

variable {ι : Type*} [Fintype ι]
variable {E : ι → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]

/-- A finite family of maps is charged by the sum of its image dimensions.
Each image is finite-dimensional because `U` is finite-dimensional, even when
the corresponding ambient codomain is not. -/
theorem family_kernel_budget (U W : Submodule K V) [FiniteDimensional K U]
    (L : ∀ i, U →ₗ[K] E i)
    (hker : ∀ u : U, (∀ i, L i u = 0) → (u : V) ∈ W) :
    Module.finrank K U ≤
      Module.finrank K ↥(U ⊓ W) +
        ∑ i, Module.finrank K (L i).range := by
  classical
  let T : U →ₗ[K] (∀ i, (L i).range) :=
    LinearMap.pi (fun i => (L i).rangeRestrict)
  have hT : ∀ u : U, T u = 0 → (u : V) ∈ W := by
    intro u hu
    exact hker u (fun i => congrArg Subtype.val (congrFun hu i))
  calc
    Module.finrank K U ≤
        Module.finrank K ↥(U ⊓ W) +
          Module.finrank K (∀ i, (L i).range) := kernel_budget U W T hT
    _ = Module.finrank K ↥(U ⊓ W) +
        ∑ i, Module.finrank K (L i).range := by
      rw [Module.finrank_pi_fintype]

/-- Numerical upper bounds on the restriction images give a numerical budget.
The bounds are hypotheses, not assumed formulas for affine restriction ranks. -/
theorem family_kernel_budget_of_bounds (U W : Submodule K V)
    [FiniteDimensional K U] (L : ∀ i, U →ₗ[K] E i)
    (hker : ∀ u : U, (∀ i, L i u = 0) → (u : V) ∈ W)
    (budget : ι → ℕ)
    (hbudget : ∀ i, Module.finrank K (L i).range ≤ budget i) :
    Module.finrank K U ≤ Module.finrank K ↥(U ⊓ W) + ∑ i, budget i := by
  classical
  exact (family_kernel_budget U W L hker).trans
    (Nat.add_le_add_left (Finset.sum_le_sum (fun i _ => hbudget i)) _)

/-- If `U` contains no nonzero vector of `W`, all of its dimension must be
accounted for by the restriction images. -/
theorem separated_family_budget (U W : Submodule K V) [FiniteDimensional K U]
    (L : ∀ i, U →ₗ[K] E i)
    (hker : ∀ u : U, (∀ i, L i u = 0) → (u : V) ∈ W)
    (budget : ι → ℕ)
    (hbudget : ∀ i, Module.finrank K (L i).range ≤ budget i)
    (hsep : ∀ u ∈ U, u ∈ W → u = 0) :
    Module.finrank K U ≤ ∑ i, budget i := by
  have hinter : U ⊓ W = ⊥ := by
    apply le_antisymm
    · intro u hu
      simpa using hsep u hu.1 hu.2
    · exact bot_le
  simpa [hinter] using family_kernel_budget_of_bounds U W L hker budget hbudget

end LinearAlgebra

section OrdinaryPC

open MvPolynomial MathResearch.PolynomialCalculus

variable {K σ ι : Type*} [Field K] [Finite σ] [Fintype ι]
variable {E : ι → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]

/-- A subspace of bounded ordinary total degree is finite-dimensional when the
variable type is finite. The full polynomial ring remains unrestricted. -/
theorem finiteDimensional_of_degree_bound
    (U : Submodule K (MvPolynomial σ K)) (k : ℕ)
    (hU : ∀ p ∈ U, p.totalDegree ≤ k) : FiniteDimensional K U := by
  have hUle : U ≤ restrictTotalDegree σ K k :=
    fun p hp => (mem_restrictTotalDegree _ _ _).mpr (hU p hp)
  exact Submodule.finiteDimensional_of_le hUle

/-- Ordinary-PC dimension budget. The kernel hypothesis must be supplied by a
derivation/replay theorem; it refers to actual degree-bounded ordinary PC. -/
theorem pc_family_budget
    (F : Set (MvPolynomial σ K)) (B k : ℕ)
    (U : Submodule K (MvPolynomial σ K))
    (hU : ∀ p ∈ U, p.totalDegree ≤ k)
    (L : ∀ i, U →ₗ[K] E i)
    (hker : ∀ p : U, (∀ i, L i p = 0) → Derives F B p.val)
    (budget : ι → ℕ)
    (hbudget : ∀ i, Module.finrank K (L i).range ≤ budget i) :
    Module.finrank K U ≤
      Module.finrank K ↥(U ⊓ pcSpace F B) + ∑ i, budget i := by
  letI : FiniteDimensional K U := finiteDimensional_of_degree_bound U k hU
  exact family_kernel_budget_of_bounds U (pcSpace F B) L hker budget hbudget

/-- The separated ordinary-PC version. Separation is stated against the actual
PC derivation relation and is not inferred from a static NS separator. -/
theorem pc_separated_family_budget
    (F : Set (MvPolynomial σ K)) (B k : ℕ)
    (U : Submodule K (MvPolynomial σ K))
    (hU : ∀ p ∈ U, p.totalDegree ≤ k)
    (L : ∀ i, U →ₗ[K] E i)
    (hker : ∀ p : U, (∀ i, L i p = 0) → Derives F B p.val)
    (budget : ι → ℕ)
    (hbudget : ∀ i, Module.finrank K (L i).range ≤ budget i)
    (hsep : ∀ p ∈ U, Derives F B p → p = 0) :
    Module.finrank K U ≤ ∑ i, budget i := by
  letI : FiniteDimensional K U := finiteDimensional_of_degree_bound U k hU
  exact separated_family_budget U (pcSpace F B) L hker budget hbudget hsep

end OrdinaryPC

end BoundaryLab.DimensionBudget
