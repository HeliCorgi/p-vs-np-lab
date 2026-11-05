import ProofLab.QuadraticPolar
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

/-!
# Exponentially many affine charts for a linear-size Boolean computation

An explicit injection of the smaller assignment cube into the one-level of
the binary inner-product quadratic supplies a large subset of that level.
The polar-rank theorem bounds every injective constant affine chart. Counting
their union proves an exponential covering lower bound, allowing arbitrary
overlaps. This is a representation lower bound, not a circuit lower bound.
-/

set_option autoImplicit false

namespace BoundaryLab.QuadraticAffineCover

noncomputable section

open QuadraticPolar
open scoped BigOperators

variable {W : Type} [Fintype W]

/-- Pin one coordinate of the first input to one and choose the corresponding
second coordinate to make the whole inner product one. -/
def positiveSlice (z : Point W) : Point (Option W) :=
  ((fun i => match i with | none => 1 | some j => z.1 j),
   (fun i => match i with | none => 1 + quadratic z | some j => z.2 j))

@[simp]
theorem quadratic_positiveSlice (z : Point W) :
    quadratic (positiveSlice z) = 1 := by
  classical
  have htwo : (2 : F2) = 0 := by decide
  change (∑ i : Option W, (positiveSlice z).1 i * (positiveSlice z).2 i) = 1
  rw [Fintype.sum_option]
  change 1 * (1 + quadratic z) + quadratic z = 1
  calc
    1 * (1 + quadratic z) + quadratic z = 1 + 2 * quadratic z := by ring
    _ = 1 := by rw [htwo]; ring

theorem positiveSlice_injective : Function.Injective (positiveSlice (W := W)) := by
  intro a b hab
  apply Prod.ext
  · funext j
    exact congrArg (fun z : Point (Option W) => z.1 (some j)) hab
  · funext j
    exact congrArg (fun z : Point (Option W) => z.2 (some j)) hab

theorem card_point : Fintype.card (Point W) = 2 ^ (2 * Fintype.card W) := by
  simp [Point, Fintype.card_fun, ← pow_add, two_mul]

/-- A finite chart union covering the one-level must have exponentially many
points in its combined parameter cubes. No disjointness premise is used. -/
theorem cover_parameter_budget {ι : Type} [Fintype ι]
    (t : ι → ℕ)
    (f : ∀ a, (Fin (t a) → F2) →ᵃ[F2] Point (Option W))
    (hcover : ∀ z : Point (Option W), quadratic z = 1 →
      ∃ a, ∃ y, f a y = z) :
    2 ^ (2 * Fintype.card W) ≤ ∑ a, 2 ^ t a := by
  classical
  let images : ι → Finset (Point (Option W)) :=
    fun a => Finset.univ.image (f a)
  let slice : Finset (Point (Option W)) :=
    Finset.univ.image (positiveSlice (W := W))
  have hsubset : slice ⊆ Finset.univ.biUnion images := by
    intro z hz
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨a, y, hy⟩ := hcover (positiveSlice w) (quadratic_positiveSlice w)
    exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a,
      Finset.mem_image.mpr ⟨y, Finset.mem_univ y, hy⟩⟩
  have hslice : slice.card = 2 ^ (2 * Fintype.card W) := by
    rw [Finset.card_image_of_injective _ positiveSlice_injective, Finset.card_univ]
    exact card_point
  calc
    2 ^ (2 * Fintype.card W) = slice.card := hslice.symm
    _ ≤ (Finset.univ.biUnion images).card := Finset.card_le_card hsubset
    _ ≤ ∑ a, (images a).card := Finset.card_biUnion_le
    _ ≤ ∑ a, 2 ^ t a := by
      apply Finset.sum_le_sum
      intro a _
      calc
        (images a).card ≤ (Finset.univ : Finset (Fin (t a) → F2)).card :=
          Finset.card_image_le
        _ = 2 ^ t a := by simp [Fintype.card_fun]

/-- The geometric dimension theorem converts the parameter sum to a bound on
the number of flats. Repeated charts and overlapping flats are allowed. -/
theorem cover_count_budget {ι : Type} [Fintype ι]
    (t : ι → ℕ)
    (f : ∀ a, (Fin (t a) → F2) →ᵃ[F2] Point (Option W))
    (hinj : ∀ a, Function.Injective (f a))
    (hone : ∀ a y, quadratic (f a y) = 1)
    (hcover : ∀ z : Point (Option W), quadratic z = 1 →
      ∃ a, ∃ y, f a y = z) :
    2 ^ (2 * Fintype.card W) ≤
      Fintype.card ι * 2 ^ (Fintype.card W + 1) := by
  have ht : ∀ a, t a ≤ Fintype.card W + 1 := by
    intro a
    simpa only [Fintype.card_option] using
      parameterCount_le_of_constant_affine (f a) (hinj a) 1 (hone a)
  calc
    2 ^ (2 * Fintype.card W) ≤ ∑ a, 2 ^ t a := cover_parameter_budget t f hcover
    _ ≤ ∑ _a : ι, 2 ^ (Fintype.card W + 1) :=
      Finset.sum_le_sum (fun a _ => Nat.pow_le_pow_right (by decide) (ht a))
    _ = Fintype.card ι * 2 ^ (Fintype.card W + 1) := by simp

/-- On `2 * (card W + 1)` input bits, every affine one-cover has at least
`2 ^ (card W - 1)` charts. The zero-dimensional parameter cube is a singleton.
The nonempty free-index hypothesis only justifies exponent subtraction. -/
theorem exponential_cover_count {ι : Type} [Fintype ι] [Nonempty W]
    (t : ι → ℕ)
    (f : ∀ a, (Fin (t a) → F2) →ᵃ[F2] Point (Option W))
    (hinj : ∀ a, Function.Injective (f a))
    (hone : ∀ a y, quadratic (f a y) = 1)
    (hcover : ∀ z : Point (Option W), quadratic z = 1 →
      ∃ a, ∃ y, f a y = z) :
    2 ^ (Fintype.card W - 1) ≤ Fintype.card ι := by
  have h := cover_count_budget t f hinj hone hcover
  have hn := Fintype.card_pos (α := W)
  have he : 2 * Fintype.card W =
      (Fintype.card W - 1) + (Fintype.card W + 1) := by omega
  rw [he, pow_add] at h
  exact le_of_mul_le_mul_right h (by positivity)

end

end BoundaryLab.QuadraticAffineCover
