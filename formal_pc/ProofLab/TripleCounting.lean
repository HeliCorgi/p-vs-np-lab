import ProofLab.BernoulliCounting
import ProofLab.LinearClauseBoundary
import Mathlib.Data.Nat.Choose.Bounds

/-! The actual finite sample space of distinct proper triples and its counts. -/

namespace BoundaryLab.TripleCounting

noncomputable section
open scoped BigOperators

variable {V : Type} [Fintype V] [DecidableEq V]

abbrev Triple (V : Type) [DecidableEq V] := {e : Finset V // e.card = 3}

def inside (W : Finset V) : Finset (Triple V) := Finset.univ.filter (fun e => e.1 ⊆ W)
def extending (W : Finset V) : Finset (Triple V) := Finset.univ.filter (fun e => W ⊆ e.1)
def incident (v : V) : Finset (Triple V) := extending {v}
def neighbors (A : Finset (Triple V)) : Finset V := A.biUnion Subtype.val

theorem inside_image (W : Finset V) : (inside W).image Subtype.val = W.powersetCard 3 := by
  ext e
  simp only [Finset.mem_image, inside, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_powersetCard]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ha, a.2⟩
  · rintro ⟨heW, he3⟩
    exact ⟨⟨e, he3⟩, heW, rfl⟩

theorem card_inside (W : Finset V) : (inside W).card = W.card.choose 3 := by
  rw [← Finset.card_image_of_injective _ Subtype.val_injective, inside_image, Finset.card_powersetCard]

theorem card_triple : Fintype.card (Triple V) = (Fintype.card V).choose 3 := by
  simp [Triple, Fintype.card_subtype]

theorem extending_image (W : Finset V) :
    (extending W).image Subtype.val =
      ((Finset.univ : Finset V).powersetCard 3).filter (W ⊆ ·) := by
  ext e
  simp only [Finset.mem_image, extending, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_powersetCard, Finset.subset_univ, true_and]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.2, ha⟩
  · rintro ⟨he3, hWe⟩
    exact ⟨⟨e, he3⟩, hWe, rfl⟩

theorem card_extending (W : Finset V) (hW : W.card ≤ 3) :
    (extending W).card = (Fintype.card V - W.card).choose (3 - W.card) := by
  rw [← Finset.card_image_of_injective _ Subtype.val_injective, extending_image,
    Finset.card_filter_powersetCard_subset _ _ _ (Finset.subset_univ _) hW, Finset.card_univ]

theorem card_incident (v : V) : (incident v).card = (Fintype.card V - 1).choose 2 := by
  simpa [incident] using card_extending ({v} : Finset V) (by simp)

theorem card_incident_le (v : V) : ((incident v).card : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 / 2 := by
  rw [card_incident]
  have h := (Nat.choose_le_pow_div 2 (Fintype.card V - 1) :
    ((Fintype.card V - 1).choose 2 : ℝ) ≤ ((Fintype.card V - 1 : ℕ) : ℝ) ^ 2 / (Nat.factorial 2 : ℝ))
  norm_num [Nat.factorial] at h
  have hn : ((Fintype.card V - 1 : ℕ) : ℝ) ≤ Fintype.card V := by exact_mod_cast Nat.sub_le _ 1
  have hpow := pow_le_pow_left₀ (by positivity) hn 2
  linarith

def conflicts (e : Triple V) : Finset (Triple V) :=
  Finset.univ.filter (fun f => e ≠ f ∧ 2 ≤ (e.1 ∩ f.1).card)

theorem conflicts_subset (e : Triple V) :
    conflicts e ⊆ (e.1.powersetCard 2).biUnion extending := by
  intro f hf
  have hcard := (Finset.mem_filter.mp hf).2.2
  obtain ⟨P, hP, hPc⟩ := Finset.exists_subset_card_eq hcard
  apply Finset.mem_biUnion.mpr
  exact ⟨P, Finset.mem_powersetCard.mpr ⟨hP.trans Finset.inter_subset_left, hPc⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP.trans Finset.inter_subset_right⟩⟩

theorem card_conflicts_le (e : Triple V) : (conflicts e).card ≤ 3 * Fintype.card V := by
  calc
    _ ≤ ((e.1.powersetCard 2).biUnion extending).card := Finset.card_le_card (conflicts_subset e)
    _ ≤ ∑ P ∈ e.1.powersetCard 2, (extending P).card := Finset.card_biUnion_le
    _ ≤ ∑ _P ∈ e.1.powersetCard 2, Fintype.card V := by
      apply Finset.sum_le_sum
      intro P hP
      have hPc := (Finset.mem_powersetCard.mp hP).2
      rw [card_extending P (by omega), hPc]
      simp
    _ = _ := by simp [Finset.card_powersetCard, e.2]

def conflictPairs : Finset (Triple V × Triple V) :=
  Finset.univ.filter (fun ef => ef.2 ∈ conflicts ef.1)

theorem card_conflictPairs_le :
    (conflictPairs (V := V)).card ≤ (Fintype.card V).choose 3 * (3 * Fintype.card V) := by
  have heq : conflictPairs (V := V) =
      (Finset.univ : Finset (Triple V)).biUnion
        (fun e => (conflicts e).image (fun f => (e, f))) := by
    ext ef
    simp only [conflictPairs, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_biUnion, Finset.mem_image]
    constructor
    · intro h
      exact ⟨ef.1, ef.2, h, rfl⟩
    · rintro ⟨e, f, hf, rfl⟩
      exact hf
  rw [heq]
  calc
    _ ≤ ∑ e : Triple V, ((conflicts e).image (fun f => (e, f))).card := Finset.card_biUnion_le
    _ ≤ ∑ _e : Triple V, 3 * Fintype.card V := Finset.sum_le_sum (fun e _ =>
      Finset.card_image_le.trans (card_conflicts_le e))
    _ = _ := by simp

theorem card_conflictPairs_real_le :
    ((conflictPairs (V := V)).card : ℝ) ≤ (Fintype.card V : ℝ) ^ 4 / 2 := by
  have hc : ((conflictPairs (V := V)).card : ℝ) ≤
      ((Fintype.card V).choose 3 : ℝ) * (3 * Fintype.card V) := by exact_mod_cast card_conflictPairs_le
  have hb := (Nat.choose_le_pow_div 3 (Fintype.card V) :
    ((Fintype.card V).choose 3 : ℝ) ≤ (Fintype.card V : ℝ) ^ 3 / (Nat.factorial 3 : ℝ))
  norm_num [Nat.factorial] at hb
  have h := mul_le_mul_of_nonneg_right hb (show (0 : ℝ) ≤ 3 * Fintype.card V by positivity)
  nlinarith

end

end BoundaryLab.TripleCounting
