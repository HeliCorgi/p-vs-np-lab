import ProofLab.RandomCNFEstimates
import ProofLab.TripleCounting

/-! The neighborhood-expansion failure event in the actual random hypergraph. -/

namespace BoundaryLab.RandomCNFExpansion

noncomputable section
open scoped BigOperators
open FiniteBernoulli BernoulliCounting TripleCounting ExponentialBudget RandomCNFEstimates

variable {V : Type} [Fintype V] [DecidableEq V]

def badInside (W : Finset V) (t : ℕ) : Finset (Finset (Triple V)) :=
  ((inside W).powersetCard t).biUnion containing

def badLayer (t : ℕ) : Finset (Finset (Triple V)) :=
  ((Finset.univ : Finset V).powersetCard (7 * t / 4)).biUnion (fun W => badInside W t)

def badExpansion : Finset (Finset (Triple V)) :=
  ((Finset.range (expansionSize (Fintype.card V) + 1)).filter (3 ≤ ·)).biUnion badLayer

def tripleProbability (n : ℕ) : ℝ := 96 / (n : ℝ) ^ 2

theorem tripleProbability_bounds {n : ℕ} (hn : 10 ≤ n) :
    0 ≤ tripleProbability n ∧ tripleProbability n ≤ 1 := by
  have h : (10 : ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · unfold tripleProbability; positivity
  · unfold tripleProbability
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)).mpr
    nlinarith

theorem mass_badInside_le {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (W : Finset V) (t : ℕ) :
    mass p (badInside W t) ≤ ((W.card.choose 3).choose t : ℝ) * p ^ t := by
  have h := mass_witnesses_le hp hp1 ((inside W).powersetCard t) id
  have hsum : (∑ A ∈ (inside W).powersetCard t, p ^ A.card) =
      ((W.card.choose 3).choose t : ℝ) * p ^ t := by
    calc
      _ = ∑ _A ∈ (inside W).powersetCard t, p ^ t := Finset.sum_congr rfl (fun A hA => by
        rw [(Finset.mem_powersetCard.mp hA).2])
      _ = _ := by simp [Finset.card_powersetCard, card_inside]
  exact h.trans_eq hsum

theorem mass_badLayer_le {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (t : ℕ) :
    mass p (badLayer (V := V) t) ≤
      ((Fintype.card V).choose (7 * t / 4) : ℝ) *
        (((7 * t / 4).choose 3).choose t : ℝ) * p ^ t := by
  apply (mass_union_le hp hp1 _ _).trans
  calc
    _ ≤ ∑ _W ∈ (Finset.univ : Finset V).powersetCard (7 * t / 4),
        (((7 * t / 4).choose 3).choose t : ℝ) * p ^ t := by
      apply Finset.sum_le_sum
      intro W hW
      simpa only [(Finset.mem_powersetCard.mp hW).2] using mass_badInside_le hp hp1 W t
    _ = _ := by simp [Finset.card_powersetCard, mul_assoc]

theorem geometric_tail_three (s : ℕ) :
    (∑ t ∈ (Finset.range (s + 1)).filter (3 ≤ ·), (1 / 2 : ℝ) ^ t) ≤ 1 / 4 := by
  by_cases hs : 3 ≤ s
  · have heq : s + 1 = 3 + (s - 2) := by omega
    rw [Finset.sum_filter, heq, Finset.sum_range_add]
    have hsmall : (∑ t ∈ Finset.range 3, if 3 ≤ t then (1 / 2 : ℝ) ^ t else 0) = 0 := by
      norm_num [Finset.sum_range_succ]
    rw [hsmall, zero_add]
    simp only [show ∀ j : ℕ, 3 ≤ 3 + j by omega, ite_true, pow_add]
    rw [← Finset.mul_sum]
    have h := sum_geometric_two_le (s - 2)
    norm_num at h ⊢
    linarith
  · have he : (Finset.range (s + 1)).filter (3 ≤ ·) = ∅ := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false]
      omega
    rw [he]
    norm_num

theorem mass_badExpansion_le (hn : 10 ≤ Fintype.card V) :
    mass (tripleProbability (Fintype.card V)) (badExpansion (V := V)) ≤ 1 / 4 := by
  obtain ⟨hp, hp1⟩ := tripleProbability_bounds hn
  apply (mass_union_le hp hp1 _ _).trans
  apply (Finset.sum_le_sum (fun t ht => ?_)).trans (geometric_tail_three _)
  obtain ⟨hts, ht3⟩ := Finset.mem_filter.mp ht
  have hts' : t ≤ Fintype.card V / expansionScale := by
    simpa only [Finset.mem_range, Nat.lt_succ_iff, expansionSize] using hts
  exact (mass_badLayer_le hp hp1 t).trans (bad_neighborhood_summand ht3 hts')

theorem neighborhood_of_not_bad {H : Finset (Triple V)}
    (hH : H ∉ badExpansion) (A : Finset (Triple V)) (hAH : A ⊆ H)
    (hA3 : 3 ≤ A.card) (hAs : A.card ≤ expansionSize (Fintype.card V)) :
    7 * A.card < 4 * (neighbors A).card := by
  by_contra h
  have hsmall : (neighbors A).card ≤ 7 * A.card / 4 := by omega
  have hrn : 7 * A.card / 4 ≤ Fintype.card V := by
    have hs := Nat.div_mul_le_self (Fintype.card V) expansionScale
    unfold expansionSize at hAs
    norm_num [expansionScale] at *
    omega
  obtain ⟨W, hNW, _, hW⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ (neighbors A)) hsmall (by simpa using hrn)
  apply hH
  apply Finset.mem_biUnion.mpr
  refine ⟨A.card, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hA3⟩, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨W, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hW⟩, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨A, Finset.mem_powersetCard.mpr ⟨?_, rfl⟩, ?_⟩
  · intro e he
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro v hv
    exact hNW (Finset.mem_biUnion.mpr ⟨e, he, hv⟩)
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAH⟩

end

end BoundaryLab.RandomCNFExpansion
