import ProofLab.BernoulliBounds

/-! Finite expectations and union bounds for the actual Bernoulli weights. -/

namespace BoundaryLab.BernoulliCounting

noncomputable section
open scoped BigOperators
open FiniteBernoulli

variable {V : Type*} [Fintype V] [DecidableEq V]

def expectation (p : ℝ) (f : Finset V → ℝ) : ℝ := ∑ T, weight p T * f T

theorem expectation_sum {J : Type*} (p : ℝ) (A : Finset J) (f : J → Finset V → ℝ) :
    expectation p (fun T => ∑ j ∈ A, f j T) = ∑ j ∈ A, expectation p (f j) := by
  simp only [expectation, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem expectation_indicator (p : ℝ) (H : Finset (Finset V)) :
    expectation p (fun T => if T ∈ H then 1 else 0) = mass p H :=
  (mass_eq_indicator p H).symm

theorem expectation_containing (p : ℝ) (D : Finset V) :
    expectation p (fun T => if D ⊆ T then 1 else 0) = p ^ D.card := by
  simpa only [containing, Finset.mem_filter, Finset.mem_univ, true_and] using
    (expectation_indicator p (containing D)).trans (mass_containing p D)

theorem expectation_mono {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    {f g : Finset V → ℝ} (h : ∀ T, f T ≤ g T) : expectation p f ≤ expectation p g :=
  Finset.sum_le_sum (fun T _ => mul_le_mul_of_nonneg_left (h T) (weight_nonneg hp hp1 T))

theorem mass_union_le {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    {J : Type*} (A : Finset J) (H : J → Finset (Finset V)) :
    mass p (A.biUnion H) ≤ ∑ j ∈ A, mass p (H j) := by
  classical
  simp_rw [← expectation_indicator]
  rw [← expectation_sum]
  apply expectation_mono hp hp1
  intro T
  by_cases hT : T ∈ A.biUnion H
  · rw [ite_eq_left hT]
    obtain ⟨j, hj, hjT⟩ := Finset.mem_biUnion.mp hT
    have h := Finset.single_le_sum (f := fun j => if T ∈ H j then (1 : ℝ) else 0)
      (fun j _ => by split <;> norm_num) hj
    simpa only [ite_eq_left hjT] using h
  · rw [ite_eq_right hT]
    exact Finset.sum_nonneg (fun j _ => by split <;> norm_num)

theorem mass_witnesses_le {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    {J : Type*} (A : Finset J) (D : J → Finset V) :
    mass p (A.biUnion (fun j => containing (D j))) ≤ ∑ j ∈ A, p ^ (D j).card := by
  simpa only [mass_containing] using mass_union_le hp hp1 A (fun j => containing (D j))

theorem mass_ge_value_le {p a : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (f : Finset V → ℝ) (hf : ∀ T, 0 ≤ f T) (ha : 0 < a)
    (H : Finset (Finset V)) (hH : ∀ T ∈ H, a ≤ f T) :
    mass p H ≤ expectation p f / a := by
  apply (le_div_iff₀ ha).mpr
  rw [mass, Finset.sum_mul]
  calc
    ∑ T ∈ H, weight p T * a ≤ ∑ T ∈ H, weight p T * f T :=
      Finset.sum_le_sum (fun T hT => mul_le_mul_of_nonneg_left (hH T hT) (weight_nonneg hp hp1 T))
    _ ≤ expectation p f := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun T _ _ => mul_nonneg (weight_nonneg hp hp1 T) (hf T))

omit [Fintype V] in
theorem card_inter_indicator (D T : Finset V) :
    ((D ∩ T).card : ℝ) = ∑ i ∈ D, if i ∈ T then (1 : ℝ) else 0 := by
  simp

theorem expectation_card_inter (p : ℝ) (D : Finset V) :
    expectation p (fun T => ((D ∩ T).card : ℝ)) = p * D.card := by
  simp_rw [card_inter_indicator]
  rw [expectation_sum]
  have hs (i : V) : expectation p (fun T => if i ∈ T then 1 else 0) = p := by
    simpa using expectation_containing p {i}
  simp [hs, mul_comm]

omit [Fintype V] in
theorem card_inter_square_indicator (D T : Finset V) :
    ((D ∩ T).card : ℝ) ^ 2 =
      ∑ i ∈ D, ∑ j ∈ D, if ({i, j} : Finset V) ⊆ T then (1 : ℝ) else 0 := by
  rw [pow_two, card_inter_indicator, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hi : i ∈ T <;> by_cases hj : j ∈ T <;>
    simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, hi, hj]

theorem expectation_card_inter_square (p : ℝ) (D : Finset V) :
    expectation p (fun T => ((D ∩ T).card : ℝ) ^ 2) =
      (D.card : ℝ) * p + (D.card : ℝ) * (D.card - 1 : ℕ) * p ^ 2 := by
  simp_rw [card_inter_square_indicator, expectation_sum, expectation_containing]
  have hi (i : V) (hi : i ∈ D) : ∑ j ∈ D, p ^ ({i, j} : Finset V).card =
      p + (D.card - 1 : ℕ) * p ^ 2 := by
    have heq : (∑ j ∈ D, p ^ ({i, j} : Finset V).card) =
        ∑ j ∈ D, if j = i then p else p ^ 2 := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hij : j = i
      · simp [hij]
      · simp [Finset.card_pair (Ne.symm hij), hij]
    rw [heq, ← Finset.sum_erase_add _ _ hi]
    have herase : (∑ j ∈ D.erase i, if j = i then p else p ^ 2) =
        (D.erase i).card * p ^ 2 := by
      simp only [Finset.sum_ite_of_false (fun j hj => Finset.ne_of_mem_erase hj),
        Finset.sum_const, nsmul_eq_mul]
    rw [herase]
    simp [Finset.card_erase_of_mem hi, add_comm]
  rw [Finset.sum_congr rfl hi]
  simp [mul_assoc]

theorem expectation_card_inter_square_le (p : ℝ) (D : Finset V) :
    expectation p (fun T => ((D ∩ T).card : ℝ) ^ 2) ≤
      p * D.card + (p * D.card) ^ 2 := by
  rw [expectation_card_inter_square]
  have h : ((D.card - 1 : ℕ) : ℝ) ≤ D.card := by exact_mod_cast Nat.sub_le D.card 1
  have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ (D.card : ℝ) * p ^ 2 by positivity)
  nlinarith

end

end BoundaryLab.BernoulliCounting
