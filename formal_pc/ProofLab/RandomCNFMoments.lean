import ProofLab.RandomCNFExpansion

/-! Moment and tail bounds used simultaneously in the finite triple sample. -/

namespace BoundaryLab.RandomCNFMoments

noncomputable section
open scoped BigOperators
open FiniteBernoulli BernoulliBounds BernoulliCounting TripleCounting RandomCNFExpansion

variable {V : Type} [Fintype V] [DecidableEq V]

def degree (H : Finset (Triple V)) (v : V) : ℕ := (incident v ∩ H).card
def degreeSquares (H : Finset (Triple V)) : ℕ := ∑ v, degree H v ^ 2
def sampledPairs (H : Finset (Triple V)) : Finset (Triple V × Triple V) :=
  conflictPairs.filter (fun ef => ({ef.1, ef.2} : Finset (Triple V)) ⊆ H)

theorem mean_degree_le (v : V) :
    tripleProbability (Fintype.card V) * (incident v).card ≤ 48 := by
  have hn : 0 < (Fintype.card V : ℝ) := by
    have : Nonempty V := ⟨v⟩
    exact_mod_cast Fintype.card_pos
  have h := mul_le_mul_of_nonneg_left (card_incident_le v)
    (show 0 ≤ tripleProbability (Fintype.card V) by unfold tripleProbability; positivity)
  have he : tripleProbability (Fintype.card V) * ((Fintype.card V : ℝ) ^ 2 / 2) = 48 := by
    unfold tripleProbability
    field_simp
    ring
  exact h.trans_eq he

theorem expectation_degreeSquares_le :
    expectation (tripleProbability (Fintype.card V)) (fun H : Finset (Triple V) =>
      (degreeSquares H : ℝ)) ≤ 2352 * Fintype.card V := by
  simp only [degreeSquares, Nat.cast_sum, Nat.cast_pow]
  rw [expectation_sum]
  calc
    _ ≤ ∑ _v : V, (2352 : ℝ) := by
      apply Finset.sum_le_sum
      intro v _
      apply (expectation_card_inter_square_le (tripleProbability (Fintype.card V)) (incident v)).trans
      have h := mean_degree_le v
      have h0 : 0 ≤ tripleProbability (Fintype.card V) * (incident v).card := by
        unfold tripleProbability; positivity
      nlinarith
    _ = _ := by simp [mul_comm]

theorem expectation_sampledPairs (p : ℝ) :
    expectation p (fun H : Finset (Triple V) => ((sampledPairs H).card : ℝ)) =
      (conflictPairs (V := V)).card * p ^ 2 := by
  have hc (H : Finset (Triple V)) : ((sampledPairs H).card : ℝ) =
      ∑ ef ∈ conflictPairs, if ({ef.1, ef.2} : Finset (Triple V)) ⊆ H then (1 : ℝ) else 0 := by
    simp [sampledPairs]
  simp_rw [hc, expectation_sum, expectation_containing]
  have heq : (∑ ef ∈ conflictPairs (V := V), p ^ ({ef.1, ef.2} : Finset (Triple V)).card) =
      ∑ _ef ∈ conflictPairs (V := V), p ^ 2 := by
    apply Finset.sum_congr rfl
    intro ef hef
    have hne := (Finset.mem_filter.mp (Finset.mem_filter.mp hef).2).2.1
    rw [Finset.card_pair hne]
  rw [heq]
  simp

theorem expectation_sampledPairs_le (hn : 0 < Fintype.card V) :
    expectation (tripleProbability (Fintype.card V))
      (fun H : Finset (Triple V) => ((sampledPairs H).card : ℝ)) ≤ 4608 := by
  rw [expectation_sampledPairs]
  have hnR : 0 < (Fintype.card V : ℝ) := by exact_mod_cast hn
  have h := mul_le_mul_of_nonneg_right (card_conflictPairs_real_le (V := V))
    (sq_nonneg (tripleProbability (Fintype.card V)))
  apply h.trans_eq
  unfold tripleProbability
  field_simp
  ring

theorem mean_triples_lower {n : ℕ} (hn : 96 ≤ n) :
    (31 / 2 : ℝ) * n ≤ tripleProbability n * (n.choose 3 : ℝ) := by
  have hn2 : 2 ≤ n := by omega
  have hnR : (96 : ℝ) ≤ n := by exact_mod_cast hn
  have hnat := Nat.descFactorial_eq_factorial_mul_choose n 3
  norm_num [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.factorial] at hnat
  have hcast := congrArg (fun a : ℕ => (a : ℝ)) hnat
  push_cast [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_sub hn2] at hcast
  unfold tripleProbability
  rw [show (96 : ℝ) / (n : ℝ) ^ 2 * (n.choose 3 : ℝ) =
    96 * (n.choose 3 : ℝ) / (n : ℝ) ^ 2 by ring]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)).mpr
  have hpoly : 0 ≤ (n : ℝ) ^ 2 * ((n : ℝ) - 96) := by positivity
  nlinarith

theorem mass_too_few_triples_le (hn : 1000000 ≤ Fintype.card V) :
    mass (tripleProbability (Fintype.card V))
      (Finset.univ.filter (fun H : Finset (Triple V) => H.card < 15 * Fintype.card V)) ≤ 1 / 16 := by
  obtain ⟨hp, hp1⟩ := tripleProbability_bounds (by omega : 10 ≤ Fintype.card V)
  have hnR : (1000000 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hmean := mean_triples_lower (by omega : 96 ≤ Fintype.card V)
  have hexp : Real.exp (-1 / 64) ≤ 1 - 1 / 64 + 1 / 4096 := by
    have h := Real.abs_exp_sub_one_sub_id_le (x := (-1 / 64 : ℝ)) (by norm_num)
    norm_num [neg_div] at h ⊢
    linarith [(abs_le.mp h).2]
  have htail := mass_le_exponential_markov (V := Triple V) (θ := -1 / 64)
    (a := -(15 * (Fintype.card V : ℝ)) / 64) hp hp1
    (Finset.univ.filter (fun H : Finset (Triple V) => H.card < 15 * Fintype.card V)) (by
      intro H hH
      have h : (H.card : ℝ) < 15 * Fintype.card V := by exact_mod_cast (Finset.mem_filter.mp hH).2
      linarith)
  rw [card_triple] at htail
  have hsmall : Real.exp (-(Fintype.card V : ℝ) / 256) ≤ 1 / 16 := by
    rw [neg_div, Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
    have h := Real.add_one_le_exp ((Fintype.card V : ℝ) / 256)
    linarith
  apply htail.trans (le_trans (Real.exp_le_exp.mpr ?_) hsmall)
  have h0 : 0 ≤ tripleProbability (Fintype.card V) * ((Fintype.card V).choose 3 : ℝ) := by positivity
  nlinarith [mul_nonneg h0 (sub_nonneg.mpr hexp)]

end

end BoundaryLab.RandomCNFMoments
