import ProofLab.RandomCNFMoments

/-! A simultaneous good sample, obtained by one finite averaging argument. -/

namespace BoundaryLab.RandomCNFSample

noncomputable section
open scoped BigOperators
open FiniteBernoulli BernoulliCounting TripleCounting RandomCNFExpansion RandomCNFMoments

variable {V : Type} [Fintype V] [DecidableEq V]

theorem exists_good_sample (hn : 1000000 ≤ Fintype.card V) :
    ∃ H : Finset (Triple V), H ∉ badExpansion ∧ 15 * Fintype.card V ≤ H.card ∧
      degreeSquares H ≤ 8192 * Fintype.card V ∧ (sampledPairs H).card ≤ Fintype.card V := by
  let n := Fintype.card V
  let p := tripleProbability n
  let L : Finset (Finset (Triple V)) := Finset.univ.filter (fun H => H.card < 15 * n)
  let f : Finset (Triple V) → ℝ := fun H =>
    (if H ∈ badExpansion then 1 else 0) + (if H ∈ L then 1 else 0) +
    (degreeSquares H : ℝ) / (8192 * n) + ((sampledPairs H).card : ℝ) / n
  have hnR : (1000000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  obtain ⟨hp, hp1⟩ := tripleProbability_bounds (by omega : 10 ≤ n)
  have he : expectation p f = mass p (badExpansion (V := V)) + mass p L +
      expectation p (fun H : Finset (Triple V) => (degreeSquares H : ℝ)) / (8192 * n) +
      expectation p (fun H : Finset (Triple V) => ((sampledPairs H).card : ℝ)) / n := by
    simp only [f, expectation, mul_add, div_eq_mul_inv, ← mul_assoc,
      Finset.sum_add_distrib, Finset.sum_mul, mass_eq_indicator]
  have hE : expectation p f < 1 := by
    have hb := mass_badExpansion_le (by omega : 10 ≤ Fintype.card V)
    have hl := mass_too_few_triples_le hn
    have hd := div_le_div_of_nonneg_right (expectation_degreeSquares_le (V := V))
      (show 0 ≤ 8192 * (n : ℝ) by positivity)
    have hc := div_le_div_of_nonneg_right (expectation_sampledPairs_le (by omega : 0 < Fintype.card V)) hn0.le
    have hdeq : (2352 * (n : ℝ)) / (8192 * n) = 2352 / 8192 := by field_simp
    rw [hdeq] at hd
    have hcle : (4608 : ℝ) / n ≤ 1 / 16 := by
      apply (div_le_iff₀ hn0).mpr
      linarith
    rw [he]
    change mass p (badExpansion (V := V)) ≤ 1 / 4 at hb
    change mass p L ≤ 1 / 16 at hl
    linarith
  have hex : ∃ H, f H < 1 := by
    by_contra! h
    have hm := expectation_mono hp hp1 (f := fun _ : Finset (Triple V) => 1) h
    have hnorm : expectation p (fun _ : Finset (Triple V) => 1) = 1 := by
      simpa [expectation, mass] using (mass_univ (V := Triple V) p)
    rw [hnorm] at hm
    linarith
  obtain ⟨H, hH⟩ := hex
  have hd0 : 0 ≤ (degreeSquares H : ℝ) / (8192 * n) := by positivity
  have hc0 : 0 ≤ ((sampledPairs H).card : ℝ) / n := by positivity
  have hb0 : (0 : ℝ) ≤ if H ∈ badExpansion then 1 else 0 := by split <;> norm_num
  have hl0 : (0 : ℝ) ≤ if H ∈ L then 1 else 0 := by split <;> norm_num
  have hnotB : H ∉ badExpansion := by
    intro h
    have hf : 1 ≤ f H := by dsimp [f]; rw [ite_eq_left h]; linarith
    linarith
  have hnotL : H ∉ L := by
    intro h
    have hf : 1 ≤ f H := by dsimp [f]; rw [ite_eq_left h]; linarith
    linarith
  have hcount : 15 * n ≤ H.card := by
    simpa only [L, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] using hnotL
  have hD : (degreeSquares H : ℝ) / (8192 * n) < 1 := by dsimp [f] at hH; linarith
  have hC : ((sampledPairs H).card : ℝ) / n < 1 := by dsimp [f] at hH; linarith
  have hD' : (degreeSquares H : ℝ) ≤ 8192 * n := by
    have h := (div_lt_iff₀ (show (0 : ℝ) < 8192 * n by positivity)).mp hD
    linarith
  have hC' : ((sampledPairs H).card : ℝ) ≤ n := by
    have h := (div_lt_iff₀ hn0).mp hC
    linarith
  exact ⟨H, hnotB, hcount, by exact_mod_cast hD', by exact_mod_cast hC'⟩

end

end BoundaryLab.RandomCNFSample
