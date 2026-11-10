import ProofLab.FiniteBernoulli
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Exponential bounds for explicit finite Bernoulli sums

The lower bound is derived from positive association and a sum of actual
boundary-containment probabilities. The distribution is the finite product
distribution defined in `FiniteBernoulli`, including its exact layer counts.
-/

namespace BoundaryLab.BernoulliBounds

noncomputable section

open FiniteBernoulli
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exp_neg_two_le_one_sub {u : ℝ} (hu : 0 ≤ u) (hu2 : u ≤ 1 / 2) :
    Real.exp (-2 * u) ≤ 1 - u := by
  have hpos : 0 < 1 - u := by linarith
  have hinv : (1 - u)⁻¹ ≤ 1 + 2 * u := by
    apply (inv_le_iff_one_le_mul₀ hpos).mpr
    nlinarith
  have hlog := Real.one_sub_inv_le_log_of_pos hpos
  calc
    Real.exp (-2 * u) ≤ Real.exp (Real.log (1 - u)) :=
      Real.exp_le_exp.mpr (by linarith)
    _ = 1 - u := Real.exp_log hpos

theorem exp_sum_le_product {J : Type*} (A : Finset J) (u : J → ℝ)
    (h0 : ∀ j ∈ A, 0 ≤ u j) (hhalf : ∀ j ∈ A, u j ≤ 1 / 2) :
    Real.exp (-2 * ∑ j ∈ A, u j) ≤ ∏ j ∈ A, (1 - u j) := by
  rw [Finset.mul_sum, Real.exp_sum]
  exact Finset.prod_le_prod₀ (fun j _ => (Real.exp_pos _).le)
    (fun j hj => exp_neg_two_le_one_sub (h0 j hj) (hhalf j hj))

/-- No probabilistic bound is postulated: the exponent is the explicit finite
sum over the supplied family of actual boundaries. -/
theorem exp_le_mass_avoidAll {J : Type*} {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Finset J) (D : J → Finset V) (hhalf : ∀ j ∈ A, p ^ (D j).card ≤ 1 / 2) :
    Real.exp (-2 * ∑ j ∈ A, p ^ (D j).card) ≤ mass p (avoidAll A D) :=
  (exp_sum_le_product A (fun j => p ^ (D j).card)
    (fun _ _ => pow_nonneg hp _) hhalf).trans (product_le_mass_avoidAll hp hp1 A D)

theorem generating_function (p z : ℝ) :
    (∑ T : Finset V, weight p T * z ^ T.card) = (1 - p + p * z) ^ Fintype.card V := by
  have heq (T : Finset V) :
      weight p T * z ^ T.card = atom (fun _ : V => p * z) (fun _ => 1 - p) T := by
    rw [weight_eq, atom_eq]
    simp only [Finset.prod_const, Finset.compl_eq_univ_sdiff,
      Finset.card_sdiff_of_subset (Finset.subset_univ T), Finset.card_univ, mul_pow]
    ring
  simp_rw [heq]
  rw [sum_atom]
  simp [add_comm]

theorem exponential_moment (p θ : ℝ) :
    (∑ T : Finset V, weight p T * Real.exp (θ * T.card)) =
      (1 - p + p * Real.exp θ) ^ Fintype.card V := by
  simp_rw [mul_comm θ, Real.exp_nat_mul]
  exact generating_function p (Real.exp θ)

theorem exponential_moment_le {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (θ : ℝ) :
    (∑ T : Finset V, weight p T * Real.exp (θ * T.card)) ≤
      Real.exp (p * Fintype.card V * (Real.exp θ - 1)) := by
  rw [exponential_moment]
  have hbase : 0 ≤ 1 - p + p * Real.exp θ :=
    add_nonneg (sub_nonneg.mpr hp1) (mul_nonneg hp (Real.exp_pos _).le)
  calc
    _ ≤ (Real.exp (p * (Real.exp θ - 1))) ^ Fintype.card V :=
      pow_le_pow_left₀ hbase (by linarith [Real.add_one_le_exp (p * (Real.exp θ - 1))]) _
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

/-- Markov's bound, proved directly for a finite sum of nonnegative weights. -/
theorem mass_le_exponential_markov {p θ a : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (H : Finset (Finset V)) (hH : ∀ T ∈ H, a ≤ θ * T.card) :
    mass p H ≤ Real.exp (p * Fintype.card V * (Real.exp θ - 1) - a) := by
  have hmul : mass p H * Real.exp a ≤
      ∑ T : Finset V, weight p T * Real.exp (θ * T.card) := by
    unfold mass
    rw [Finset.sum_mul]
    calc
      _ ≤ ∑ T ∈ H, weight p T * Real.exp (θ * T.card) :=
        Finset.sum_le_sum (fun T hT => mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (hH T hT)) (weight_nonneg hp hp1 T))
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ H)
        (fun T _ _ => mul_nonneg (weight_nonneg hp hp1 T) (Real.exp_pos _).le)
  have h := hmul.trans (exponential_moment_le hp hp1 θ)
  rw [Real.exp_sub, le_div_iff₀ (Real.exp_pos a)]
  exact h

theorem lower_tail {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (H : Finset (Finset V)) (hH : ∀ T ∈ H, (T.card : ℝ) ≤ p * Fintype.card V / 2) :
    mass p H ≤ Real.exp (-(p * Fintype.card V) / 8) := by
  have hmu : 0 ≤ p * Fintype.card V := mul_nonneg hp (Nat.cast_nonneg _)
  have he : Real.exp (-1) ≤ 3 / 8 := by
    have ht := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) 4
    norm_num [Finset.sum_range_succ] at ht
    rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos 1)]
    linarith
  apply (mass_le_exponential_markov (θ := -1) (a := -(p * Fintype.card V) / 2)
    hp hp1 H (fun T hT => by linarith [hH T hT])).trans
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg hmu (sub_nonneg.mpr he)]

theorem upper_tail {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (H : Finset (Finset V)) (hH : ∀ T ∈ H, 2 * (p * Fintype.card V) ≤ (T.card : ℝ)) :
    mass p H ≤ Real.exp (-(p * Fintype.card V) / 8) := by
  have hmu : 0 ≤ p * Fintype.card V := mul_nonneg hp (Nat.cast_nonneg _)
  have he : Real.exp (1 / 2) ≤ 5 / 3 := by
    have h := Real.exp_le_two_add_div_two_sub (x := 1 / 2) (by norm_num) (by norm_num)
    norm_num at h ⊢
    exact h
  apply (mass_le_exponential_markov (θ := 1 / 2) (a := p * Fintype.card V)
    hp hp1 H (fun T hT => by linarith [hH T hT])).trans
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg hmu (sub_nonneg.mpr he)]

def centralSizes (n : ℕ) (p : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (n + 1)).filter (fun k => p * n / 2 ≤ (k : ℝ) ∧ (k : ℝ) ≤ 2 * (p * n))

@[simp]
theorem mem_centralSizes (n k : ℕ) (p : ℝ) :
    k ∈ centralSizes n p ↔ k ≤ n ∧ p * n / 2 ≤ (k : ℝ) ∧ (k : ℝ) ≤ 2 * (p * n) := by
  classical
  simp only [centralSizes, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

/-- The explicit two-sided binomial tail estimate used by the paper argument. -/
theorem mass_outside_central {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    mass p (window (Finset.univ : Finset (Finset V)) (centralSizes (Fintype.card V) p))ᶜ ≤
      2 * Real.exp (-(p * Fintype.card V) / 8) := by
  classical
  let L : Finset (Finset V) := Finset.univ.filter (fun T => (T.card : ℝ) < p * Fintype.card V / 2)
  let U : Finset (Finset V) := Finset.univ.filter (fun T => 2 * (p * Fintype.card V) < (T.card : ℝ))
  have hsub : (window (Finset.univ : Finset (Finset V)) (centralSizes (Fintype.card V) p))ᶜ ⊆ L ∪ U := by
    intro T hT
    have hcard : T.card ≤ Fintype.card V := Finset.card_le_univ T
    have hout : ¬ (p * Fintype.card V / 2 ≤ (T.card : ℝ) ∧
        (T.card : ℝ) ≤ 2 * (p * Fintype.card V)) := by
      simpa [window, hcard] using hT
    rcases not_and_or.mp hout with hl | hu
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨Finset.mem_univ T, lt_of_not_ge hl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_univ T, lt_of_not_ge hu⟩)
  have hsplit : mass p (L ∪ U) ≤ mass p L + mass p U := by
    rw [mass_eq_indicator, mass_eq_indicator, mass_eq_indicator, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro T _
    have hw := weight_nonneg hp hp1 T
    by_cases hL : T ∈ L <;> by_cases hU : T ∈ U <;> simp [hL, hU]; linarith
  have hl := lower_tail hp hp1 L (fun T hT => ((Finset.mem_filter.mp hT).2).le)
  have hu := upper_tail hp hp1 U (fun T hT => ((Finset.mem_filter.mp hT).2).le)
  exact (mass_mono hp hp1 hsub).trans (hsplit.trans (by linarith))

/-- The entire probability-to-uniform-layer step, with the tail bound proved
internally. The remaining hypothesis compares two explicit numerical bounds. -/
theorem exists_dense_central_layer {J : Type*} {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (A : Finset J) (D : J → Finset V) (hhalf : ∀ j ∈ A, p ^ (D j).card ≤ 1 / 2)
    (htail : 2 * Real.exp (-(p * Fintype.card V) / 8) ≤
      (1 / 2) * Real.exp (-2 * ∑ j ∈ A, p ^ (D j).card)) :
    ∃ k ∈ centralSizes (Fintype.card V) p,
      ((1 / 2) * Real.exp (-2 * ∑ j ∈ A, p ^ (D j).card)) *
        ((Fintype.card V).choose k : ℝ) ≤ (layer (avoidAll A D) k).card := by
  apply exists_dense_layer hp hp1 (by positivity) (avoidAll A D) _
  have hg := exp_le_mass_avoidAll hp.le hp1.le A D hhalf
  have ht := mass_outside_central (V := V) hp.le hp1.le
  have hw := mass_window_ge_sub hp.le hp1.le (avoidAll A D) (centralSizes (Fintype.card V) p)
  linarith

end

end BoundaryLab.BernoulliBounds
