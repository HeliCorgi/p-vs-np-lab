import ProofLab.ExponentialBudget
import ProofLab.BernoulliCounting

/-!
# Explicit estimates for the random triple construction

The union bound is kept finite. A geometric bound starting at t=3 suffices;
no informal interchange of an asymptotic limit and a growing sum is needed.
-/

namespace BoundaryLab.RandomCNFEstimates

noncomputable section
open scoped BigOperators

theorem exp_one_le_three : Real.exp 1 ≤ 3 := by
  have h := Real.exp_le_two_add_div_two_sub (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  norm_num at h
  have he : Real.exp 1 = Real.exp (1 / 2) * Real.exp (1 / 2) := by
    rw [← Real.exp_add]
    norm_num
  rw [he]
  nlinarith [Real.exp_pos (1 / 2)]

theorem choose_le_three_pow (n k : ℕ) (hk : 0 < k) :
    (n.choose k : ℝ) ≤ (3 * n / k) ^ k := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hfact : 0 < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  calc
    (n.choose k : ℝ) ≤ (n : ℝ) ^ k / k.factorial := Nat.choose_le_pow_div k n
    _ = ((n : ℝ) / k) ^ k * ((k : ℝ) ^ k / k.factorial) := by
      rw [div_pow]
      field_simp
    _ ≤ ((n : ℝ) / k) ^ k * Real.exp k :=
      mul_le_mul_of_nonneg_left (Real.pow_div_factorial_le_exp (k : ℝ) hkR.le k) (by positivity)
    _ = ((n : ℝ) / k) ^ k * (Real.exp 1) ^ k := by rw [← Real.exp_nat_mul]; simp
    _ ≤ ((n : ℝ) / k) ^ k * 3 ^ k :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.exp_pos 1).le exp_one_le_three k) (by positivity)
    _ = (3 * n / k) ^ k := by rw [← mul_pow]; congr 1; ring

/-- A union-bound summand for t selected triples with at most floor(7t/4)
neighbors. The fourth power removes all fractional powers from the proof. -/
theorem bad_neighborhood_summand {n t : ℕ} (ht : 3 ≤ t)
    (htn : t ≤ n / ExponentialBudget.expansionScale) :
    ((n.choose (7 * t / 4) : ℝ) * (((7 * t / 4).choose 3).choose t : ℝ)) *
      (96 / (n : ℝ) ^ 2) ^ t ≤ (1 / 2 : ℝ) ^ t := by
  let r := 7 * t / 4
  have ht0 : 0 < t := by omega
  have hr0 : 0 < r := by dsimp [r]; omega
  have hscale : ExponentialBudget.expansionScale * t ≤ n := by
    simpa only [Nat.mul_comm] using
      (Nat.le_div_iff_mul_le (by norm_num [ExponentialBudget.expansionScale])).mp htn
  have hn0 : 0 < n := by norm_num [ExponentialBudget.expansionScale] at hscale; omega
  have htR : 0 < (t : ℝ) := by exact_mod_cast ht0
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr0
  have h3tr : 3 * t ≤ 2 * r := by dsimp [r]; omega
  have h4r : 4 * r ≤ 7 * t := by dsimp [r]; omega
  have htlen : t ≤ n := by norm_num [ExponentialBudget.expansionScale] at hscale; omega
  have hbase : 1 ≤ 2 * (n : ℝ) / t := by
    apply (le_div_iff₀ htR).mpr
    have h : (t : ℝ) ≤ n := by exact_mod_cast htlen
    linarith
  have hnr : 3 * (n : ℝ) / r ≤ 2 * n / t := by
    apply (div_le_div_iff₀ hrR htR).mpr
    have h : 3 * (t : ℝ) ≤ 2 * r := by exact_mod_cast h3tr
    nlinarith
  have hrbound : (r : ℝ) ≤ 7 * t / 4 := by
    have h : 4 * (r : ℝ) ≤ 7 * t := by exact_mod_cast h4r
    linarith
  have htriple : ((r.choose 3) : ℝ) ≤ (r : ℝ) ^ 3 / 6 := by
    simpa [Nat.factorial] using (Nat.choose_le_pow_div 3 r :
      (r.choose 3 : ℝ) ≤ (r : ℝ) ^ 3 / (Nat.factorial 3 : ℝ))
  have hinside : 3 * (r.choose 3 : ℝ) / t * (96 / (n : ℝ) ^ 2) ≤
      (1029 / 4 : ℝ) * t ^ 2 / n ^ 2 := by
    have hrpow := pow_le_pow_left₀ hrR.le hrbound 3
    calc
      _ = (288 * (r.choose 3 : ℝ)) / (t * (n : ℝ) ^ 2) := by ring
      _ ≤ (48 * (r : ℝ) ^ 3) / (t * (n : ℝ) ^ 2) :=
        div_le_div_of_nonneg_right (by linarith [htriple]) (by positivity)
      _ ≤ (48 * (7 * (t : ℝ) / 4) ^ 3) / (t * (n : ℝ) ^ 2) :=
        div_le_div_of_nonneg_right (by linarith [hrpow]) (by positivity)
      _ = _ := by field_simp; ring
  have hprod : ((n.choose r : ℝ) * ((r.choose 3).choose t : ℝ)) * (96 / (n : ℝ) ^ 2) ^ t ≤
      (2 * n / t) ^ r * ((1029 / 4 : ℝ) * t ^ 2 / n ^ 2) ^ t := by
    calc
      _ ≤ (3 * n / r) ^ r * (3 * (r.choose 3 : ℝ) / t) ^ t * (96 / (n : ℝ) ^ 2) ^ t :=
        mul_le_mul_of_nonneg_right (mul_le_mul (choose_le_three_pow n r hr0)
          (choose_le_three_pow (r.choose 3) t ht0) (by positivity) (by positivity)) (by positivity)
      _ = (3 * n / r) ^ r * (3 * (r.choose 3 : ℝ) / t * (96 / (n : ℝ) ^ 2)) ^ t := by
        rw [mul_assoc, ← mul_pow]
      _ ≤ _ := mul_le_mul (pow_le_pow_left₀ (by positivity) hnr r)
        (pow_le_pow_left₀ (by positivity) hinside t) (by positivity) (by positivity)
  have hfour : ((2 * (n : ℝ) / t) ^ r * ((1029 / 4 : ℝ) * t ^ 2 / n ^ 2) ^ t) ^ 4 ≤
      ((1 / 2 : ℝ) ^ t) ^ 4 := by
    calc
      _ = (2 * (n : ℝ) / t) ^ (4 * r) *
          (((1029 / 4 : ℝ) * t ^ 2 / n ^ 2) ^ 4) ^ t := by
        simp only [mul_pow, ← pow_mul]; congr 1 <;> congr 1 <;> omega
      _ ≤ (2 * (n : ℝ) / t) ^ (7 * t) *
          (((1029 / 4 : ℝ) * t ^ 2 / n ^ 2) ^ 4) ^ t :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hbase h4r) (by positivity)
      _ = ((128 * (1029 / 4 : ℝ) ^ 4) * t / n) ^ t := by
        rw [pow_mul, ← mul_pow]
        congr 1
        field_simp
        ring
      _ ≤ ((1 / 2 : ℝ) ^ 4) ^ t := by
        apply pow_le_pow_left₀ (by positivity)
        apply (div_le_iff₀ hnR).mpr
        have h : (ExponentialBudget.expansionScale : ℝ) * t ≤ n := by exact_mod_cast hscale
        norm_num [ExponentialBudget.expansionScale] at h ⊢
        linarith
      _ = _ := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  exact hprod.trans ((pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : 4 ≠ 0)).mp hfour)

end

end BoundaryLab.RandomCNFEstimates
