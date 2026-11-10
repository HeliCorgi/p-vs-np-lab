import ProofLab.ExpanderDensityDAG
import Mathlib.Data.Nat.Choose.Bounds

/-!
# From the finite dimension budget to an exponential lower bound

The binomial sum, loss in the density exponent, and integer rounding are
estimated here. No asymptotic comparison or numerical inequality is postulated.
-/

namespace BoundaryLab.ExponentialBudget

noncomputable section

open scoped BigOperators
open BooleanFunctionSpace

/-- Below one third of the row, the truncated binomial sum is at most twice
its last coefficient. This proof uses the exact adjacent-coefficient identity. -/
theorem sum_choose_le_twice {N k : ℕ} (hk : 3 * k ≤ N + 1) :
    (∑ j ∈ Finset.range (k + 1), N.choose j) ≤ 2 * N.choose k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hkN : k ≤ N := by omega
    have hc := Nat.choose_succ_right_eq N k
    have hratio : 2 * N.choose k ≤ N.choose (k + 1) := by
      have hnk : 2 * (k + 1) ≤ N - k := by omega
      have h := Nat.mul_le_mul_left (N.choose k) hnk
      rw [← hc] at h
      nlinarith
    rw [Finset.sum_range_succ]
    have hprev := ih (by omega)
    omega

theorem booleanBudget_le_twice {N k : ℕ} (hk : k ≤ N) (hthird : 3 * k ≤ N + 1) :
    booleanBudget k N ≤ 2 * N.choose k := by
  simpa only [booleanBudget, Nat.min_eq_left hk] using sum_choose_le_twice hthird

theorem choose_step_decay {n t k : ℕ} (hk : k ≤ t) (ht : t + 1 ≤ n) :
    (t.choose k : ℝ) ≤ Real.exp (-(k : ℝ) / n) * ((t + 1).choose k : ℝ) := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have ht0 : 0 < (t : ℝ) + 1 := by positivity
  have hId : (t.choose k : ℝ) * ((t : ℝ) + 1) =
      ((t + 1).choose k : ℝ) * ((t : ℝ) + 1 - k) := by
    have h := congrArg (fun a : ℕ => (a : ℝ)) (Nat.choose_mul_succ_eq t k)
    push_cast [Nat.cast_sub (by omega : k ≤ t + 1)] at h
    exact h
  have heq : (t.choose k : ℝ) =
      (1 - (k : ℝ) / ((t : ℝ) + 1)) * ((t + 1).choose k : ℝ) := by
    field_simp
    nlinarith [hId]
  rw [heq]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  calc
    1 - (k : ℝ) / ((t : ℝ) + 1) ≤ 1 - (k : ℝ) / n := by
      have htn : (t : ℝ) + 1 ≤ n := by exact_mod_cast ht
      have hdiv := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ k by positivity) ht0 htn
      linarith
    _ ≤ Real.exp (-(k : ℝ) / n) := by
      simpa only [neg_div] using Real.one_sub_le_exp_neg ((k : ℝ) / n)

theorem choose_decay {n t k d : ℕ} (hk : k ≤ t) (ht : t + d ≤ n) :
    (t.choose k : ℝ) ≤ Real.exp (-(d : ℝ) * k / n) * ((t + d).choose k : ℝ) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hprev := ih (by omega)
    have hstep := choose_step_decay (n := n) (t := t + d) (k := k) (by omega) (by omega)
    have hm := mul_le_mul_of_nonneg_left hstep
      (Real.exp_pos (-(d : ℝ) * k / n)).le
    have he : Real.exp (-(d : ℝ) * k / n) * Real.exp (-(k : ℝ) / n) =
        Real.exp (-((d + 1 : ℕ) : ℝ) * k / n) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    calc
      (t.choose k : ℝ) ≤ Real.exp (-(d : ℝ) * k / n) * ((t + d).choose k : ℝ) := hprev
      _ ≤ (Real.exp (-(d : ℝ) * k / n) * Real.exp (-(k : ℝ) / n)) *
          ((t + d + 1).choose k : ℝ) := by simpa only [mul_assoc] using hm
      _ = _ := by rw [he, Nat.add_assoc]

/-- Exponential gain from deleting d ambient coordinates, with no product
formula or positivity of a denominator left as a hypothesis. -/
theorem choose_exponential_gain {n N k : ℕ} (hk : k ≤ N) (hN : N ≤ n) :
    Real.exp (((n - N : ℕ) : ℝ) * k / n) * (N.choose k : ℝ) ≤ (n.choose k : ℝ) := by
  have hd := choose_decay (n := n) (t := N) (k := k) (d := n - N) hk (by omega)
  have hm := mul_le_mul_of_nonneg_left hd
    (Real.exp_pos (((n - N : ℕ) : ℝ) * k / n)).le
  have hcancel : Real.exp (((n - N : ℕ) : ℝ) * k / n) *
      Real.exp (-((n - N : ℕ) : ℝ) * k / n) = 1 := by
    rw [← Real.exp_add]
    have hz : ((n - N : ℕ) : ℝ) * k / n + -((n - N : ℕ) : ℝ) * k / n = 0 := by ring
    rw [hz, Real.exp_zero]
  simpa only [← mul_assoc, hcancel, one_mul, Nat.add_sub_of_le hN] using hm

def expansionScale : ℕ := 10 ^ 16
def probabilityDenominator : ℕ := 1024 * 12288 ^ 4 * expansionScale
def samplingProbability : ℝ := 1 / probabilityDenominator
def numericalThreshold : ℕ := 16 * probabilityDenominator
def expansionSize (n : ℕ) : ℕ := n / expansionScale
def rankThreshold (n : ℕ) : ℕ := expansionSize n / 16
def exponentDenominator : ℕ := 81 * 2 ^ 65 * 10 ^ 32

theorem probability_pos : 0 < samplingProbability := by
  norm_num [samplingProbability, probabilityDenominator, expansionScale]

theorem probability_parameters :
    samplingProbability = (1 / (expansionScale : ℝ)) /
      (1024 * (((max 1 (3 * 4096) : ℕ) : ℝ) ^ 2) ^ 2) := by
  norm_num [samplingProbability, probabilityDenominator, expansionScale]

theorem threshold_mean {n : ℕ} (hn : numericalThreshold ≤ n) :
    16 ≤ samplingProbability * n := by
  norm_num [numericalThreshold, probabilityDenominator, expansionScale] at hn
  have h : (3735465674926184202240000000000000000 : ℝ) ≤ n := by exact_mod_cast hn
  norm_num [samplingProbability, probabilityDenominator, expansionScale]
  linarith

/-- All integer degree and dimension room, including the truncated subtraction
in the target dimension, follows from the explicit threshold. -/
theorem integer_room {n k : ℕ} (hn : numericalThreshold ≤ n)
    (hhi : (k : ℝ) ≤ 2 * (samplingProbability * n)) :
    3 ≤ rankThreshold n ∧ 4 * (k + 3 * rankThreshold n) ≤ expansionSize n ∧
      k ≤ n - rankThreshold n - 1 ∧
      3 * k ≤ (n - rankThreshold n - 1) + 1 ∧ rankThreshold n + 1 ≤ n := by
  have hk : probabilityDenominator * k ≤ 2 * n := by
    have h : (probabilityDenominator : ℝ) * k ≤ 2 * n := by
      norm_num [samplingProbability, probabilityDenominator, expansionScale] at *
      linarith
    exact_mod_cast h
  norm_num [numericalThreshold, probabilityDenominator, expansionScale,
    rankThreshold, expansionSize] at *
  omega

theorem exponent_denominator_eq :
    exponentDenominator = 128 * expansionScale * probabilityDenominator := by
  norm_num [exponentDenominator, expansionScale, probabilityDenominator]

/-- The rounding loss in R and the loss in good-set density are both included
in the exponent, rather than hidden in an asymptotic notation. -/
theorem exponent_gain {n k : ℕ} (hn : numericalThreshold ≤ n)
    (hlo : samplingProbability * n / 2 ≤ (k : ℝ)) :
    (n : ℝ) / exponentDenominator ≤
      ((rankThreshold n + 1 : ℕ) : ℝ) * k / n -
        168 * n * (((max 1 (3 * 4096) : ℕ) : ℝ) ^ 2) ^ 4 * samplingProbability ^ 3 := by
  have hn0 : 0 < n := by
    norm_num [numericalThreshold, probabilityDenominator, expansionScale] at hn
    omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
  have hround : n < (rankThreshold n + 1) * (16 * expansionScale) := by
    unfold rankThreshold expansionSize
    rw [Nat.div_div_eq_div_mul]
    have h := Nat.lt_mul_div_succ n (by norm_num [expansionScale] : 0 < expansionScale * 16)
    nlinarith [h]
  have hroundR : (n : ℝ) / (16 * expansionScale) ≤ ((rankThreshold n + 1 : ℕ) : ℝ) := by
    have h : (n : ℝ) ≤ ((rankThreshold n + 1 : ℕ) : ℝ) * (16 * expansionScale) := by
      exact_mod_cast hround.le
    exact (div_le_iff₀ (by norm_num [expansionScale] : (0 : ℝ) < 16 * expansionScale)).mpr h
  have hprod := mul_le_mul hroundR hlo
    (show 0 ≤ samplingProbability * n / 2 by positivity [probability_pos])
    (show (0 : ℝ) ≤ ((rankThreshold n + 1 : ℕ) : ℝ) by positivity)
  have hdiv := div_le_div_of_nonneg_right hprod hnR.le
  have heq : ((n : ℝ) / (16 * expansionScale) * (samplingProbability * n / 2)) / n =
      samplingProbability * n / (32 * expansionScale) := by
    field_simp
    ring
  rw [heq] at hdiv
  norm_num [samplingProbability, probabilityDenominator, expansionScale,
    exponentDenominator] at *
  linarith

/-- The exact finite budget implies the requested exponential estimate. -/
theorem exponential_of_budget {n k H : ℕ} (hn : numericalThreshold ≤ n)
    (hlo : samplingProbability * n / 2 ≤ (k : ℝ))
    (hhi : (k : ℝ) ≤ 2 * (samplingProbability * n))
    (hbudget : ((1 / 2 : ℝ) * Real.exp (-168 * n *
        (((max 1 (3 * 4096) : ℕ) : ℝ) ^ 2) ^ 4 * samplingProbability ^ 3)) *
      (n.choose k : ℝ) ≤ H * (booleanBudget k (n - rankThreshold n - 1) : ℝ)) :
    (1 / 4 : ℝ) * Real.exp ((n : ℝ) / exponentDenominator) ≤ H := by
  obtain ⟨_, _, hkN, hthird, hRn⟩ := integer_room hn hhi
  let N := n - rankThreshold n - 1
  let a : ℝ := 168 * n * (((max 1 (3 * 4096) : ℕ) : ℝ) ^ 2) ^ 4 * samplingProbability ^ 3
  let g : ℝ := ((rankThreshold n + 1 : ℕ) : ℝ) * k / n
  have hc : 0 < (N.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hkN
  have hb : (booleanBudget k N : ℝ) ≤ 2 * (N.choose k : ℝ) := by
    exact_mod_cast booleanBudget_le_twice hkN hthird
  have hg : Real.exp g * (N.choose k : ℝ) ≤ (n.choose k : ℝ) := by
    have h := choose_exponential_gain hkN (show N ≤ n by omega)
    have heq : n - N = rankThreshold n + 1 := by omega
    change Real.exp (((n - N : ℕ) : ℝ) * k / n) * (N.choose k : ℝ) ≤ (n.choose k : ℝ) at h
    rw [heq] at h
    exact h
  have hlow := mul_le_mul_of_nonneg_left hg
    (show 0 ≤ (1 / 2 : ℝ) * Real.exp (-a) by positivity)
  have hhigh := mul_le_mul_of_nonneg_left hb (show (0 : ℝ) ≤ H by positivity)
  have hbudget' : (1 / 2 : ℝ) * Real.exp (-a) * (n.choose k : ℝ) ≤
      H * (booleanBudget k N : ℝ) := by simpa only [a, neg_mul] using hbudget
  have hmid : (1 / 2 : ℝ) * Real.exp (-a) * (Real.exp g * (N.choose k : ℝ)) ≤
      H * (2 * (N.choose k : ℝ)) := hlow.trans (hbudget'.trans hhigh)
  have he : Real.exp (-a) * Real.exp g = Real.exp (g - a) := by
    rw [← Real.exp_add]; congr 1; ring
  have hcancel : (1 / 4 : ℝ) * Real.exp (g - a) ≤ H := by
    have h : ((1 / 2 : ℝ) * Real.exp (g - a)) * (N.choose k : ℝ) ≤
        (2 * H) * (N.choose k : ℝ) := by
      rw [← he]
      nlinarith [hmid]
    have h' := (mul_le_mul_iff_left₀ hc).mp h
    linarith
  exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (exponent_gain hn hlo))
    (by norm_num : (0 : ℝ) ≤ 1 / 4)).trans hcancel

open ExpanderSupport ExpanderObstructions LinearClauseBoundary BooleanIdealNormalForm

/-- For every support family with the paper's structural properties, the
original-variable affine-clause DAG lower bound has the stated explicit
exponent. Only the support-family existence question remains external here. -/
theorem bounded_occurrence_exponential_dag
    {I V : Type} [Fintype I] [DecidableEq I] [Fintype V] [LinearOrder V]
    {E : I → Finset V} (hn : numericalThreshold ≤ Fintype.card V)
    (hexp : HalfBoundaryExpander E (expansionSize (Fintype.card V)))
    (hwidth : ∀ i, (E i).card = 3) (hlinear : LinearSupports E)
    (hocc : ∀ v, (occurrences E v).card ≤ 4096)
    (hm : Fintype.card I = 12 * Fintype.card V)
    (sign : I → V → Bool) (S : ℕ)
    (clauses : Fin S → AffineIndicators.Clause V) (initial : Fin S → Bool)
    (dag : AffineClauseDAG.ClauseDAG (clauseBase E sign Finset.univ) clauses initial)
    (hAffine : ∀ i, AffineIndicators.IsAffineClause (clauses i))
    (hinputWidth : ∀ i, initial i = true → (clauses i).card ≤ 3)
    (finish : Fin S) (hfinish : clauses finish = ∅) :
    (1 / 4 : ℝ) * Real.exp ((Fintype.card V : ℝ) / exponentDenominator) ≤
      (DistinctAffineFlats.distinctFlats clauses
        (fun i => AffineIndicators.spanRank (clauses i) ≤ rankThreshold (Fintype.card V))).card ∧
    (1 / 4 : ℝ) * Real.exp ((Fintype.card V : ℝ) / exponentDenominator) ≤ S := by
  obtain ⟨k, _, hlo, hhi, hb⟩ := ExpanderDensityDAG.bounded_occurrence_dense_dag_budget
    hexp hwidth hlinear hocc hm (by norm_num [expansionScale] : (0 : ℝ) < 1 / expansionScale)
    (by norm_num [expansionScale] : (1 : ℝ) / expansionScale ≤ 1)
    probability_parameters (threshold_mean hn)
  obtain ⟨hR, hroom, _, _, _⟩ := integer_room hn hhi
  obtain ⟨hd, hs⟩ := hb sign (rankThreshold (Fintype.card V)) S hR hroom clauses initial
    dag hAffine (fun i hi => (hinputWidth i hi).trans hR) finish hfinish
  exact ⟨exponential_of_budget hn hlo hhi hd, exponential_of_budget hn hlo hhi hs⟩

end

end BoundaryLab.ExponentialBudget
