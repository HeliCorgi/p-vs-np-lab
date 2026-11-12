import ProofLab.BoundaryProbabilitySum
import ProofLab.ExpanderDAGLowerBound

/-!
# Quantitative density of the actual separated monomial space

This composes connected obstruction extraction, walk counting, linear-triple
boundary bounds, positive association, binomial tails and uniform-layer
selection. The expander and occurrence hypotheses are retained; no density,
probability, connected-count or PC-separation hypothesis is postulated.
-/

namespace BoundaryLab.ExpanderDensity

noncomputable section

open ExpanderSupport ExpanderObstructions ConnectedSetCounting LinearClauseBoundary
open FiniteBernoulli BernoulliBounds BoundaryProbabilitySum ExpanderMonomials
open scoped BigOperators

variable {I V : Type} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]

theorem goodFamily_mass_ge {E : I → Finset V} {s : ℕ}
    (hexp : HalfBoundaryExpander E s) (hwidth : ∀ i, (E i).card = 3)
    (hlinear : LinearSupports E) (q : ℕ) (hq1 : 1 ≤ q)
    (hq : ∀ i, (neighbors (intersectionGraph E) i).card ≤ q)
    {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (hp3 : p ^ 3 ≤ 1 / 2)
    (hr : ((q : ℝ) ^ 2) ^ 2 * p ≤ 1 / 2) :
    Real.exp (-14 * Fintype.card I * ((q : ℝ) ^ 2) ^ 4 * p ^ 3) ≤
      mass p (goodFamily E s) := by
  have hsum := boundary_probability_sum_le hexp hwidth hlinear q hq1 hq hp hp1 hr
  have hhalf : ∀ A ∈ connectedObstructions E s, p ^ (boundary E A).card ≤ 1 / 2 := by
    intro A hA
    exact (pow_le_pow_of_le_one hp hp1 (three_le_boundary hexp hwidth hlinear A
      ((mem_connectedObstructions E s A).mp hA).2.1
      ((mem_connectedObstructions E s A).mp hA).1)).trans hp3
  exact (Real.exp_le_exp.mpr (by nlinarith [hsum])).trans
    (exp_le_mass_goodFamily E s hp hp1 hhalf)

/-- The paper's density estimate with its explicit numerical tail gate. All
probabilistic and combinatorial bounds needed for it are proved internally. -/
theorem exists_dense_goodSupports {E : I → Finset V} {s : ℕ}
    (hexp : HalfBoundaryExpander E s) (hwidth : ∀ i, (E i).card = 3)
    (hlinear : LinearSupports E) (q : ℕ) (hq1 : 1 ≤ q)
    (hq : ∀ i, (neighbors (intersectionGraph E) i).card ≤ q)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (hp3 : p ^ 3 ≤ 1 / 2)
    (hr : ((q : ℝ) ^ 2) ^ 2 * p ≤ 1 / 2)
    (htail : 2 * Real.exp (-(p * Fintype.card V) / 8) ≤
      (1 / 2) * Real.exp (-14 * Fintype.card I * ((q : ℝ) ^ 2) ^ 4 * p ^ 3)) :
    ∃ k, k ≤ Fintype.card V ∧ p * Fintype.card V / 2 ≤ (k : ℝ) ∧
      (k : ℝ) ≤ 2 * (p * Fintype.card V) ∧
      ((1 / 2) * Real.exp (-14 * Fintype.card I * ((q : ℝ) ^ 2) ^ 4 * p ^ 3)) *
        ((Fintype.card V).choose k : ℝ) ≤ (goodSupports E s k).card := by
  have hδ : 0 < (1 / 2 : ℝ) * Real.exp (-14 * Fintype.card I * ((q : ℝ) ^ 2) ^ 4 * p ^ 3) := by
    positivity
  obtain ⟨k, hk, hd⟩ := exists_dense_layer hp hp1 hδ (goodFamily E s)
    (centralSizes (Fintype.card V) p) (by
      have hg := goodFamily_mass_ge hexp hwidth hlinear q hq1 hq hp.le hp1.le hp3 hr
      have ht := mass_outside_central (V := V) hp.le hp1.le
      have hw := mass_window_ge_sub hp.le hp1.le (goodFamily E s) (centralSizes (Fintype.card V) p)
      linarith)
  obtain ⟨hkn, hlo, hhi⟩ := (mem_centralSizes _ _ _).mp hk
  exact ⟨k, hkn, hlo, hhi, by simpa only [← goodSupports_eq_layer] using hd⟩

theorem tail_gate {μ a : ℝ} (hμ : 16 ≤ μ) (ha : a ≤ μ / 4096) :
    2 * Real.exp (-μ / 8) ≤ (1 / 2) * Real.exp (-a) := by
  have hdiff : 7 / 4 ≤ μ / 8 - a := by linarith
  have h4 : 4 ≤ Real.exp (μ / 8 - a) := by
    have h := Real.quadratic_le_exp_of_nonneg (x := μ / 8 - a) (by linarith)
    nlinarith
  have h := mul_le_mul_of_nonneg_right h4 (Real.exp_pos (-μ / 8)).le
  rw [← Real.exp_add] at h
  have heq : μ / 8 - a + -μ / 8 = -a := by ring
  rw [heq] at h
  linarith

/-- The numerical choices in the paper discharge the tail gate. -/
theorem small_parameter_bounds {C ε p n : ℝ}
    (hC : 1 ≤ C) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hpdef : p = ε / (1024 * C ^ 2)) (hpn : 16 ≤ p * n) :
    0 < p ∧ p < 1 ∧ p ^ 3 ≤ 1 / 2 ∧ C ^ 2 * p ≤ 1 / 2 ∧
      2 * Real.exp (-(p * n) / 8) ≤ (1 / 2) * Real.exp (-168 * n * C ^ 4 * p ^ 3) := by
  have hC0 : 0 < C := by linarith
  have hC2 : 1 ≤ C ^ 2 := by nlinarith
  have hp : 0 < p := by rw [hpdef]; positivity
  have heq : 1024 * C ^ 2 * p = ε := by
    rw [hpdef]
    field_simp
  have hr : C ^ 2 * p ≤ 1 / 1024 := by nlinarith
  have hr0 : 0 ≤ C ^ 2 * p := by positivity
  have hple : p ≤ 1 / 1024 := by nlinarith [mul_le_mul_of_nonneg_right hC2 hp.le]
  have hp1 : p < 1 := by linarith
  have hp3 : p ^ 3 ≤ 1 / 2 := by
    have h := pow_le_pow_of_le_one hp.le hp1.le (by omega : 1 ≤ 3)
    simp only [pow_one] at h
    linarith
  refine ⟨hp, hp1, hp3, by linarith, ?_⟩
  have hr2 : (C ^ 2 * p) ^ 2 ≤ (1 / 1024 : ℝ) ^ 2 := pow_le_pow_left₀ hr0 hr 2
  have hc : 168 * (C ^ 2 * p) ^ 2 ≤ 1 / 4096 := by nlinarith
  have hμ : 0 ≤ p * n := by linarith
  have ha : 168 * n * C ^ 4 * p ^ 3 ≤ (p * n) / 4096 := by
    have h := mul_le_mul_of_nonneg_left hc hμ
    nlinarith [h]
  simpa only [neg_mul] using tail_gate hpn ha

/-- Density for every bounded-occurrence proper linear 3-CNF support family
with m=12n and the stated expansion. Existence of that family is not assumed
proved: E and its structural properties are explicit inputs. -/
theorem bounded_occurrence_dense_goodSupports {E : I → Finset V} {s Δ : ℕ}
    (hexp : HalfBoundaryExpander E s) (hwidth : ∀ i, (E i).card = 3)
    (hlinear : LinearSupports E) (hocc : ∀ v, (occurrences E v).card ≤ Δ)
    (hm : Fintype.card I = 12 * Fintype.card V)
    {ε p : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hpdef : p = ε / (1024 * (((max 1 (3 * Δ) : ℕ) : ℝ) ^ 2) ^ 2))
    (hpn : 16 ≤ p * Fintype.card V) :
    ∃ k, k ≤ Fintype.card V ∧ p * Fintype.card V / 2 ≤ (k : ℝ) ∧
      (k : ℝ) ≤ 2 * (p * Fintype.card V) ∧
      ((1 / 2) * Real.exp (-168 * Fintype.card V *
        (((max 1 (3 * Δ) : ℕ) : ℝ) ^ 2) ^ 4 * p ^ 3)) *
        ((Fintype.card V).choose k : ℝ) ≤ (goodSupports E s k).card := by
  let q := max 1 (3 * Δ)
  have hq1 : 1 ≤ q := le_max_left _ _
  have hC : 1 ≤ (q : ℝ) ^ 2 := by
    have h : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    nlinarith
  obtain ⟨hp, hp1, hp3, hr, ht⟩ := small_parameter_bounds hC hε hε1 hpdef hpn
  have hq : ∀ i, (neighbors (intersectionGraph E) i).card ≤ q := fun i =>
    (intersection_neighbors_card_le E 3 Δ (fun i => (hwidth i).le) hocc i).trans (le_max_right _ _)
  have hmR : (Fintype.card I : ℝ) = 12 * Fintype.card V := by exact_mod_cast hm
  have hex : -14 * (Fintype.card I : ℝ) * ((q : ℝ) ^ 2) ^ 4 * p ^ 3 =
      -168 * Fintype.card V * ((q : ℝ) ^ 2) ^ 4 * p ^ 3 := by rw [hmR]; ring
  have hd := exists_dense_goodSupports hexp hwidth hlinear q hq1 hq hp hp1 hp3 hr
    (by rw [hex]; exact ht)
  simpa only [hex] using hd

end

end BoundaryLab.ExpanderDensity
