import Mathlib.Combinatorics.SetFamily.FourFunctions
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Explicit Bernoulli weights on finite sets

All probabilities here are finite sums of actual product weights. Normalization,
boundary-containment probabilities and positive association are proved, rather
than supplied as an abstract probabilistic interface. Positive association is
an application of Mathlib's four-functions theorem, the FKG argument for
decreasing events on the powerset lattice.
-/

namespace BoundaryLab.FiniteBernoulli

noncomputable section

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

def atom (a b : V → ℝ) (T : Finset V) : ℝ :=
  ∏ v, if v ∈ T then a v else b v

theorem atom_eq (a b : V → ℝ) (T : Finset V) :
    atom a b T = (∏ v ∈ T, a v) * ∏ v ∈ Tᶜ, b v := by
  simp [atom, Finset.prod_ite, Finset.compl_eq_univ_sdiff, Finset.sdiff_eq_filter]

theorem sum_atom (a b : V → ℝ) : ∑ T : Finset V, atom a b T = ∏ v, (a v + b v) := by
  simp only [atom_eq]
  simpa only [Finset.powerset_univ, Finset.compl_eq_univ_sdiff] using
    (Finset.prod_add a b Finset.univ).symm

def weight (p : ℝ) (T : Finset V) : ℝ := atom (fun _ => p) (fun _ => 1 - p) T

def mass (p : ℝ) (H : Finset (Finset V)) : ℝ := ∑ T ∈ H, weight p T

theorem weight_eq (p : ℝ) (T : Finset V) :
    weight p T = p ^ T.card * (1 - p) ^ (Fintype.card V - T.card) := by
  simp [weight, atom_eq, Finset.compl_eq_univ_sdiff, Finset.card_sdiff_of_subset]

theorem weight_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (T : Finset V) :
    0 ≤ weight p T := by
  rw [weight_eq]
  exact mul_nonneg (pow_nonneg hp _) (pow_nonneg (sub_nonneg.mpr hp1) _)

theorem mass_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (H : Finset (Finset V)) :
    0 ≤ mass p H := Finset.sum_nonneg (fun T _ => weight_nonneg hp hp1 T)

@[simp]
theorem mass_univ (p : ℝ) : mass p (Finset.univ : Finset (Finset V)) = 1 := by
  unfold mass weight
  rw [sum_atom]
  simp

theorem mass_mono {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    {H K : Finset (Finset V)} (hHK : H ⊆ K) : mass p H ≤ mass p K :=
  Finset.sum_le_sum_of_subset_of_nonneg hHK (fun T _ _ => weight_nonneg hp hp1 T)

theorem mass_le_one {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (H : Finset (Finset V)) :
    mass p H ≤ 1 := (mass_mono hp hp1 (Finset.subset_univ H)).trans_eq (mass_univ p)

theorem mass_eq_indicator (p : ℝ) (H : Finset (Finset V)) :
    mass p H = ∑ T : Finset V, weight p T * (if T ∈ H then 1 else 0) := by
  simp [mass, mul_ite, Finset.sum_ite_mem]

theorem mass_compl (p : ℝ) (H : Finset (Finset V)) : mass p Hᶜ = 1 - mass p H := by
  have h : mass p H + mass p Hᶜ = 1 := by
    unfold mass
    rw [Finset.sum_add_sum_compl]
    exact mass_univ p
  linarith

theorem weight_modular (p : ℝ) (T D : Finset V) :
    weight p T * weight p D = weight p (T ∩ D) * weight p (T ∪ D) := by
  unfold weight atom
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro v _
  by_cases hT : v ∈ T <;> by_cases hD : v ∈ D <;> simp [hT, hD, mul_comm]

def Lower (H : Finset (Finset V)) : Prop :=
  ∀ T ∈ H, ∀ D, D ⊆ T → D ∈ H

omit [Fintype V] in
theorem lower_inter {H K : Finset (Finset V)} (hH : Lower H) (hK : Lower K) :
    Lower (H ∩ K) := by
  intro T hT D hD
  exact Finset.mem_inter.mpr ⟨hH T (Finset.mem_inter.mp hT).1 D hD,
    hK T (Finset.mem_inter.mp hT).2 D hD⟩

/-- Harris positive association for the actual Bernoulli product weights. -/
theorem mass_inter_ge_mul {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (H K : Finset (Finset V)) (hH : Lower H) (hK : Lower K) :
    mass p H * mass p K ≤ mass p (H ∩ K) := by
  classical
  have hn (L : Finset (Finset V)) :
      0 ≤ (fun T => weight p T * (if T ∈ L then (1 : ℝ) else 0)) := by
    intro T
    exact mul_nonneg (weight_nonneg hp hp1 T) (by split <;> norm_num)
  have h := four_functions_theorem_univ
    (fun T => weight p T * (if T ∈ H then (1 : ℝ) else 0))
    (fun T => weight p T * (if T ∈ K then (1 : ℝ) else 0))
    (fun T => weight p T * (if T ∈ H ∩ K then (1 : ℝ) else 0)) (weight p)
    (hn H) (hn K) (hn (H ∩ K)) (fun T => weight_nonneg hp hp1 T) (fun T D => by
      change (weight p T * (if T ∈ H then 1 else 0)) *
          (weight p D * (if D ∈ K then 1 else 0)) ≤
        (weight p (T ∩ D) * (if T ∩ D ∈ H ∩ K then 1 else 0)) * weight p (T ∪ D)
      by_cases hT : T ∈ H
      · by_cases hD : D ∈ K
        · have hi : T ∩ D ∈ H ∩ K := Finset.mem_inter.mpr
            ⟨hH T hT _ Finset.inter_subset_left, hK D hD _ Finset.inter_subset_right⟩
          simpa [hT, hD, hi] using (weight_modular p T D).le
        · simp only [hD, ite_false, mul_zero]
          exact mul_nonneg (hn (H ∩ K) _) (weight_nonneg hp hp1 _)
      · simp only [hT, ite_false, mul_zero, zero_mul]
        exact mul_nonneg (hn (H ∩ K) _) (weight_nonneg hp hp1 _))
  have htotal : (∑ T : Finset V, weight p T) = 1 := mass_univ p
  simpa only [← mass_eq_indicator, htotal, mul_one] using h

def containing (D : Finset V) : Finset (Finset V) := Finset.univ.filter (D ⊆ ·)

def avoiding (D : Finset V) : Finset (Finset V) := (containing D)ᶜ

@[simp]
theorem mem_avoiding (D T : Finset V) : T ∈ avoiding D ↔ ¬ D ⊆ T := by
  simp [avoiding, containing]

theorem avoiding_lower (D : Finset V) : Lower (avoiding D) := by
  intro T hT U hU
  simp only [mem_avoiding] at hT ⊢
  exact fun hD => hT (hD.trans hU)

/-- Boundary events may overlap; each individual containment probability is exact. -/
theorem mass_containing (p : ℝ) (D : Finset V) : mass p (containing D) = p ^ D.card := by
  have hatom (T : Finset V) :
      atom (fun _ : V => p) (fun v => if v ∈ D then 0 else 1 - p) T =
        weight p T * (if T ∈ containing D then 1 else 0) := by
    by_cases hD : D ⊆ T
    · simp only [containing, Finset.mem_filter, Finset.mem_univ, true_and, hD,
        ite_true, mul_one]
      unfold atom weight
      apply Finset.prod_congr rfl
      intro v _
      by_cases hv : v ∈ T
      · simp [hv]
      · have hvD : v ∉ D := fun h => hv (hD h)
        simp [hv, hvD]
    · simp only [containing, Finset.mem_filter, Finset.mem_univ, true_and, hD,
        ite_false, mul_zero]
      obtain ⟨v, hvD, hvT⟩ := Finset.not_subset.mp hD
      exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp [hvD, hvT])
  rw [mass_eq_indicator]
  simp_rw [← hatom]
  rw [sum_atom]
  have heq : (fun v : V => p + (if v ∈ D then 0 else 1 - p)) =
      (fun v : V => if v ∈ D then p else 1) := by
    funext v
    split <;> simp_all
  rw [heq]
  simp

theorem mass_avoiding (p : ℝ) (D : Finset V) : mass p (avoiding D) = 1 - p ^ D.card := by
  rw [avoiding, mass_compl, mass_containing]

def avoidAll {J : Type*} (A : Finset J) (D : J → Finset V) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter (fun T => ∀ j ∈ A, ¬ D j ⊆ T)

@[simp]
theorem mem_avoidAll {J : Type*} (A : Finset J) (D : J → Finset V) (T : Finset V) :
    T ∈ avoidAll A D ↔ ∀ j ∈ A, ¬ D j ⊆ T := by
  classical
  simp [avoidAll]

theorem avoidAll_lower {J : Type*} (A : Finset J) (D : J → Finset V) :
    Lower (avoidAll A D) := by
  intro T hT U hUT
  simp only [mem_avoidAll] at hT ⊢
  exact fun j hj hD => hT j hj (hD.trans hUT)

/-- Repeated boundaries are permitted; no independence between events is used. -/
theorem product_le_mass_avoidAll {J : Type*} {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Finset J) (D : J → Finset V) :
    (∏ j ∈ A, (1 - p ^ (D j).card)) ≤ mass p (avoidAll A D) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [avoidAll]
  | @insert j A hj ih =>
    have heq : avoidAll (insert j A) D = avoiding (D j) ∩ avoidAll A D := by
      ext T
      simp
    rw [Finset.prod_insert hj, heq]
    calc
      _ ≤ mass p (avoiding (D j)) * mass p (avoidAll A D) := by
        rw [mass_avoiding]
        exact mul_le_mul_of_nonneg_left ih (by
          rw [← mass_avoiding]
          exact mass_nonneg hp hp1 _)
      _ ≤ _ := mass_inter_ge_mul hp hp1 _ _ (avoiding_lower _) (avoidAll_lower A D)

def layer (H : Finset (Finset V)) (k : ℕ) : Finset (Finset V) := H.filter (·.card = k)

theorem mass_layer (p : ℝ) (H : Finset (Finset V)) (k : ℕ) :
    mass p (layer H k) = (layer H k).card * p ^ k * (1 - p) ^ (Fintype.card V - k) := by
  unfold mass
  calc
    _ = ∑ _T ∈ layer H k, p ^ k * (1 - p) ^ (Fintype.card V - k) := by
      apply Finset.sum_congr rfl
      intro T hT
      rw [weight_eq, (Finset.mem_filter.mp hT).2]
    _ = _ := by simp [mul_assoc]

omit [DecidableEq V] in
theorem layer_univ (k : ℕ) :
    layer (Finset.univ : Finset (Finset V)) k = Finset.univ.powersetCard k := by
  ext T
  simp [layer]

theorem mass_card_eq (p : ℝ) (k : ℕ) :
    mass p (Finset.univ.powersetCard k : Finset (Finset V)) =
      (Fintype.card V).choose k * p ^ k * (1 - p) ^ (Fintype.card V - k) := by
  rw [← layer_univ, mass_layer, layer_univ]
  simp

def window (H : Finset (Finset V)) (K : Finset ℕ) : Finset (Finset V) :=
  H.filter (fun T => T.card ∈ K)

theorem mass_window (p : ℝ) (H : Finset (Finset V)) (K : Finset ℕ) :
    mass p (window H K) = ∑ k ∈ K, mass p (layer H k) := by
  unfold mass window layer
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T _
  simp

theorem mass_window_ge_sub {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (H : Finset (Finset V)) (K : Finset ℕ) :
    mass p H - mass p (window (Finset.univ : Finset (Finset V)) K)ᶜ ≤ mass p (window H K) := by
  have hsplit : mass p H = mass p (window H K) + mass p (H.filter (fun T => T.card ∉ K)) := by
    simp only [mass, window, Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro T _
    by_cases h : T.card ∈ K <;> simp [h]
  have hle : mass p (H.filter (fun T => T.card ∉ K)) ≤
      mass p (window (Finset.univ : Finset (Finset V)) K)ᶜ := by
    apply mass_mono hp hp1
    intro T hT
    simpa [window] using (Finset.mem_filter.mp hT).2
  linarith

/-- Positive good mass in a size window gives one dense uniform layer. The
binomial weights and layer cardinalities are derived from the actual measure. -/
theorem exists_dense_layer {p δ : ℝ} (hp : 0 < p) (hp1 : p < 1) (hδ : 0 < δ)
    (H : Finset (Finset V)) (K : Finset ℕ) (hgood : δ ≤ mass p (window H K)) :
    ∃ k ∈ K, δ * ((Fintype.card V).choose k : ℝ) ≤ (layer H k).card := by
  classical
  by_contra hnone
  push Not at hnone
  have hK : K.Nonempty := by
    by_contra he
    have heq : K = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    simp [heq, window, mass] at hgood
    linarith
  have hterm (k : ℕ) (hk : k ∈ K) :
      mass p (layer H k) < δ * mass p (layer (Finset.univ : Finset (Finset V)) k) := by
    have hlt := mul_lt_mul_of_pos_right (hnone k hk)
      (mul_pos (pow_pos hp k) (pow_pos (sub_pos.mpr hp1) (Fintype.card V - k)))
    rw [mass_layer, mass_layer, layer_univ]
    simpa only [Finset.card_powersetCard, Finset.card_univ, mul_assoc] using hlt
  have hs : mass p (window H K) < δ * mass p (window (Finset.univ : Finset (Finset V)) K) := by
    rw [mass_window, mass_window, Finset.mul_sum]
    exact Finset.sum_lt_sum_of_nonempty hK hterm
  have hfull := mul_le_mul_of_nonneg_left (mass_le_one hp.le hp1.le
    (window (Finset.univ : Finset (Finset V)) K)) hδ.le
  linarith

end

end BoundaryLab.FiniteBernoulli
