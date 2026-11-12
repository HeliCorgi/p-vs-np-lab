import ProofLab.LinearClauseBoundary

/-!
# The quantitative sum of connected boundary probabilities

For a proper linear 3-uniform family with strict half-boundary expansion and
intersection-graph degree at most q, C=q² gives the paper bound 7 m C⁴ p³.
All connected-set counts and boundary-size estimates are proved in the imports;
the finite geometric-series estimate is proved here.
-/

namespace BoundaryLab.BoundaryProbabilitySum

noncomputable section

open ExpanderSupport ExpanderObstructions ConnectedSetCounting LinearClauseBoundary
open scoped BigOperators

theorem sum_pairs (f : ℕ → ℝ) (n : ℕ) :
    (∑ t ∈ Finset.range (2 * n), f (6 + t)) =
      ∑ j ∈ Finset.range n, (f (2 * j + 6) + f (2 * j + 7)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
    simp only [Finset.sum_range_succ]
    rw [ih]
    have h6 : 6 + 2 * n = 2 * n + 6 := by omega
    have h7 : 6 + (2 * n + 1) = 2 * n + 7 := by omega
    rw [h6, h7]
    ring

theorem finite_envelope_bound (f : ℕ → ℝ) (M C p : ℝ)
    (hM : 0 ≤ M) (hC : 1 ≤ C) (hp : 0 ≤ p) (hr : C ^ 2 * p ≤ 1 / 2)
    (h0 : ∀ t, 0 ≤ f t) (hz : f 0 = 0)
    (hlow : ∀ t, 1 ≤ t → t ≤ 5 → f t ≤ M * C ^ 4 * p ^ 3)
    (heven : ∀ j, f (2 * j + 6) ≤ M * C ^ 6 * p ^ 4 * (C ^ 2 * p) ^ j)
    (hodd : ∀ j, f (2 * j + 7) ≤ M * C ^ 6 * p ^ 4 * (C ^ 2 * p) ^ j)
    (s : ℕ) : (∑ t ∈ Finset.range (s + 1), f t) ≤ 7 * M * C ^ 4 * p ^ 3 := by
  have hC0 : 0 ≤ C := by linarith
  have hr0 : 0 ≤ C ^ 2 * p := mul_nonneg (sq_nonneg C) hp
  have hgeom : (∑ j ∈ Finset.range (s + 1), (C ^ 2 * p) ^ j) ≤ 2 := by
    exact (Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ hr0 hr j)).trans
      (sum_geometric_two_le (s + 1))
  have hfirst : (∑ t ∈ Finset.range 6, f t) ≤ 5 * M * C ^ 4 * p ^ 3 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hz, zero_add]
    linarith [hlow 1 (by omega) (by omega), hlow 2 (by omega) (by omega),
      hlow 3 (by omega) (by omega), hlow 4 (by omega) (by omega), hlow 5 (by omega) (by omega)]
  have htail : (∑ j ∈ Finset.range (s + 1), (f (2 * j + 6) + f (2 * j + 7))) ≤
      4 * M * C ^ 6 * p ^ 4 := by
    calc
      _ ≤ ∑ j ∈ Finset.range (s + 1), 2 * M * C ^ 6 * p ^ 4 * (C ^ 2 * p) ^ j := by
        apply Finset.sum_le_sum
        intro j _
        linarith [heven j, hodd j]
      _ = (2 * M * C ^ 6 * p ^ 4) * ∑ j ∈ Finset.range (s + 1), (C ^ 2 * p) ^ j :=
        (Finset.mul_sum ..).symm
      _ ≤ (2 * M * C ^ 6 * p ^ 4) * 2 := mul_le_mul_of_nonneg_left hgeom (by positivity)
      _ = _ := by ring
  have htail' : 4 * M * C ^ 6 * p ^ 4 ≤ 2 * M * C ^ 4 * p ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hr (show 0 ≤ 4 * M * C ^ 4 * p ^ 3 by positivity)
    nlinarith [h]
  have hlarge : (∑ t ∈ Finset.range (s + 1), f t) ≤
      ∑ t ∈ Finset.range (6 + 2 * (s + 1)), f t :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun t _ _ => h0 t)
  rw [Finset.sum_range_add f 6 (2 * (s + 1)), sum_pairs] at hlarge
  linarith

variable {I V : Type} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]

def boundaryMassAt (E : I → Finset V) (s : ℕ) (p : ℝ) (t : ℕ) : ℝ :=
  ∑ A ∈ (connectedObstructions E s).filter (fun A => A.card = t), p ^ (boundary E A).card

theorem boundaryMassAt_nonneg (E : I → Finset V) (s : ℕ) {p : ℝ} (hp : 0 ≤ p) (t : ℕ) :
    0 ≤ boundaryMassAt E s p t := Finset.sum_nonneg (fun _ _ => pow_nonneg hp _)

theorem boundaryMassAt_zero (E : I → Finset V) (s : ℕ) (p : ℝ) :
    boundaryMassAt E s p 0 = 0 := by
  apply Finset.sum_eq_zero
  intro A hA
  obtain ⟨hA, hcard⟩ := Finset.mem_filter.mp hA
  have hpos := Finset.card_pos.mpr ((mem_connectedObstructions E s A).mp hA).2.1
  omega

theorem sum_boundaryMassAt (E : I → Finset V) (s : ℕ) (p : ℝ) :
    (∑ t ∈ Finset.range (s + 1), boundaryMassAt E s p t) =
      ∑ A ∈ connectedObstructions E s, p ^ (boundary E A).card := by
  apply Finset.sum_fiberwise_of_maps_to
  intro A hA
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le ((mem_connectedObstructions E s A).mp hA).1)

theorem boundaryMassAt_le (E : I → Finset V) (s q t d : ℕ)
    (hq : ∀ i, (neighbors (intersectionGraph E) i).card ≤ q)
    {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hd : ∀ A ∈ connectedObstructions E s, A.card = t → d ≤ (boundary E A).card) :
    boundaryMassAt E s p t ≤ (Fintype.card I : ℝ) * ((q : ℝ) ^ 2) ^ (t - 1) * p ^ d := by
  have hcount : (((connectedObstructions E s).filter (fun A => A.card = t)).card : ℝ) ≤
      (Fintype.card I : ℝ) * ((q : ℝ) ^ 2) ^ (t - 1) := by
    exact_mod_cast connectedObstructions_card_le E s t q hq
  calc
    _ ≤ ∑ _A ∈ (connectedObstructions E s).filter (fun A => A.card = t), p ^ d := by
      apply Finset.sum_le_sum
      intro A hA
      obtain ⟨hA, hc⟩ := Finset.mem_filter.mp hA
      exact pow_le_pow_of_le_one hp hp1 (hd A hA hc)
    _ = _ := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcount (pow_nonneg hp d)

/-- The complete connected-obstruction estimate, with no count or boundary-size
assumption beyond the actual graph, linear triples, and expansion. -/
theorem boundary_probability_sum_le {E : I → Finset V} {s : ℕ}
    (hexp : HalfBoundaryExpander E s) (hwidth : ∀ i, (E i).card = 3)
    (hlinear : LinearSupports E) (q : ℕ) (hq1 : 1 ≤ q)
    (hq : ∀ i, (neighbors (intersectionGraph E) i).card ≤ q)
    {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : ((q : ℝ) ^ 2) ^ 2 * p ≤ 1 / 2) :
    (∑ A ∈ connectedObstructions E s, p ^ (boundary E A).card) ≤
      7 * Fintype.card I * ((q : ℝ) ^ 2) ^ 4 * p ^ 3 := by
  let C : ℝ := (q : ℝ) ^ 2
  have hC : 1 ≤ C := by
    have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    dsimp [C]
    nlinarith
  have hC0 : 0 ≤ C := by linarith
  rw [← sum_boundaryMassAt]
  apply finite_envelope_bound (boundaryMassAt E s p) (Fintype.card I) C p
    (Nat.cast_nonneg _) hC hp hr (boundaryMassAt_nonneg E s hp) (boundaryMassAt_zero E s p)
  · intro t ht ht5
    have h := boundaryMassAt_le E s q t 3 hq hp hp1 (fun A hA _ =>
      three_le_boundary hexp hwidth hlinear A ((mem_connectedObstructions E s A).mp hA).2.1
        ((mem_connectedObstructions E s A).mp hA).1)
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hp 3)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hC (by omega : t - 1 ≤ 4)) (Nat.cast_nonneg _)
  · intro j
    have h := boundaryMassAt_le E s q (2 * j + 6) (j + 4) hq hp hp1 (fun A hA hc => by
      have hb := half_card_add_one_le_boundary hexp A
        ((mem_connectedObstructions E s A).mp hA).2.1 ((mem_connectedObstructions E s A).mp hA).1
      omega)
    apply h.trans
    change (Fintype.card I : ℝ) * C ^ (2 * j + 6 - 1) * p ^ (j + 4) ≤ _
    rw [show 2 * j + 6 - 1 = 2 * j + 5 by omega, pow_add C, pow_mul, pow_add p, mul_pow]
    have hc : C ^ 5 ≤ C ^ 6 := pow_le_pow_right₀ hC (by omega)
    have hmul := mul_le_mul_of_nonneg_left hc
      (show 0 ≤ (Fintype.card I : ℝ) * (C ^ 2) ^ j * p ^ j * p ^ 4 by positivity)
    nlinarith [hmul]
  · intro j
    have h := boundaryMassAt_le E s q (2 * j + 7) (j + 4) hq hp hp1 (fun A hA hc => by
      have hb := half_card_add_one_le_boundary hexp A
        ((mem_connectedObstructions E s A).mp hA).2.1 ((mem_connectedObstructions E s A).mp hA).1
      omega)
    convert h using 1
    change (Fintype.card I : ℝ) * C ^ 6 * p ^ 4 * (C ^ 2 * p) ^ j =
      (Fintype.card I : ℝ) * C ^ (2 * j + 7 - 1) * p ^ (j + 4)
    rw [show 2 * j + 7 - 1 = 2 * j + 6 by omega, pow_add C, pow_mul, pow_add p, mul_pow]
    ring

end

end BoundaryLab.BoundaryProbabilitySum
