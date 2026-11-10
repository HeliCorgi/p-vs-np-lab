import ProofLab.ExpanderObstructions

/-!
# Small boundaries in a proper linear 3-uniform clause family

The minimum boundary size three is derived from actual incidences. For each
clause, nonprivate variables are charged to its intersections with other
clauses; linearity bounds every charge by one. Private variables are counted
exactly once. Larger clause sets are handled by strict half-boundary expansion.
-/

namespace BoundaryLab.LinearClauseBoundary

noncomputable section

open ExpanderSupport
open scoped BigOperators

variable {I V : Type} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]

def LinearSupports (E : I → Finset V) : Prop := ∀ i j, i ≠ j → (E i ∩ E j).card ≤ 1

theorem sum_private_card (E : I → Finset V) (A : Finset I) :
    (∑ i ∈ A, (E i ∩ boundary E A).card) = (boundary E A).card := by
  have hdisj : (A : Set I).PairwiseDisjoint (fun i => E i ∩ boundary E A) := by
    intro i hi j hj hne
    apply Finset.disjoint_left.mpr
    intro v hvi hvj
    obtain ⟨k, _, _, huniq⟩ := (mem_boundary E A v).mp (Finset.mem_inter.mp hvi).2
    exact hne ((huniq i hi (Finset.mem_inter.mp hvi).1).trans
      (huniq j hj (Finset.mem_inter.mp hvj).1).symm)
  have heq : A.biUnion (fun i => E i ∩ boundary E A) = boundary E A := by
    ext v
    constructor
    · intro hv
      obtain ⟨i, _, hvi⟩ := Finset.mem_biUnion.mp hv
      exact (Finset.mem_inter.mp hvi).2
    · intro hv
      obtain ⟨i, hi, hvi, _⟩ := (mem_boundary E A v).mp hv
      exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_inter.mpr ⟨hvi, hv⟩⟩
  rw [← Finset.card_biUnion hdisj, heq]

theorem nonprivate_card_le (E : I → Finset V) (hlinear : LinearSupports E)
    (A : Finset I) (i : I) (hi : i ∈ A) : (E i \ boundary E A).card ≤ A.card - 1 := by
  classical
  have hsub : E i \ boundary E A ⊆ (A.erase i).biUnion (fun j => E i ∩ E j) := by
    intro v hv
    obtain ⟨hvi, hvb⟩ := Finset.mem_sdiff.mp hv
    have hex : ∃ j ∈ A, j ≠ i ∧ v ∈ E j := by
      by_contra hn
      push Not at hn
      apply hvb
      apply (mem_boundary E A v).mpr
      refine ⟨i, hi, hvi, ?_⟩
      intro j hj hvj
      by_contra hji
      exact hn j hj hji hvj
    obtain ⟨j, hj, hji, hvj⟩ := hex
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_erase.mpr ⟨hji, hj⟩,
      Finset.mem_inter.mpr ⟨hvi, hvj⟩⟩
  calc
    _ ≤ ((A.erase i).biUnion (fun j => E i ∩ E j)).card := Finset.card_le_card hsub
    _ ≤ ∑ j ∈ A.erase i, (E i ∩ E j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ A.erase i, 1 := Finset.sum_le_sum (fun j hj =>
      hlinear i j (Finset.ne_of_mem_erase hj).symm)
    _ = A.card - 1 := by simp [Finset.card_erase_of_mem hi]

theorem incidence_le_boundary_add_pairs (E : I → Finset V) (hlinear : LinearSupports E)
    (A : Finset I) : (∑ i ∈ A, (E i).card) ≤ (boundary E A).card + A.card * (A.card - 1) := by
  calc
    _ ≤ ∑ i ∈ A, ((E i ∩ boundary E A).card + (A.card - 1)) := by
      apply Finset.sum_le_sum
      intro i hi
      have heq := Finset.card_sdiff_add_card_inter (E i) (boundary E A)
      have hb := nonprivate_card_le E hlinear A i hi
      omega
    _ = _ := by rw [Finset.sum_add_distrib, sum_private_card]; simp

theorem three_uniform_incidence (E : I → Finset V) (hwidth : ∀ i, (E i).card = 3)
    (hlinear : LinearSupports E) (A : Finset I) :
    3 * A.card ≤ (boundary E A).card + A.card * (A.card - 1) := by
  simpa only [hwidth, Finset.sum_const, smul_eq_mul, mul_comm 3] using
    incidence_le_boundary_add_pairs E hlinear A

theorem boundary_two_clause_le (E : I → Finset V) (hwidth : ∀ i, (E i).card = 3)
    (hlinear : LinearSupports E) (A : Finset I) (hA : A.card = 2) :
    4 ≤ (boundary E A).card := by
  have h := three_uniform_incidence E hwidth hlinear A
  rw [hA] at h
  omega

theorem three_le_boundary {E : I → Finset V} {s : ℕ}
    (hexp : HalfBoundaryExpander E s) (hwidth : ∀ i, (E i).card = 3)
    (hlinear : LinearSupports E) (A : Finset I) (hA : A.Nonempty) (hs : A.card ≤ s) :
    3 ≤ (boundary E A).card := by
  have hpos := Finset.card_pos.mpr hA
  by_cases hsmall : A.card ≤ 3
  · have h := three_uniform_incidence E hwidth hlinear A
    have ht : A.card = 1 ∨ A.card = 2 ∨ A.card = 3 := by omega
    rcases ht with ht | ht | ht <;> rw [ht] at h <;> omega
  · have h := hexp A hA hs
    omega

theorem half_card_add_one_le_boundary {E : I → Finset V} {s : ℕ}
    (hexp : HalfBoundaryExpander E s) (A : Finset I) (hA : A.Nonempty) (hs : A.card ≤ s) :
    A.card / 2 + 1 ≤ (boundary E A).card := by
  have h := hexp A hA hs
  omega

end

end BoundaryLab.LinearClauseBoundary
