import ProofLab.LinearClauseBoundary

/-! Incidence counting converts strict 7/4-neighborhood expansion to the
strict half-boundary expansion used by the ordinary-PC lower bound. -/

namespace BoundaryLab.NeighborhoodBoundary

noncomputable section
open scoped BigOperators
open ExpanderSupport LinearClauseBoundary

variable {I V : Type} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]

def localDegree (E : I → Finset V) (A : Finset I) (v : V) : ℕ :=
  (A.filter (fun i => v ∈ E i)).card

theorem boundary_iff_degree_one (E : I → Finset V) (A : Finset I) (v : V) :
    v ∈ boundary E A ↔ localDegree E A v = 1 := by
  rw [mem_boundary, localDegree, Finset.card_eq_one]
  constructor
  · rintro ⟨i, hi, hvi, hu⟩
    refine ⟨i, ?_⟩
    ext j
    simp only [Finset.mem_filter, Finset.mem_singleton]
    exact ⟨fun h => hu j h.1 h.2, fun h => by subst j; exact ⟨hi, hvi⟩⟩
  · rintro ⟨i, hi⟩
    have hmem : i ∈ A.filter (fun j => v ∈ E j) := by rw [hi]; simp
    obtain ⟨hiA, hvi⟩ := Finset.mem_filter.mp hmem
    refine ⟨i, hiA, hvi, ?_⟩
    intro j hj hvj
    have h : j ∈ A.filter (fun j => v ∈ E j) := Finset.mem_filter.mpr ⟨hj, hvj⟩
    simpa only [hi, Finset.mem_singleton] using h

omit [Fintype I] [DecidableEq I] [Fintype V] in
theorem sum_localDegree (E : I → Finset V) (A : Finset I) :
    (∑ v ∈ A.biUnion E, localDegree E A v) = ∑ i ∈ A, (E i).card := by
  have hcount (v : V) : localDegree E A v = ∑ i ∈ A, if v ∈ E i then 1 else 0 := by
    simp [localDegree]
  simp_rw [hcount]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have heq : (A.biUnion E).filter (fun v => v ∈ E i) = E i := by
    ext v
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun hv => ⟨Finset.mem_biUnion.mpr ⟨i, hi, hv⟩, hv⟩⟩
  simp only [Finset.sum_boole, heq, Nat.cast_id]

theorem neighborhood_incidence (E : I → Finset V) (A : Finset I) :
    2 * (A.biUnion E).card ≤ (∑ i ∈ A, (E i).card) + (boundary E A).card := by
  have hbsub : boundary E A ⊆ A.biUnion E := by
    intro v hv
    obtain ⟨i, hi, hvi, _⟩ := (mem_boundary E A v).mp hv
    exact Finset.mem_biUnion.mpr ⟨i, hi, hvi⟩
  have hsum := Finset.sum_le_sum (s := A.biUnion E) (f := fun _ => 2)
    (g := fun v => localDegree E A v + if v ∈ boundary E A then 1 else 0) (by
      intro v hv
      obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp hv
      have hpos : 0 < localDegree E A v :=
        Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hvi⟩⟩
      by_cases hb : v ∈ boundary E A
      · rw [(boundary_iff_degree_one E A v).mp hb, ite_eq_left hb]
      · rw [ite_eq_right hb]
        have hne := mt (boundary_iff_degree_one E A v).mpr hb
        omega)
  have heq : (A.biUnion E).filter (fun v => v ∈ boundary E A) = boundary E A := by
    ext v
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun hv => ⟨hbsub hv, hv⟩⟩
  simpa only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
    sum_localDegree, Finset.sum_boole, heq, Nat.mul_comm, Nat.cast_id] using hsum

theorem halfBoundary_of_neighborhood (E : I → Finset V) (s : ℕ)
    (hwidth : ∀ i, (E i).card = 3) (hlinear : LinearSupports E)
    (hN : ∀ A : Finset I, 3 ≤ A.card → A.card ≤ s →
      7 * A.card < 4 * (A.biUnion E).card) : HalfBoundaryExpander E s := by
  intro A hA hAs
  by_cases hlarge : 3 ≤ A.card
  · have hn := hN A hlarge hAs
    have hi := neighborhood_incidence E A
    simp only [hwidth, Finset.sum_const, smul_eq_mul] at hi
    omega
  · have hpos := Finset.card_pos.mpr hA
    have hi := three_uniform_incidence E hwidth hlinear A
    have hcase : A.card = 1 ∨ A.card = 2 := by omega
    rcases hcase with h | h <;> rw [h] at hi ⊢ <;> omega

end

end BoundaryLab.NeighborhoodBoundary
