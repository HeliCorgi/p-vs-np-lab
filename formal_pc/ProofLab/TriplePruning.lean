import ProofLab.RandomCNFMoments

/-! Delete high-degree and overlapping triples, preserving the sampled expansion. -/

namespace BoundaryLab.TriplePruning

noncomputable section
open scoped BigOperators
open TripleCounting RandomCNFMoments ExpanderSupport LinearClauseBoundary

variable {V : Type} [Fintype V] [DecidableEq V]

def highEdges (H : Finset (Triple V)) : Finset (Triple V) :=
  H.filter (fun e => ∃ v ∈ e.1, 4096 < degree H v)
def conflictEdges (H : Finset (Triple V)) : Finset (Triple V) := (sampledPairs H).image Prod.fst
def pruned (H : Finset (Triple V)) : Finset (Triple V) := H \ (highEdges H ∪ conflictEdges H)

theorem highEdges_card_bound (H : Finset (Triple V)) :
    4096 * (highEdges H).card ≤ degreeSquares H := by
  let B := (Finset.univ : Finset V).filter (fun v => 4096 < degree H v)
  have hsub : highEdges H ⊆ B.biUnion (fun v => incident v ∩ H) := by
    intro e he
    obtain ⟨heH, v, hv, hd⟩ := Finset.mem_filter.mp he
    exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩,
      Finset.mem_inter.mpr ⟨by simpa [incident, extending] using hv, heH⟩⟩
  have hc : (highEdges H).card ≤ ∑ v ∈ B, degree H v :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  calc
    4096 * (highEdges H).card ≤ 4096 * ∑ v ∈ B, degree H v := Nat.mul_le_mul_left _ hc
    _ = ∑ v ∈ B, 4096 * degree H v := Finset.mul_sum ..
    _ ≤ ∑ v ∈ B, degree H v ^ 2 := by
      apply Finset.sum_le_sum
      intro v hv
      have h := (Finset.mem_filter.mp hv).2
      nlinarith
    _ ≤ degreeSquares H := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

theorem pruned_card_lower (H : Finset (Triple V))
    (hcount : 15 * Fintype.card V ≤ H.card)
    (hsq : degreeSquares H ≤ 8192 * Fintype.card V)
    (hpairs : (sampledPairs H).card ≤ Fintype.card V) :
    12 * Fintype.card V ≤ (pruned H).card := by
  have hh := highEdges_card_bound H
  have hhigh : (highEdges H).card ≤ 2 * Fintype.card V := by omega
  have hconf : (conflictEdges H).card ≤ Fintype.card V := Finset.card_image_le.trans hpairs
  have hdel := Finset.card_union_le (highEdges H) (conflictEdges H)
  have hremain := Finset.card_le_card_sdiff_add_card (s := H) (t := highEdges H ∪ conflictEdges H)
  change H.card ≤ (pruned H).card + _ at hremain
  omega

theorem pruned_subset (H : Finset (Triple V)) : pruned H ⊆ H := Finset.sdiff_subset

theorem pruned_degree (H : Finset (Triple V)) {e : Triple V} (he : e ∈ pruned H)
    {v : V} (hv : v ∈ e.1) : degree H v ≤ 4096 := by
  obtain ⟨heH, hdel⟩ := Finset.mem_sdiff.mp he
  by_contra h
  apply hdel
  exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨heH, v, hv, by omega⟩)

theorem pruned_linear (H : Finset (Triple V)) {e f : Triple V}
    (he : e ∈ pruned H) (hf : f ∈ pruned H) (hne : e ≠ f) : (e.1 ∩ f.1).card ≤ 1 := by
  obtain ⟨heH, hdel⟩ := Finset.mem_sdiff.mp he
  have hfH := pruned_subset H hf
  by_contra h
  apply hdel
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  refine ⟨(e, f), ?_, rfl⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne, (by
      change 2 ≤ (e.1 ∩ f.1).card
      omega)⟩
  · simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨heH, hfH⟩

/-- A triple support on the selected clause index type. -/
def supportOn (H : Finset (Triple V)) (e : H) : Finset V := e.1.1

omit [Fintype V] in
theorem supportOn_width (H : Finset (Triple V)) (e : H) : (supportOn H e).card = 3 := e.1.2

theorem supportOn_linear {H G : Finset (Triple V)} (hG : G ⊆ pruned H) :
    LinearSupports (supportOn G) := by
  intro e f hne
  exact pruned_linear H (hG e.2) (hG f.2) (fun h => hne (Subtype.ext h))

theorem supportOn_occurrence {H G : Finset (Triple V)} (hG : G ⊆ pruned H) (v : V) :
    (ExpanderObstructions.occurrences (supportOn G) v).card ≤ 4096 := by
  by_cases hempty : (ExpanderObstructions.occurrences (supportOn G) v) = ∅
  · rw [hempty]; simp
  obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hve : v ∈ e.1.1 := (Finset.mem_filter.mp he).2
  have hdegree := pruned_degree H (hG e.2) hve
  apply le_trans _ hdegree
  apply Finset.card_le_card_of_injOn (fun e : G => (e.1 : Triple V))
  · intro f hf
    exact Finset.mem_inter.mpr ⟨by
      simpa [incident, extending, supportOn] using (Finset.mem_filter.mp hf).2,
      pruned_subset H (hG f.2)⟩
  · intro e _ f _ heq
    exact Subtype.ext heq

end

end BoundaryLab.TriplePruning
