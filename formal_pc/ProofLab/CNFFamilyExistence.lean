import ProofLab.RandomCNFSample
import ProofLab.TriplePruning
import ProofLab.NeighborhoodBoundary
import ProofLab.CNFSigning

/-!
# Existence of the actual bounded-occurrence expanding 3-CNF family

The sampled supports, pruning, exact clause count and unsatisfiable signing
are all constructed inside the theorem. No existence or probability estimate
is received as a hypothesis.
-/

namespace BoundaryLab.CNFFamilyExistence

noncomputable section
open TripleCounting RandomCNFExpansion RandomCNFMoments RandomCNFSample TriplePruning
open ExpanderSupport ExpanderObstructions LinearClauseBoundary ExponentialBudget CNFSigning

variable {V : Type} [Fintype V] [DecidableEq V]

def Admissible (H : Finset (Triple V)) : Prop :=
  H.card = 12 * Fintype.card V ∧ LinearSupports (supportOn H) ∧
    (∀ v, (occurrences (supportOn H) v).card ≤ 4096) ∧
    HalfBoundaryExpander (supportOn H) (expansionSize (Fintype.card V))

theorem exists_admissible (hn : 1000000 ≤ Fintype.card V) :
    ∃ H : Finset (Triple V), Admissible H := by
  obtain ⟨H, hnotbad, hcount, hsq, hpairs⟩ := exists_good_sample hn
  obtain ⟨G, hG, hGc⟩ := Finset.exists_subset_card_eq (pruned_card_lower H hcount hsq hpairs)
  have hlin := supportOn_linear hG
  refine ⟨G, hGc, hlin, supportOn_occurrence hG, ?_⟩
  apply NeighborhoodBoundary.halfBoundary_of_neighborhood _ _ (supportOn_width G) hlin
  intro A hA3 hAs
  let D : Finset (Triple V) := A.image Subtype.val
  have hcard : D.card = A.card := Finset.card_image_of_injective _ Subtype.val_injective
  have hDH : D ⊆ H := by
    intro e he
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp he
    exact pruned_subset H (hG a.2)
  have heq : neighbors D = A.biUnion (supportOn G) := by
    ext v
    simp only [neighbors, D, Finset.mem_biUnion, Finset.mem_image, supportOn]
    constructor
    · rintro ⟨e, ⟨a, ha, rfl⟩, hv⟩
      exact ⟨a, ha, hv⟩
    · rintro ⟨a, ha, hv⟩
      exact ⟨a.1, ⟨a, ha, rfl⟩, hv⟩
  have hN := neighborhood_of_not_bad hnotbad D hDH (by omega) (by omega)
  simpa only [hcard, heq] using hN

/-- Every sufficiently large ambient size has both an UNSAT signing and an
all-positive SAT sibling, with exactly the same proper linear supports. -/
theorem exists_unsatisfiable_family (hn : 1000000 ≤ Fintype.card V) :
    ∃ H : Finset (Triple V), Admissible H ∧
      (∃ sign : H → V → Bool, ¬ Satisfiable (supportOn H) sign) ∧
      Satisfiable (supportOn H) (fun _ _ => true) := by
  obtain ⟨H, hH⟩ := exists_admissible hn
  refine ⟨H, hH, ?_, all_positive_satisfiable _ (fun e => Finset.card_pos.mp (by rw [supportOn_width]; omega))⟩
  apply exists_unsatisfiable_signing _ (supportOn_width H) (by omega)
  simpa only [Fintype.card_coe] using hH.1

end

end BoundaryLab.CNFFamilyExistence
