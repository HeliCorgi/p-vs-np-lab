import ProofLab.ExpanderMonomials
import ProofLab.ConnectedSetCounting
import ProofLab.BernoulliBounds

/-!
# Actual connected boundary obstructions

Empty pooled support is equivalent to avoiding the boundaries of connected
small clause sets. A disconnected obstruction is replaced by a proper smaller
one, using the absence of shared variables across the cut. The connected-set
count is then obtained from actual walks in the clause-intersection graph.
-/

namespace BoundaryLab.ExpanderObstructions

noncomputable section

open ExpanderSupport ExpanderMonomials ConnectedSetCounting FiniteBernoulli BernoulliBounds
open scoped BigOperators

variable {I V : Type} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]

def intersectionGraph (E : I → Finset V) : SimpleGraph I where
  Adj i j := i ≠ j ∧ (E i ∩ E j).Nonempty
  symm := ⟨by
    intro i j h
    exact ⟨h.1.symm, by simpa [Finset.inter_comm] using h.2⟩⟩
  loopless := ⟨by intro i h; exact h.1 rfl⟩

theorem boundary_subset_of_no_crossing (E : I → Finset V) (A D : Finset I)
    (hDA : D ⊆ A)
    (hcut : ∀ i ∈ D, ∀ j ∈ A, j ∉ D → ¬ (intersectionGraph E).Adj i j) :
    boundary E D ⊆ boundary E A := by
  intro v hv
  obtain ⟨i, hi, hvi, huniq⟩ := (mem_boundary E D v).mp hv
  apply (mem_boundary E A v).mpr
  refine ⟨i, hDA hi, hvi, ?_⟩
  intro j hj hvj
  by_cases hjD : j ∈ D
  · exact huniq j hjD hvj
  · exact False.elim (hcut i hi j hj hjD
      ⟨by intro heq; subst j; exact hjD hi, ⟨v, Finset.mem_inter.mpr ⟨hvi, hvj⟩⟩⟩)

theorem exists_connected_obstruction (E : I → Finset V) (T : Finset V)
    (A : Finset I) : A.Nonempty → boundary E A ⊆ T →
      ∃ D ⊆ A, CutConnected (intersectionGraph E) D ∧ boundary E D ⊆ T := by
  classical
  induction A using Finset.strongInductionOn with
  | _ A ih =>
    intro hA hb
    by_cases hconn : CutConnected (intersectionGraph E) A
    · exact ⟨A, Finset.Subset.refl A, hconn, hb⟩
    have hcut : ¬ ∀ D ⊆ A, D.Nonempty → D ≠ A →
        ∃ i ∈ D, ∃ j ∈ A, j ∉ D ∧ (intersectionGraph E).Adj i j :=
      fun h => hconn ⟨hA, h⟩
    push Not at hcut
    obtain ⟨D, hDA, hD, hne, hno⟩ := hcut
    have hbD := (boundary_subset_of_no_crossing E A D hDA hno).trans hb
    obtain ⟨C, hCD, hC, hbC⟩ := ih D (Finset.ssubset_iff_subset_ne.mpr ⟨hDA, hne⟩) hD hbD
    exact ⟨C, hCD.trans hDA, hC, hbC⟩

def connectedObstructions (E : I → Finset V) (s : ℕ) : Finset (Finset I) := by
  classical
  exact Finset.univ.filter (fun A => A.card ≤ s ∧ CutConnected (intersectionGraph E) A)

omit [DecidableEq I] [Fintype V] in
@[simp]
theorem mem_connectedObstructions (E : I → Finset V) (s : ℕ) (A : Finset I) :
    A ∈ connectedObstructions E s ↔ A.card ≤ s ∧ CutConnected (intersectionGraph E) A := by
  classical
  simp [connectedObstructions]

def goodFamily (E : I → Finset V) (s : ℕ) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter (fun T => support E s T = ∅)

@[simp]
theorem mem_goodFamily (E : I → Finset V) (s : ℕ) (T : Finset V) :
    T ∈ goodFamily E s ↔ support E s T = ∅ := by
  classical
  simp [goodFamily]

theorem goodFamily_eq_avoidAll (E : I → Finset V) (s : ℕ) :
    goodFamily E s = avoidAll (connectedObstructions E s) (boundary E) := by
  classical
  ext T
  simp only [mem_goodFamily, mem_avoidAll, support_eq_empty_iff, mem_connectedObstructions]
  constructor
  · intro h A hA
    exact h A hA.2.1 hA.1
  · intro h A hA hs hb
    obtain ⟨D, hDA, hconn, hbD⟩ := exists_connected_obstruction E T A hA hb
    exact h D ⟨(Finset.card_le_card hDA).trans hs, hconn⟩ hbD

theorem goodSupports_eq_layer (E : I → Finset V) (s k : ℕ) :
    goodSupports E s k = layer (goodFamily E s) k := by
  classical
  ext T
  simp [layer, and_comm]

def occurrences (E : I → Finset V) (v : V) : Finset I := Finset.univ.filter (fun i => v ∈ E i)

omit [Fintype V] in
theorem intersection_neighbors_card_le (E : I → Finset V) (w Δ : ℕ)
    (hwidth : ∀ i, (E i).card ≤ w) (hocc : ∀ v, (occurrences E v).card ≤ Δ) (i : I) :
    (neighbors (intersectionGraph E) i).card ≤ w * Δ := by
  classical
  have hsub : neighbors (intersectionGraph E) i ⊆ (E i).biUnion (occurrences E) := by
    intro j hj
    obtain ⟨_, v, hv⟩ := (mem_neighbors _ _ _).mp hj
    exact Finset.mem_biUnion.mpr ⟨v, (Finset.mem_inter.mp hv).1,
      Finset.mem_filter.mpr ⟨Finset.mem_univ j, (Finset.mem_inter.mp hv).2⟩⟩
  calc
    _ ≤ ((E i).biUnion (occurrences E)).card := Finset.card_le_card hsub
    _ ≤ ∑ v ∈ E i, (occurrences E v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ E i, Δ := Finset.sum_le_sum (fun v _ => hocc v)
    _ = (E i).card * Δ := by simp
    _ ≤ w * Δ := Nat.mul_le_mul_right Δ (hwidth i)

omit [Fintype V] in
theorem connectedObstructions_card_le (E : I → Finset V) (s t q : ℕ)
    (hq : ∀ i, (neighbors (intersectionGraph E) i).card ≤ q) :
    ((connectedObstructions E s).filter (fun A => A.card = t)).card ≤
      Fintype.card I * (q ^ 2) ^ (t - 1) := by
  classical
  have hsub : (connectedObstructions E s).filter (fun A => A.card = t) ⊆
      connectedSets (intersectionGraph E) t := by
    intro A hA
    obtain ⟨hA, hc⟩ := Finset.mem_filter.mp hA
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ A, hc, ((mem_connectedObstructions E s A).mp hA).2⟩
  exact (Finset.card_le_card hsub).trans (by
    simpa only [pow_mul] using connectedSets_card_le (intersectionGraph E) q hq t)

theorem product_le_mass_goodFamily (E : I → Finset V) (s : ℕ)
    {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (∏ A ∈ connectedObstructions E s, (1 - p ^ (boundary E A).card)) ≤ mass p (goodFamily E s) := by
  rw [goodFamily_eq_avoidAll]
  exact product_le_mass_avoidAll hp hp1 _ _

theorem exp_le_mass_goodFamily (E : I → Finset V) (s : ℕ)
    {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hhalf : ∀ A ∈ connectedObstructions E s, p ^ (boundary E A).card ≤ 1 / 2) :
    Real.exp (-2 * ∑ A ∈ connectedObstructions E s, p ^ (boundary E A).card) ≤
      mass p (goodFamily E s) := by
  rw [goodFamily_eq_avoidAll]
  exact exp_le_mass_avoidAll hp hp1 _ _ hhalf

end

end BoundaryLab.ExpanderObstructions
