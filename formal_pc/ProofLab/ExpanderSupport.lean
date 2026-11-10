import Mathlib.Data.Finset.Powerset
import Lean.Elab.Tactic.Omega

/-!
# Pooled supports in a finite boundary expander

These are the actual finite clause-variable supports used in the separated-space
argument. Strict half-boundary expansion is `|A| < 2 |boundary A|`.
The pooled support, its boundary, its size bound, and the support-absorption
step are proved. No polynomial reduction operator or PC separation is assumed
or established here. In particular this is not the full expander lower bound.
-/

namespace BoundaryLab.ExpanderSupport

noncomputable section

variable {I V : Type*} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]

/-- Variables occurring in exactly one selected clause. -/
def boundary (E : I → Finset V) (A : Finset I) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => ∃ i ∈ A, v ∈ E i ∧
    ∀ j ∈ A, v ∈ E j → j = i)

@[simp]
theorem mem_boundary (E : I → Finset V) (A : Finset I) (v : V) :
    v ∈ boundary E A ↔ ∃ i ∈ A, v ∈ E i ∧ ∀ j ∈ A, v ∈ E j → j = i := by
  classical
  simp [boundary]

@[simp]
theorem boundary_empty (E : I → Finset V) : boundary E ∅ = ∅ := by
  ext v
  simp

theorem boundary_union_subset (E : I → Finset V) (A D : Finset I) :
    boundary E (A ∪ D) ⊆ boundary E A ∪ boundary E D := by
  intro v hv
  obtain ⟨i, hi, hvi, hu⟩ := (mem_boundary E _ v).mp hv
  rcases Finset.mem_union.mp hi with hi | hi
  · exact Finset.mem_union_left _ ((mem_boundary E A v).mpr
      ⟨i, hi, hvi, fun j hj hvj => hu j (Finset.mem_union_left _ hj) hvj⟩)
  · exact Finset.mem_union_right _ ((mem_boundary E D v).mpr
      ⟨i, hi, hvi, fun j hj hvj => hu j (Finset.mem_union_right _ hj) hvj⟩)

/-- Boundary variables already touching `A` must be private to `A` itself. -/
theorem boundary_union_subset_sdiff (E : I → Finset V) (A D : Finset I) :
    boundary E (A ∪ D) ⊆ boundary E A ∪ (boundary E D \ A.biUnion E) := by
  intro v hv
  obtain ⟨i, hi, hvi, hu⟩ := (mem_boundary E _ v).mp hv
  by_cases hN : v ∈ A.biUnion E
  · obtain ⟨j, hj, hvj⟩ := Finset.mem_biUnion.mp hN
    have hji := hu j (Finset.mem_union_left _ hj) hvj
    subst j
    exact Finset.mem_union_left _ ((mem_boundary E A v).mpr
      ⟨i, hj, hvi, fun j hj hvj => hu j (Finset.mem_union_left _ hj) hvj⟩)
  · have hiD : i ∈ D := by
      rcases Finset.mem_union.mp hi with hiA | hiD
      · exact False.elim (hN (Finset.mem_biUnion.mpr ⟨i, hiA, hvi⟩))
      · exact hiD
    exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
      ⟨(mem_boundary E D v).mpr
        ⟨i, hiD, hvi, fun j hj hvj => hu j (Finset.mem_union_right _ hj) hvj⟩, hN⟩)

theorem boundary_biUnion_subset (E : I → Finset V) (H : Finset (Finset I)) :
    boundary E (H.biUnion id) ⊆ H.biUnion (boundary E) := by
  induction H using Finset.induction_on with
  | empty => simp
  | @insert A H hA ih =>
    simp only [Finset.biUnion_insert, id_eq]
    exact (boundary_union_subset E A _).trans (Finset.union_subset_union (by rfl) ih)

/-- The strict half-expansion condition, without a hidden real-number division. -/
def HalfBoundaryExpander (E : I → Finset V) (s : ℕ) : Prop :=
  ∀ A : Finset I, A.Nonempty → A.card ≤ s → A.card < 2 * (boundary E A).card

/-- All small clause sets whose boundary is contained in the variable set. -/
def supportedSets (E : I → Finset V) (s : ℕ) (T : Finset V) :
    Finset (Finset I) := by
  classical
  exact Finset.univ.powerset.filter (fun A => A.card ≤ s ∧ boundary E A ⊆ T)

@[simp]
theorem mem_supportedSets (E : I → Finset V) (s : ℕ) (T : Finset V) (A : Finset I) :
    A ∈ supportedSets E s T ↔ A.card ≤ s ∧ boundary E A ⊆ T := by
  classical
  simp [supportedSets]

/-- The union of all eligible clause sets, not a chosen single witness. -/
def support (E : I → Finset V) (s : ℕ) (T : Finset V) : Finset I :=
  (supportedSets E s T).biUnion id

theorem subset_support (E : I → Finset V) {s : ℕ} {T : Finset V} {A : Finset I}
    (hs : A.card ≤ s) (hb : boundary E A ⊆ T) : A ⊆ support E s T := by
  intro i hi
  exact Finset.mem_biUnion.mpr ⟨A, (mem_supportedSets E s T A).mpr ⟨hs, hb⟩, hi⟩

theorem boundary_support_subset (E : I → Finset V) (s : ℕ) (T : Finset V) :
    boundary E (support E s T) ⊆ T := by
  apply (boundary_biUnion_subset E _).trans
  intro v hv
  obtain ⟨A, hA, hv⟩ := Finset.mem_biUnion.mp hv
  exact ((mem_supportedSets E s T A).mp hA).2 hv

theorem support_mono (E : I → Finset V) (s : ℕ) {T T' : Finset V} (h : T ⊆ T') :
    support E s T ⊆ support E s T' := by
  intro i hi
  obtain ⟨A, hA, hi⟩ := Finset.mem_biUnion.mp hi
  have hAs := (mem_supportedSets E s T A).mp hA
  exact subset_support E hAs.1 (hAs.2.trans h) hi

theorem card_le_of_supported {E : I → Finset V} {s B : ℕ}
    (hexp : HalfBoundaryExpander E s) {T : Finset V} (hT : T.card ≤ B)
    {A : Finset I} (hs : A.card ≤ s) (hb : boundary E A ⊆ T) : A.card ≤ 2 * B := by
  rcases A.eq_empty_or_nonempty with hA | hA
  · simp [hA]
  · have hbd := (Finset.card_le_card hb).trans hT
    have ha := hexp A hA hs
    omega

/-- The union of many eligible sets stays small. Merely bounding each member
would not be sufficient; expansion is applied again at every union step. -/
theorem card_biUnion_le_of_supported {E : I → Finset V} {s B : ℕ}
    (hexp : HalfBoundaryExpander E s) (hroom : 4 * B ≤ s)
    {T : Finset V} (hT : T.card ≤ B) (H : Finset (Finset I)) :
    (∀ A ∈ H, A.card ≤ s ∧ boundary E A ⊆ T) → (H.biUnion id).card ≤ 2 * B := by
  induction H using Finset.induction_on with
  | empty => simp
  | @insert A H hA ih =>
    intro hH
    have ha := hH A (Finset.mem_insert_self _ _)
    have hrest := fun D hD => hH D (Finset.mem_insert_of_mem hD)
    have hsmallA := card_le_of_supported hexp hT ha.1 ha.2
    have hsmallH := ih hrest
    have hboundaryH : boundary E (H.biUnion id) ⊆ T := by
      apply (boundary_biUnion_subset E H).trans
      intro v hv
      obtain ⟨D, hD, hv⟩ := Finset.mem_biUnion.mp hv
      exact (hrest D hD).2 hv
    rw [Finset.biUnion_insert]
    apply card_le_of_supported hexp hT
    · have hcard := Finset.card_union_le A (H.biUnion id)
      change (A ∪ H.biUnion id).card ≤ s
      omega
    · exact (boundary_union_subset E A _).trans (Finset.union_subset ha.2 hboundaryH)

theorem support_card_le {E : I → Finset V} {s B : ℕ}
    (hexp : HalfBoundaryExpander E s) (hroom : 4 * B ≤ s)
    {T : Finset V} (hT : T.card ≤ B) : (support E s T).card ≤ 2 * B :=
  card_biUnion_le_of_supported hexp hroom hT _
    (fun A hA => (mem_supportedSets E s T A).mp hA)

theorem support_mem_supportedSets {E : I → Finset V} {s B : ℕ}
    (hexp : HalfBoundaryExpander E s) (hroom : 4 * B ≤ s)
    {T : Finset V} (hT : T.card ≤ B) : support E s T ∈ supportedSets E s T := by
  apply (mem_supportedSets E s T _).mpr
  refine ⟨?_, boundary_support_subset E s T⟩
  have := support_card_le hexp hroom hT
  omega

/-- The combinatorial absorption step needed when a normal-form term only
introduces variables in the old support neighborhood. It also handles repeated
variables in the later PC application, without assuming a polynomial operator. -/
theorem support_absorbs {E : I → Finset V} {s B : ℕ}
    (hexp : HalfBoundaryExpander E s) (hroom : 4 * B ≤ s)
    {T T' : Finset V} (hT : T.card ≤ B) (hT' : T'.card ≤ B)
    (hN : T' ⊆ (support E s T).biUnion E ∪ T) :
    support E s T' ⊆ support E s T := by
  have hsizeA := support_card_le hexp hroom hT
  have hsizeD := support_card_le hexp hroom hT'
  have hsmall : (support E s T ∪ support E s T').card ≤ s := by
    have := Finset.card_union_le (support E s T) (support E s T')
    omega
  have hb : boundary E (support E s T ∪ support E s T') ⊆ T := by
    apply (boundary_union_subset_sdiff E _ _).trans
    apply Finset.union_subset (boundary_support_subset E s T)
    intro v hv
    obtain ⟨hbd, hnot⟩ := Finset.mem_sdiff.mp hv
    have hT'v := boundary_support_subset E s T' hbd
    exact (Finset.mem_union.mp (hN hT'v)).resolve_left hnot
  exact Finset.subset_union_right.trans (subset_support E hsmall hb)

theorem support_eq_empty_iff (E : I → Finset V) (s : ℕ) (T : Finset V) :
    support E s T = ∅ ↔
      ∀ A : Finset I, A.Nonempty → A.card ≤ s → ¬ boundary E A ⊆ T := by
  constructor
  · intro h A hA hs hb
    obtain ⟨i, hi⟩ := hA
    have := subset_support E hs hb hi
    simp [h] at this
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    obtain ⟨A, hA, hi⟩ := Finset.mem_biUnion.mp hi
    have ha := (mem_supportedSets E s T A).mp hA
    exact h A ⟨i, hi⟩ ha.1 ha.2

end

end BoundaryLab.ExpanderSupport
