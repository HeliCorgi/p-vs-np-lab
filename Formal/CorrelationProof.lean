import Formal.WitnessTransport

/-!
# Exact Boolean relations and compatible projection

All relations are evaluated on the same original Boolean assignment.  Joining
therefore identifies overlapping coordinates before existential projection.
The checker implements finite tables; this file proves its semantic inference
rules, not the Python implementation, discovery bounds, or a P versus NP claim.
-/

set_option autoImplicit false

namespace BoundaryLab.CorrelationProof

open BoundaryLab.WitnessTransport

abbrev Relation (V : Type) := (V → Bool) → Prop

def Project {V : Type} (keep : V → Prop) (r : Relation V) : Relation V :=
  fun a => ∃ b, (∀ v, keep v → b v = a v) ∧ r b

inductive Derives {V : Type} (f : CNF V) : Relation V → Prop where
  | source (c : Clause V) (member : c ∈ f) : Derives f (fun a => Holds a c)
  | join {r s : Relation V} (left : Derives f r) (right : Derives f s) :
      Derives f (fun a => r a ∧ s a)
  | project {r : Relation V} (keep : V → Prop) (inner : Derives f r) :
      Derives f (Project keep r)
  | table {r s : Relation V} (inner : Derives f r)
      (checked : ∀ a, r a → s a) : Derives f s

/-- A derivation preserves every actual original model, including at joins
with overlapping scopes.  The same assignment witnesses each projection. -/
theorem derivation_sound {V : Type} {f : CNF V} {r : Relation V}
    (proof : Derives f r) : ∀ a, Models a f → r a := by
  induction proof with
  | source c member =>
    intro a model
    exact model c member
  | join left right ihLeft ihRight =>
    intro a model
    exact ⟨ihLeft a model, ihRight a model⟩
  | project keep inner ih =>
    intro a model
    exact ⟨a, fun _ _ => rfl, ih a model⟩
  | table inner checked ih =>
    intro a model
    exact checked a (ih a model)

theorem empty_relation_refutes {V : Type} (f : CNF V)
    (proof : Derives f (fun _ => False)) : ¬ Sat f := by
  rintro ⟨a, model⟩
  exact derivation_sound proof a model

/-- One resolution step is exactly a join followed by eliminating its pivot;
the other literal evaluations are fixed by the shared outer assignment. -/
theorem resolution_is_exact_projection (a b : Prop) :
    (∃ pivot : Bool, (pivot = true ∨ a) ∧ (pivot = false ∨ b)) ↔ (a ∨ b) := by
  constructor
  · rintro ⟨pivot, left, right⟩
    cases pivot
    · exact Or.inl (left.resolve_left (by decide))
    · exact Or.inr (right.resolve_left (by decide))
  · intro h
    cases h with
    | inl ha => exact ⟨false, Or.inr ha, Or.inl rfl⟩
    | inr hb => exact ⟨true, Or.inl rfl, Or.inr hb⟩

/-- Independent existential witnesses can lose a two-coordinate correlation:
equality and disequality each project to every x, while their join is empty. -/
theorem separate_projections_lose_correlation (x : Bool) :
    ((∃ y : Bool, x = y) ∧ (∃ y : Bool, x ≠ y)) ∧
      ¬ (∃ y : Bool, x = y ∧ x ≠ y) := by
  constructor
  · constructor
    · exact ⟨x, rfl⟩
    · exact ⟨!x, by cases x <;> decide⟩
  · rintro ⟨y, yes, no⟩
    exact no yes

end BoundaryLab.CorrelationProof
