import Std

/-!
# Boundary relations with independent interiors

The interior variables have separate types `X` and `Y`.  The joint predicate
contains exactly the two local predicates and a possible boundary-only
constraint.  An actual graph decomposition must justify this factorization;
unmodeled interior cross-edges do not satisfy its premises.
-/

set_option autoImplicit false

namespace BoundaryLab.Composition

def BoundaryRelation {B X : Type} (P : B → X → Prop) (b : B) : Prop :=
  ∃ x : X, P b x

theorem independent_interiors_compose
    {B X Y : Type} (P : B → X → Prop) (Q : B → Y → Prop) (b : B) :
    (∃ x : X, ∃ y : Y, P b x ∧ Q b y) ↔
      BoundaryRelation P b ∧ BoundaryRelation Q b := by
  constructor
  · intro h
    obtain ⟨x, y, hp, hq⟩ := h
    exact ⟨⟨x, hp⟩, ⟨y, hq⟩⟩
  · intro h
    obtain ⟨⟨x, hp⟩, ⟨y, hq⟩⟩ := h
    exact ⟨x, y, hp, hq⟩

theorem independent_interiors_with_boundary_constraint
    {B X Y : Type} (P : B → X → Prop) (Q : B → Y → Prop)
    (R : B → Prop) (b : B) :
    (∃ x : X, ∃ y : Y, P b x ∧ Q b y ∧ R b) ↔
      BoundaryRelation P b ∧ BoundaryRelation Q b ∧ R b := by
  constructor
  · intro h
    obtain ⟨x, y, hp, hq, hr⟩ := h
    exact ⟨⟨x, hp⟩, ⟨y, hq⟩, hr⟩
  · intro h
    obtain ⟨⟨x, hp⟩, ⟨y, hq⟩, hr⟩ := h
    exact ⟨x, y, hp, hq, hr⟩

#print axioms independent_interiors_compose
#print axioms independent_interiors_with_boundary_constraint

end BoundaryLab.Composition
