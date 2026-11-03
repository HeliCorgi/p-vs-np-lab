import Formal.ExactlyOneParity

/-!
# No nontrivial affine equation follows from the bridge CNF alone

Coordinates are `Sum V I`: original variables are tagged `inl`, and helper i
is tagged `inr i`. The entire CNF consists of one binary clause per helper:

    evaluated original literal i OR helper i.

Each helper is therefore fresh, positive, and occurs only in its own clause.
Original variables and original literals may be shared or repeated.

Every coordinate admits two models differing only by flipping that coordinate.
Consequently any finite XOR row, in normalized duplicate-free support form,
that has one fixed RHS on every CNF model must have empty support and RHS zero.
For finite V and I this is precisely the absence of nontrivial affine-hull
equations. The statement is not restricted to the exactly-one recognizer.

The model set is explicitly nonempty, including when both coordinate types
are empty. This theorem concerns unconditional consequences of this CNF alone.
It does not restrict deductions using the existing XOR equations as additional
premises, conditioning on assignments, adding variables, or other algorithms.
It does not formalize the Python implementation or a running-time lower bound.
-/

set_option autoImplicit false

namespace BoundaryLab.BridgeAffineBarrier

open BoundaryLab.ExactlyOneParity

def flipAt {C : Type} [DecidableEq C]
    (assignment : C → Bool) (coordinate : C) : C → Bool :=
  fun c => if c = coordinate then !(assignment c) else assignment c

/-- A normalized GF(2) row has coefficient one exactly on its support. -/
def rowValue {C : Type} (support : List C) (assignment : C → Bool) : Bool :=
  parity (support.map assignment)

@[simp] theorem rowValue_nil {C : Type} (assignment : C → Bool) :
    rowValue [] assignment = false := rfl

@[simp] theorem rowValue_cons {C : Type}
    (c : C) (support : List C) (assignment : C → Bool) :
    rowValue (c :: support) assignment =
      Bool.xor (assignment c) (rowValue support assignment) := rfl

private theorem xor_not_left (a b : Bool) :
    Bool.xor (!a) b = !(Bool.xor a b) := by
  cases a <;> cases b <;> rfl

private theorem xor_not_right (a b : Bool) :
    Bool.xor a (!b) = !(Bool.xor a b) := by
  cases a <;> cases b <;> rfl

private theorem xor_not_self (b : Bool) : Bool.xor (!b) b = true := by
  cases b <;> rfl

private theorem bool_ne_not (b : Bool) : b ≠ !b := by
  cases b <;> decide

private theorem row_flip_of_not_mem
    {C : Type} [DecidableEq C] (assignment : C → Bool) (coordinate : C) :
    ∀ support : List C, coordinate ∉ support →
      rowValue support (flipAt assignment coordinate) = rowValue support assignment := by
  intro support
  induction support with
  | nil =>
      intro _
      rfl
  | cons c support ih =>
      intro hn
      have hne : c ≠ coordinate := by
        intro he
        apply hn
        simp [he]
      have ht : coordinate ∉ support := by
        intro hm
        exact hn (List.mem_cons_of_mem c hm)
      have hh : flipAt assignment coordinate c = assignment c := by
        simp [flipAt, hne]
      simp only [rowValue_cons]
      rw [hh, ih ht]

/-- Flipping a support coordinate toggles a duplicate-free XOR row. -/
theorem row_flip_of_mem
    {C : Type} [DecidableEq C] (assignment : C → Bool) (coordinate : C) :
    ∀ support : List C, support.Nodup → coordinate ∈ support →
      rowValue support (flipAt assignment coordinate) = !(rowValue support assignment) := by
  intro support
  induction support with
  | nil =>
      intro _ hm
      cases hm
  | cons c support ih =>
      intro hn hm
      have hd := List.nodup_cons.mp hn
      by_cases he : c = coordinate
      · subst c
        have hh : flipAt assignment coordinate coordinate = !(assignment coordinate) := by
          simp [flipAt]
        simp only [rowValue_cons]
        rw [hh, row_flip_of_not_mem assignment coordinate support hd.1]
        exact xor_not_left (assignment coordinate) (rowValue support assignment)
      · have ht : coordinate ∈ support := by
          have hm' : coordinate = c ∨ coordinate ∈ support := List.mem_cons.mp hm
          cases hm' with
          | inl h => exact False.elim (he h.symm)
          | inr h => exact h
        have hh : flipAt assignment coordinate c = assignment c := by
          simp [flipAt, he]
        simp only [rowValue_cons]
        rw [hh, ih hd.2 ht]
        exact xor_not_right (assignment c) (rowValue support assignment)

/-- A nonempty model set separated in every coordinate has no nonzero XOR row. -/
theorem coordinate_separation_forces_trivial_row
    {C : Type} [DecidableEq C] (models : (C → Bool) → Prop)
    (nonempty : ∃ assignment, models assignment)
    (separates : ∀ c : C, ∃ assignment,
      models assignment ∧ models (flipAt assignment c))
    (support : List C) (distinct : support.Nodup) (rhs : Bool)
    (row_holds : ∀ assignment, models assignment → rowValue support assignment = rhs) :
    support = [] ∧ rhs = false := by
  have hs : support = [] := by
    cases support with
    | nil => rfl
    | cons c support =>
        obtain ⟨assignment, ha, hf⟩ := separates c
        have ht := row_flip_of_mem assignment c (c :: support) distinct (by simp)
        have hbase := row_holds assignment ha
        have hflip := row_holds (flipAt assignment c) hf
        rw [hbase, hflip] at ht
        exact False.elim (bool_ne_not rhs ht)
  obtain ⟨assignment, ha⟩ := nonempty
  have hbase := row_holds assignment ha
  rw [hs] at hbase
  exact ⟨hs, hbase.symm⟩

/-- Exactly the binary-clause component of the 3SAT bridge, with unique helpers. -/
def BridgeModel {V I : Type} (literals : I → Literal V)
    (assignment : Sum V I → Bool) : Prop :=
  ∀ i : I,
    eval (fun v => assignment (Sum.inl v)) (literals i) = true ∨
      assignment (Sum.inr i) = true

def withHelpersTrue {V I : Type} (original : V → Bool) : Sum V I → Bool
  | Sum.inl v => original v
  | Sum.inr _ => true

theorem all_helpers_true_is_model
    {V I : Type} (literals : I → Literal V) (original : V → Bool) :
    BridgeModel literals (withHelpersTrue original) := by
  intro i
  exact Or.inr rfl

/-- Each original or helper coordinate can be flipped between two CNF models. -/
theorem bridge_coordinate_separation
    {V I : Type} [DecidableEq V] [DecidableEq I]
    (literals : I → Literal V) (coordinate : Sum V I) :
    ∃ assignment,
      BridgeModel literals assignment ∧
        BridgeModel literals (flipAt assignment coordinate) := by
  cases coordinate with
  | inl v =>
      refine ⟨withHelpersTrue (fun _ : V => false),
        all_helpers_true_is_model literals (fun _ : V => false), ?_⟩
      intro i
      right
      simp [flipAt, withHelpersTrue]
  | inr i =>
      let assignment : Sum V I → Bool :=
        withHelpersTrue (fun _ : V => !((literals i).negative))
      have ha : BridgeModel literals assignment :=
        all_helpers_true_is_model literals (fun _ : V => !((literals i).negative))
      refine ⟨assignment, ha, ?_⟩
      intro j
      by_cases hj : j = i
      · subst j
        left
        change Bool.xor
          (flipAt assignment (Sum.inr i) (Sum.inl (literals i).var))
          (literals i).negative = true
        have hh : flipAt assignment (Sum.inr i) (Sum.inl (literals i).var) =
            !((literals i).negative) := by
          simp [flipAt, assignment, withHelpersTrue]
        rw [hh]
        exact xor_not_self (literals i).negative
      · right
        simp [flipAt, assignment, withHelpersTrue, hj]

/-- Every affine equation entailed by the bridge CNF alone is the tautology 0=0. -/
theorem bridge_has_no_nontrivial_affine_equation
    {V I : Type} [DecidableEq V] [DecidableEq I]
    (literals : I → Literal V)
    (support : List (Sum V I)) (distinct : support.Nodup) (rhs : Bool)
    (entailed : ∀ assignment,
      BridgeModel literals assignment → rowValue support assignment = rhs) :
    support = [] ∧ rhs = false := by
  apply coordinate_separation_forces_trivial_row (BridgeModel literals)
    ⟨withHelpersTrue (fun _ : V => false),
      all_helpers_true_is_model literals (fun _ : V => false)⟩
    (bridge_coordinate_separation literals) support distinct rhs entailed

#print axioms row_flip_of_mem
#print axioms coordinate_separation_forces_trivial_row
#print axioms bridge_coordinate_separation
#print axioms bridge_has_no_nontrivial_affine_equation

end BoundaryLab.BridgeAffineBarrier
