import Std

/-!
# Parity consequences of a cover clause and pairwise exclusions

The values below are the truth values of literal occurrences. A cover clause
requires at least one value to be true. A binary exclusion for each pair says
that at least one of those two values is false. Together these conditions imply
odd XOR parity. The proof is by induction for lists of arbitrary length.

Signed literals are evaluated as the variable value XOR the negation bit. The
signed theorem explicitly moves all negation bits to the right-hand side of the
derived equation. The model-preservation theorem retains the original formula
and adds only consequences; it does not replace exactly-one by the weaker
parity condition.

These are semantic inference theorems. They do not verify the Python clause
recognizer, its certificates, bit-mask normalization, Gaussian elimination, or
the running time of the preprocessing and search algorithms.
-/

set_option autoImplicit false

namespace BoundaryLab.ExactlyOneParity

def parity (values : List Bool) : Bool := values.foldr Bool.xor false

@[simp] theorem parity_nil : parity [] = false := rfl

@[simp] theorem parity_cons (b : Bool) (values : List Bool) :
    parity (b :: values) = Bool.xor b (parity values) := rfl

private theorem parity_eq_false_of_all_false :
    ∀ values : List Bool,
      (∀ b ∈ values, b = false) → parity values = false := by
  intro values
  induction values with
  | nil =>
      intro _
      rfl
  | cons b values ih =>
      intro h
      have hb : b = false := h b (by simp)
      have ht : ∀ c ∈ values, c = false := by
        intro c hc
        exact h c (by simp [hc])
      rw [parity_cons, hb, ih ht]
      rfl

/-- A cover clause and all binary exclusions imply odd parity. -/
theorem cover_exclusions_imply_parity :
    ∀ values : List Bool,
      true ∈ values →
      values.Pairwise (fun a b => a = false ∨ b = false) →
      parity values = true := by
  intro values
  induction values with
  | nil =>
      intro hc _
      cases hc
  | cons b values ih =>
      intro hc he
      have hp := List.pairwise_cons.mp he
      cases b with
      | false =>
          have ht : true ∈ values := by simpa using hc
          rw [parity_cons, ih ht hp.2]
          rfl
      | true =>
          have ht : ∀ c ∈ values, c = false := by
            intro c hm
            exact (hp.1 c hm).resolve_left (by decide)
          rw [parity_cons, parity_eq_false_of_all_false values ht]
          rfl

structure Literal (V : Type) where
  var : V
  negative : Bool

def eval {V : Type} (assignment : V → Bool) (literal : Literal V) : Bool :=
  Bool.xor (assignment literal.var) literal.negative

private theorem xor_interchange (a b c d : Bool) :
    Bool.xor (Bool.xor a b) (Bool.xor c d) =
      Bool.xor (Bool.xor a c) (Bool.xor b d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

private theorem xor_eq_true_iff (a b : Bool) :
    Bool.xor a b = true ↔ a = Bool.xor true b := by
  cases a <;> cases b <;> decide

/-- Literal parity splits into variable parity and negation-bit parity. -/
theorem parity_of_evaluated_literals
    {V : Type} (assignment : V → Bool) (literals : List (Literal V)) :
    parity (literals.map (eval assignment)) =
      Bool.xor
        (parity (literals.map (fun l => assignment l.var)))
        (parity (literals.map (fun l => l.negative))) := by
  induction literals with
  | nil => rfl
  | cons literal literals ih =>
      simp only [List.map_cons, parity_cons]
      rw [ih]
      exact xor_interchange (assignment literal.var) literal.negative
        (parity (literals.map (fun l => assignment l.var)))
        (parity (literals.map (fun l => l.negative)))

/-- The XOR row implied by exactly one signed literal being true. -/
def DerivedParity
    {V : Type} (assignment : V → Bool) (literals : List (Literal V)) : Prop :=
  parity (literals.map (fun l => assignment l.var)) =
    Bool.xor true (parity (literals.map (fun l => l.negative)))

theorem signed_exactly_one_implies_parity
    {V : Type} (assignment : V → Bool) (literals : List (Literal V))
    (cover : true ∈ literals.map (eval assignment))
    (exclusions : (literals.map (eval assignment)).Pairwise
      (fun a b => a = false ∨ b = false)) :
    DerivedParity assignment literals := by
  have hp := cover_exclusions_imply_parity
    (literals.map (eval assignment)) cover exclusions
  rw [parity_of_evaluated_literals] at hp
  exact (xor_eq_true_iff
    (parity (literals.map (fun l => assignment l.var)))
    (parity (literals.map (fun l => l.negative)))).mp hp

/-- Adding any collection of justified rows preserves each original model. -/
theorem strengthen_preserves_models
    {V I : Type} (original : (V → Bool) → Prop)
    (blocks : I → List (Literal V))
    (cover : ∀ assignment, original assignment → ∀ i,
      true ∈ (blocks i).map (eval assignment))
    (exclusions : ∀ assignment, original assignment → ∀ i,
      ((blocks i).map (eval assignment)).Pairwise
        (fun a b => a = false ∨ b = false))
    (assignment : V → Bool) :
    original assignment ↔
      original assignment ∧ ∀ i, DerivedParity assignment (blocks i) := by
  constructor
  · intro h
    refine ⟨h, ?_⟩
    intro i
    exact signed_exactly_one_implies_parity assignment (blocks i)
      (cover assignment h i) (exclusions assignment h i)
  · intro h
    exact h.1

/-- In particular, adding the justified rows preserves satisfiability. -/
theorem strengthen_preserves_sat
    {V I : Type} (original : (V → Bool) → Prop)
    (blocks : I → List (Literal V))
    (cover : ∀ assignment, original assignment → ∀ i,
      true ∈ (blocks i).map (eval assignment))
    (exclusions : ∀ assignment, original assignment → ∀ i,
      ((blocks i).map (eval assignment)).Pairwise
        (fun a b => a = false ∨ b = false)) :
    (∃ assignment, original assignment) ↔
      ∃ assignment,
        original assignment ∧ ∀ i, DerivedParity assignment (blocks i) := by
  constructor
  · intro h
    obtain ⟨assignment, ha⟩ := h
    exact ⟨assignment,
      (strengthen_preserves_models original blocks cover exclusions assignment).mp ha⟩
  · intro h
    obtain ⟨assignment, ha, _⟩ := h
    exact ⟨assignment, ha⟩

#print axioms cover_exclusions_imply_parity
#print axioms parity_of_evaluated_literals
#print axioms signed_exactly_one_implies_parity
#print axioms strengthen_preserves_models
#print axioms strengthen_preserves_sat

end BoundaryLab.ExactlyOneParity
