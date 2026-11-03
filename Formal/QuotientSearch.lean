import Std

/-!
# Exact search through a quotient with a valid right inverse

This is the logical core of the mixed solver's argument. `X` denotes complete
assignments, `Y` the observable quotient coordinates, `linear` feasibility for
the affine part, and `residual` the remaining predicate on quotient coordinates.

The hypotheses are substantive: every quotient value must have a valid lift,
and observing that lift must recover the quotient value. They are established
mathematically by the solver's linear-algebra construction, but the Python
implementation of that construction is NOT formalized by these lemmas.

The finite scan theorem proves exact decision only. It gives no polynomial
time bound; the quotient can have exponentially many elements.
-/

set_option autoImplicit false

namespace BoundaryLab.Quotient

theorem quotient_sat_iff
    {X Y : Type} (linear : X → Prop) (residual : Y → Prop)
    (observe : X → Y) (lift : Y → X)
    (lift_valid : ∀ y : Y, linear (lift y))
    (right_inverse : ∀ y : Y, observe (lift y) = y) :
    (∃ x : X, linear x ∧ residual (observe x)) ↔
      ∃ y : Y, residual y := by
  constructor
  · intro h
    obtain ⟨x, _, hx⟩ := h
    exact ⟨observe x, hx⟩
  · intro h
    obtain ⟨y, hy⟩ := h
    refine ⟨lift y, lift_valid y, ?_⟩
    rw [right_inverse y]
    exact hy

theorem lifted_witness_is_valid
    {X Y : Type} (linear : X → Prop) (residual : Y → Prop)
    (observe : X → Y) (lift : Y → X)
    (lift_valid : ∀ y : Y, linear (lift y))
    (right_inverse : ∀ y : Y, observe (lift y) = y)
    (y : Y) (hy : residual y) :
    linear (lift y) ∧ residual (observe (lift y)) := by
  constructor
  · exact lift_valid y
  · rw [right_inverse y]
    exact hy

theorem quotient_unsat_iff
    {X Y : Type} (linear : X → Prop) (residual : Y → Prop)
    (observe : X → Y) (lift : Y → X)
    (lift_valid : ∀ y : Y, linear (lift y))
    (right_inverse : ∀ y : Y, observe (lift y) = y) :
    (¬ ∃ x : X, linear x ∧ residual (observe x)) ↔
      ∀ y : Y, ¬ residual y := by
  constructor
  · intro h y hy
    apply h
    exact ⟨lift y, lifted_witness_is_valid linear residual observe lift
      lift_valid right_inverse y hy⟩
  · intro h hexists
    obtain ⟨x, _, hx⟩ := hexists
    exact h (observe x) hx

/-- A Boolean scan is exact when the enumerated quotient values cover Y. -/
theorem finite_scan_exact
    {X Y : Type} (linear : X → Prop) (residual : Y → Prop)
    (observe : X → Y) (lift : Y → X)
    (lift_valid : ∀ y : Y, linear (lift y))
    (right_inverse : ∀ y : Y, observe (lift y) = y)
    (values : List Y) (covers : ∀ y : Y, y ∈ values)
    (accept : Y → Bool) (accept_correct : ∀ y : Y, accept y = true ↔ residual y) :
    values.any accept = true ↔ ∃ x : X, linear x ∧ residual (observe x) := by
  have scan_iff : values.any accept = true ↔ ∃ y : Y, residual y := by
    constructor
    · intro h
      obtain ⟨y, _, hy⟩ := List.any_eq_true.mp h
      exact ⟨y, (accept_correct y).mp hy⟩
    · intro h
      obtain ⟨y, hy⟩ := h
      apply List.any_eq_true.mpr
      exact ⟨y, covers y, (accept_correct y).mpr hy⟩
  exact scan_iff.trans
    (quotient_sat_iff linear residual observe lift lift_valid right_inverse).symm

/-- Explicit binary vectors illustrate the cost of exhaustive quotient search. -/
def bitVectors : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (bitVectors n).map (fun xs => false :: xs) ++
      (bitVectors n).map (fun xs => true :: xs)

theorem bitVectors_length (n : Nat) : (bitVectors n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [bitVectors, ih, Nat.pow_succ, Nat.mul_two]

#print axioms quotient_sat_iff
#print axioms lifted_witness_is_valid
#print axioms quotient_unsat_iff
#print axioms finite_scan_exact
#print axioms bitVectors_length

end BoundaryLab.Quotient
