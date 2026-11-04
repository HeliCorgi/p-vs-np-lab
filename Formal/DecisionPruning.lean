import Std

/-!
A frontier is a disjunction of decision instances. A label for the anchored
disjunction (a OR x) need only be decision-faithful; equal truth assignments
to the two residuals are not required. Neither faithfulness nor a small
capacity is asserted to hold for any particular efficiently computed label.
The capacity is a bound on DISTINCT POSITIVE labels, not on all labels.
This file proves semantic preservation, not any time or width bound.
-/

set_option autoImplicit false

namespace BoundaryLab.DecisionPruning

def AnySat {F : Type} (sat : F → Prop) : List F → Prop
  | [] => False
  | x :: xs => sat x ∨ AnySat sat xs

def Faithful {F L : Type} (sat : F → Prop) (pos : L → Prop) (key : F → F → L) : Prop :=
  ∀ a x, pos (key a x) ↔ sat a ∨ sat x

def Capacity {L : Type} (pos : L → Prop) (bound : Nat) : Prop :=
  ∀ ls : List L, ls.Nodup → (∀ z, z ∈ ls → pos z) → ls.length ≤ bound

/-- If the anchor is false, a collision transfers the deleted partner's YES
answer to the retained partner; if the anchor is true it is already retained. -/
theorem anchored_collision {F L : Type} (sat : F → Prop) (pos : L → Prop)
    (key : F → F → L) (ok : Faithful sat pos key) (a x y : F) (rest : List F)
    (eqkey : key a x = key a y) :
    AnySat sat (a :: x :: y :: rest) ↔ AnySat sat (a :: x :: rest) := by
  change (sat a ∨ sat x ∨ sat y ∨ AnySat sat rest) ↔ (sat a ∨ sat x ∨ AnySat sat rest)
  constructor
  · intro h
    rcases h with ha | hx | hy | hr
    · exact Or.inl ha
    · exact Or.inr (Or.inl hx)
    · have hp : pos (key a y) := (ok a y).mpr (Or.inr hy)
      rw [← eqkey] at hp
      rcases (ok a x).mp hp with ha | hx
      · exact Or.inl ha
      · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr hr)
  · intro h
    rcases h with ha | hx | hr
    · exact Or.inl ha
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr (Or.inr hr))

/-- More distinct partner labels than the positive capacity refute the anchor.
Membership in the positive set need not be decidable or tested by the search. -/
theorem distinct_refutes_anchor {F L : Type} (sat : F → Prop) (pos : L → Prop)
    (key : F → F → L) (ok : Faithful sat pos key) (bound : Nat) (cap : Capacity pos bound)
    (a : F) (xs : List F) (hd : (xs.map (key a)).Nodup) (many : bound < xs.length) :
    ¬ sat a := by
  intro ha
  have hp : ∀ z, z ∈ xs.map (key a) → pos z := by
    intro z hz
    obtain ⟨x, _, he⟩ := List.mem_map.mp hz
    rw [← he]
    exact (ok a x).mpr (Or.inl ha)
  have hlen : xs.length ≤ bound := by simpa using cap (xs.map (key a)) hd hp
  exact (Nat.not_lt_of_ge hlen) many

/-- Certificates for a finite schedule of safe deletions, including reordering.
No capacity need be consulted in the collision constructor. -/
inductive Thin {F L : Type} (key : F → F → L) (bound : Nat) : List F → List F → Prop where
  | same (xs : List F) : Thin key bound xs xs
  | collision (a x y : F) (xs : List F) (h : key a x = key a y) :
      Thin key bound (a :: x :: y :: xs) (a :: x :: xs)
  | crowded (a : F) (xs : List F) (h : (xs.map (key a)).Nodup) (many : bound < xs.length) :
      Thin key bound (a :: xs) xs
  | keep (z : F) {xs ys : List F} (h : Thin key bound xs ys) :
      Thin key bound (z :: xs) (z :: ys)
  | swap (x y : F) (xs : List F) : Thin key bound (x :: y :: xs) (y :: x :: xs)
  | chain {xs ys zs : List F} (h₁ : Thin key bound xs ys) (h₂ : Thin key bound ys zs) :
      Thin key bound xs zs

theorem thin_preserves {F L : Type} (sat : F → Prop) (pos : L → Prop)
    (key : F → F → L) (ok : Faithful sat pos key) (bound : Nat) (cap : Capacity pos bound)
    {xs ys : List F} (steps : Thin key bound xs ys) : AnySat sat xs ↔ AnySat sat ys := by
  induction steps with
  | same _ => exact Iff.rfl
  | collision a x y xs h => exact anchored_collision sat pos key ok a x y xs h
  | crowded a xs hd hm =>
    have no := distinct_refutes_anchor sat pos key ok bound cap a xs hd hm
    constructor
    · intro h
      rcases h with ha | hr
      · exact False.elim (no ha)
      · exact hr
    · exact fun hr => Or.inr hr
  | keep _ _ ih =>
    constructor
    · intro h
      rcases h with hz | hr
      · exact Or.inl hz
      · exact Or.inr (ih.mp hr)
    · intro h
      rcases h with hz | hr
      · exact Or.inl hz
      · exact Or.inr (ih.mpr hr)
  | swap x y xs =>
    change (sat x ∨ sat y ∨ AnySat sat xs) ↔ (sat y ∨ sat x ∨ AnySat sat xs)
    exact or_left_comm
  | chain _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def splitEach {F : Type} (child : F → F × F) : List F → List F
  | [] => []
  | x :: xs => (child x).1 :: (child x).2 :: splitEach child xs

theorem split_preserves {F : Type} (sat : F → Prop) (child : F → F × F)
    (branches : ∀ x, sat x ↔ sat (child x).1 ∨ sat (child x).2) (xs : List F) :
    AnySat sat xs ↔ AnySat sat (splitEach child xs) := by
  induction xs with
  | nil => exact Iff.rfl
  | cons x xs ih =>
    change (sat x ∨ AnySat sat xs) ↔
      (sat (child x).1 ∨ sat (child x).2 ∨ AnySat sat (splitEach child xs))
    rw [branches x, ih]
    exact or_assoc

def rounds {F : Type} (child : F → F × F) (prune : List F → List F) : Nat → List F → List F
  | 0, xs => xs
  | n+1, xs => rounds child prune n (prune (splitEach child xs))

/-- Compose actual certified thinning operations and exhaustive binary splits.
This need not shrink the frontier at all: identity pruning is legal. -/
theorem rounds_preserve {F L : Type} (sat : F → Prop) (pos : L → Prop)
    (key : F → F → L) (ok : Faithful sat pos key) (bound : Nat) (cap : Capacity pos bound)
    (child : F → F × F) (branches : ∀ x, sat x ↔ sat (child x).1 ∨ sat (child x).2)
    (prune : List F → List F) (legal : ∀ xs, Thin key bound xs (prune xs))
    (fuel : Nat) (xs : List F) :
    AnySat sat xs ↔ AnySat sat (rounds child prune fuel xs) := by
  induction fuel generalizing xs with
  | zero => exact Iff.rfl
  | succ n ih =>
    exact (split_preserves sat child branches xs).trans
      ((thin_preserves sat pos key ok bound cap (legal (splitEach child xs))).trans
        (ih (prune (splitEach child xs))))

end BoundaryLab.DecisionPruning
