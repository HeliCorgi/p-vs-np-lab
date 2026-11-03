import Std

/-!
# Exact decisions from finite supports and affine observations

`Reach` chooses one original option from each group. It can be interpreted
at any prefix state, so past choices producing the same state have precisely
the same possible completions. We relate it to explicit witnesses, prove
that necessary suffix tests preserve decisions, and derive such a test from
a homomorphism which is constant on each remaining support. For the Python
solver this observation is reduction modulo the suffix difference space.

The last theorem uses actual pointwise XOR of bit vectors: if old choices
fill an exact coset and a new group's image fills an exact coset modulo the
old direction space, their sums fill the translated new coset, with original
choices on the existential side. The exact-image premise matters: containment
in an affine hull does not suffice.

These semantic theorems do not formalize the echelon-basis implementation,
the rank/cardinality test, the 3SAT reduction, the grid bound or running time.
-/

set_option autoImplicit false

namespace BoundaryLab.AffineFrontier

def Reach {X S : Type} (step : S → X → S) : List (List X) → S → S → Prop
  | [], state, target => state = target
  | g :: gs, state, target =>
      ∃ x, x ∈ g ∧ Reach step gs (step state x) target

def Picks {X : Type} : List (List X) → List X → Prop
  | [], [] => True
  | g :: gs, x :: xs => x ∈ g ∧ Picks gs xs
  | _, _ => False

def accumulate {X S : Type} (step : S → X → S) : List X → S → S
  | [], state => state
  | x :: xs, state => accumulate step xs (step state x)

/-- Feasibility is equivalent to a trace of original members that hits the target. -/
theorem reach_iff_recorded_choices {X S : Type} (step : S → X → S)
    (groups : List (List X)) (state target : S) :
    Reach step groups state target ↔
      ∃ xs, Picks groups xs ∧ accumulate step xs state = target := by
  induction groups generalizing state with
  | nil =>
    constructor
    · intro h
      exact ⟨[], True.intro, h⟩
    · intro h
      obtain ⟨xs, hx, he⟩ := h
      cases xs with
      | nil => exact he
      | cons x tail => exact False.elim hx
  | cons g gs ih =>
    constructor
    · intro h
      obtain ⟨x, hx, hr⟩ := h
      obtain ⟨xs, hxs, he⟩ := (ih (step state x)).mp hr
      exact ⟨x :: xs, ⟨hx, hxs⟩, he⟩
    · intro h
      obtain ⟨xs, hx, he⟩ := h
      cases xs with
      | nil => exact False.elim hx
      | cons x tail =>
        exact ⟨x, hx.1, (ih (step state x)).mpr ⟨tail, hx.2, he⟩⟩

def Pruned {X S : Type} (step : S → X → S) (keep : List (List X) → S → Prop) :
    List (List X) → S → S → Prop
  | [], state, target => keep [] state ∧ state = target
  | g :: gs, state, target =>
      keep (g :: gs) state ∧ ∃ x, x ∈ g ∧ Pruned step keep gs (step state x) target

/-- Applying a necessary test at *every* cut loses no exact completion. -/
theorem pruned_iff_reach {X S : Type} (step : S → X → S)
    (keep : List (List X) → S → Prop) (target : S)
    (necessary : ∀ gs p, Reach step gs p target → keep gs p)
    (groups : List (List X)) (state : S) :
    Pruned step keep groups state target ↔ Reach step groups state target := by
  induction groups generalizing state with
  | nil =>
    constructor
    · intro h
      exact h.2
    · intro h
      exact ⟨necessary [] state h, h⟩
  | cons g gs ih =>
    constructor
    · intro h
      obtain ⟨_, x, hx, hr⟩ := h
      exact ⟨x, hx, (ih (step state x)).mp hr⟩
    · intro h
      have hk := necessary (g :: gs) state h
      obtain ⟨x, hx, hr⟩ := h
      exact ⟨hk, x, hx, (ih (step state x)).mpr hr⟩

def ConstantViews {X Y : Type} (view : X → Y) : List (List X) → List Y → Prop
  | [], [] => True
  | g :: gs, b :: bs => (∀ x, x ∈ g → view x = b) ∧ ConstantViews view gs bs
  | _, _ => False

/-- If a quotient map is compatible with composition and all options of each
remaining group have the same image, these images force the observed target. -/
theorem suffix_observation_forced {X S Y T : Type}
    (step : S → X → S) (combine : T → Y → T) (observe : S → T) (view : X → Y)
    (compatible : ∀ p x, observe (step p x) = combine (observe p) (view x))
    (groups : List (List X)) (state target : S) (summaries : List Y)
    (hc : ConstantViews view groups summaries) (hr : Reach step groups state target) :
    observe target = accumulate combine summaries (observe state) := by
  induction groups generalizing state summaries with
  | nil =>
    cases summaries with
    | nil =>
      change state = target at hr
      exact (congrArg observe hr).symm
    | cons b bs => exact False.elim hc
  | cons g gs ih =>
    cases summaries with
    | nil => exact False.elim hc
    | cons b bs =>
      obtain ⟨hg, ht⟩ := hc
      obtain ⟨x, hx, htail⟩ := hr
      have he : observe target = accumulate combine bs (observe (step state x)) :=
        ih (state := step state x) (summaries := bs) ht htail
      rw [compatible state x, hg x hx] at he
      exact he

abbrev Mask (ι : Type) := ι → Bool

def plus {ι : Type} (x y : Mask ι) : Mask ι := fun i => Bool.xor (x i) (y i)

private theorem plus_cancel {ι : Type} (x y : Mask ι) : plus (plus x y) y = x := by
  funext i
  change Bool.xor (Bool.xor (x i) (y i)) (y i) = x i
  cases x i <;> cases y i <;> rfl

private theorem plus_swap {ι : Type} (x y z : Mask ι) :
    plus (plus x y) z = plus (plus x z) y := by
  funext i
  change Bool.xor (Bool.xor (x i) (y i)) (z i) = Bool.xor (Bool.xor (x i) (z i)) (y i)
  cases x i <;> cases y i <;> cases z i <;> rfl

private theorem plus_assoc {ι : Type} (x y z : Mask ι) :
    plus (plus x y) z = plus x (plus y z) := by
  funext i
  change Bool.xor (Bool.xor (x i) (y i)) (z i) = Bool.xor (x i) (Bool.xor (y i) (z i))
  cases x i <;> cases y i <;> cases z i <;> rfl

/-- One exact absorption step. U and V describe old and enlarged direction
spaces in the application. Only the two specified fiber identities are needed. -/
theorem absorb_exact_image {ι : Type} (before group U V : Mask ι → Prop)
    (anchor groupAnchor target : Mask ι)
    (before_exact : ∀ b, before b ↔ U (plus b anchor))
    (image_exact : ∀ t, (∃ s, group s ∧ U (plus t s)) ↔ V (plus t groupAnchor)) :
    (∃ b s, before b ∧ group s ∧ plus b s = target) ↔
      V (plus target (plus anchor groupAnchor)) := by
  constructor
  · intro h
    obtain ⟨b, s, hb, hs, he⟩ := h
    have eb : b = plus target s := by
      rw [← he, plus_cancel]
    have hu : U (plus (plus target anchor) s) := by
      rw [plus_swap target anchor s, ← eb]
      exact (before_exact b).mp hb
    rw [← plus_assoc target anchor groupAnchor]
    exact (image_exact (plus target anchor)).mp ⟨s, hs, hu⟩
  · intro h
    have hv : V (plus (plus target anchor) groupAnchor) := by
      rw [plus_assoc]
      exact h
    obtain ⟨s, hs, hu⟩ := (image_exact (plus target anchor)).mpr hv
    refine ⟨plus target s, s, (before_exact _).mpr ?_, hs, plus_cancel target s⟩
    rw [plus_swap target s anchor]
    exact hu

end BoundaryLab.AffineFrontier
