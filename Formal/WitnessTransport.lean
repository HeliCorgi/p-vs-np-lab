import Formal.DecisionPruning

/-!
A map goes from TARGET variables to signed SOURCE literals or constants.
Evaluating its images sends an actual SOURCE assignment to a TARGET assignment.
A pulled-back target clause must be trivially true or contain a source clause.
This file does not assert that a useful map can always be found, nor any
width or time bound. It formalizes the certificate rule, not the Python parser.
-/

set_option autoImplicit false

namespace BoundaryLab.WitnessTransport

inductive Term (V : Type) where
  | value (b : Bool)
  | pos (v : V)
  | neg (v : V)
  deriving DecidableEq

abbrev Clause (V : Type) := List (Term V)
abbrev CNF (V : Type) := List (Clause V)

def flip {V : Type} : Term V → Term V
  | .value b => .value (!b)
  | .pos v => .neg v
  | .neg v => .pos v

def eval {V : Type} (a : V → Bool) : Term V → Bool
  | .value b => b
  | .pos v => a v
  | .neg v => !(a v)

private theorem flip_twice {V : Type} (u : Term V) : flip (flip u) = u := by
  cases u with
  | value b => cases b <;> rfl
  | pos _ => rfl
  | neg _ => rfl

private theorem eval_flip {V : Type} (a : V → Bool) (u : Term V) :
    eval a (flip u) = !(eval a u) := by
  cases u with
  | value _ => rfl
  | pos _ => rfl
  | neg v =>
    change a v = !(!(a v))
    cases a v <;> rfl

def pull {S T : Type} (sigma : T → Term S) : Term T → Term S
  | .value b => .value b
  | .pos v => sigma v
  | .neg v => flip (sigma v)

def lift {S T : Type} (sigma : T → Term S) (a : S → Bool) (v : T) : Bool :=
  eval a (sigma v)

theorem eval_pull {S T : Type} (sigma : T → Term S) (a : S → Bool) (u : Term T) :
    eval a (pull sigma u) = eval (lift sigma a) u := by
  cases u with
  | value _ => rfl
  | pos _ => rfl
  | neg v => exact eval_flip a (sigma v)

private theorem pull_flip {S T : Type} (sigma : T → Term S) (u : Term T) :
    pull sigma (flip u) = flip (pull sigma u) := by
  cases u with
  | value _ => rfl
  | pos _ => rfl
  | neg v => exact (flip_twice (sigma v)).symm

def Holds {V : Type} (a : V → Bool) (c : Clause V) : Prop :=
  ∃ u ∈ c, eval a u = true

def Models {V : Type} (a : V → Bool) (f : CNF V) : Prop :=
  ∀ c ∈ f, Holds a c

/-- Leaving a false constant in a pulled-back clause is harmless. Input CNFs
in the program consist of signed literals; here the language also admits
constant terms in any clause. Empty clauses and empty CNFs are included. -/
def Covered {V : Type} (f : CNF V) (c : Clause V) : Prop :=
  Term.value true ∈ c ∨ (∃ u ∈ c, flip u ∈ c) ∨
  ∃ d ∈ f, ∀ u ∈ d, u ∈ c

def Certificate {S T : Type} (f : CNF S) (g : CNF T) (sigma : T → Term S) : Prop :=
  ∀ c ∈ g, Covered f (c.map (pull sigma))

theorem covered_holds {V : Type} {a : V → Bool} {f : CNF V} {c : Clause V}
    (sat : Models a f) (ok : Covered f c) : Holds a c := by
  rcases ok with yes | pair | sub
  · exact ⟨.value true, yes, rfl⟩
  · obtain ⟨u, hu, hn⟩ := pair
    cases h : eval a u with
    | false => exact ⟨flip u, hn, by simp [eval_flip, h]⟩
    | true => exact ⟨u, hu, h⟩
  · obtain ⟨d, hd, subset⟩ := sub
    obtain ⟨u, hu, h⟩ := sat d hd
    exact ⟨u, subset u hu, h⟩

/-- A checked map transports the supplied witness, not just the SAT bit. -/
theorem certificate_transports_model {S T : Type} {f : CNF S} {g : CNF T}
    {sigma : T → Term S} (ok : Certificate f g sigma) (a : S → Bool)
    (sat : Models a f) : Models (lift sigma a) g := by
  intro c hc
  obtain ⟨w, hw, val⟩ := covered_holds sat (ok c hc)
  obtain ⟨u, hu, e⟩ := List.mem_map.mp hw
  rw [← e] at val
  exact ⟨u, hu, (eval_pull sigma a u).symm.trans val⟩

def compose {X Y Z : Type} (sigma : Y → Term X) (tau : Z → Term Y) (z : Z) : Term X :=
  pull sigma (tau z)

private theorem pull_compose {X Y Z : Type} (sigma : Y → Term X) (tau : Z → Term Y)
    (u : Term Z) : pull (compose sigma tau) u = pull sigma (pull tau u) := by
  cases u with
  | value _ => rfl
  | pos _ => rfl
  | neg v => exact (pull_flip sigma (tau v)).symm

theorem lift_compose {X Y Z : Type} (sigma : Y → Term X) (tau : Z → Term Y)
    (a : X → Bool) : lift (compose sigma tau) a = lift tau (lift sigma a) := by
  funext z
  exact eval_pull sigma a (tau z)

private theorem covered_mono {V : Type} {f : CNF V} {c d : Clause V}
    (h : Covered f c) (sub : ∀ u ∈ c, u ∈ d) : Covered f d := by
  rcases h with ht | ⟨u,hu,hn⟩ | ⟨e,he,hsub⟩
  · exact Or.inl (sub _ ht)
  · exact Or.inr (Or.inl ⟨u,sub _ hu,sub _ hn⟩)
  · exact Or.inr (Or.inr ⟨e,he,fun x hx => sub x (hsub x hx)⟩)

private theorem covered_pull {X Y : Type} {f : CNF X} {g : CNF Y} {sigma : Y → Term X}
    (cert : Certificate f g sigma) {d : Clause Y} (h : Covered g d) :
    Covered f (d.map (pull sigma)) := by
  rcases h with ht | ⟨u,hu,hn⟩ | ⟨e,he,hsub⟩
  · exact Or.inl (List.mem_map.mpr ⟨.value true,ht,rfl⟩)
  · refine Or.inr (Or.inl ⟨pull sigma u, List.mem_map.mpr ⟨u,hu,rfl⟩, ?_⟩)
    exact List.mem_map.mpr ⟨flip u,hn,pull_flip sigma u⟩
  · apply covered_mono (cert e he)
    intro w hw
    obtain ⟨u,hu,eq⟩ := List.mem_map.mp hw
    exact List.mem_map.mpr ⟨u,hsub u hu,eq⟩

/-- Syntactic composition: a chain of two certified witness maps produces
another certificate subject to the same clause-by-clause checks. -/
theorem certificate_compose {X Y Z : Type} {f : CNF X} {g : CNF Y} {h : CNF Z}
    {sigma : Y → Term X} {tau : Z → Term Y}
    (fg : Certificate f g sigma) (gh : Certificate g h tau) :
    Certificate f h (compose sigma tau) := by
  intro c hc
  have step := covered_pull fg (gh c hc)
  have e : pull (compose sigma tau) = (pull sigma) ∘ (pull tau) :=
    funext (pull_compose sigma tau)
  rw [e]
  simpa only [List.map_map] using step

def Sat {V : Type} (f : CNF V) : Prop := ∃ a, Models a f

/-- F may be discarded only in the direction F→G, with G kept.
The common variable type just places both residuals in one raw frontier. -/
theorem directed_drop {V : Type} (f g : CNF V) (rest : List (CNF V))
    {sigma : V → Term V} (ok : Certificate f g sigma) :
    DecisionPruning.AnySat Sat (f :: g :: rest) ↔ DecisionPruning.AnySat Sat (g :: rest) := by
  change (Sat f ∨ Sat g ∨ DecisionPruning.AnySat Sat rest) ↔ (Sat g ∨ DecisionPruning.AnySat Sat rest)
  constructor
  · rintro (⟨a,ha⟩ | hr)
    · exact Or.inl ⟨lift sigma a, certificate_transports_model ok a ha⟩
    · exact hr
  · exact Or.inr

end BoundaryLab.WitnessTransport
