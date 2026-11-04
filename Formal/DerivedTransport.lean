import Formal.WitnessTransport

/-! Semantic kernel of the local proof language. The trail is represented
by the literals known false. A unit reason cites one member of the original
CNF and a currently forced literal. This formalizes soundness for finite
unit/split trees, not the Python reader, the search budget, or running time. -/
set_option autoImplicit false

namespace BoundaryLab.DerivedTransport
open WitnessTransport

def FalseTrail {V : Type} (a : V → Bool) (trail : Clause V) : Prop :=
  ∀ l ∈ trail, eval a l = false

private theorem eval_flip' {V : Type} (a : V → Bool) (l : Term V) :
    eval a (flip l) = !(eval a l) := by
  cases l with
  | value _ => rfl
  | pos _ => rfl
  | neg v =>
    change a v = !(!(a v))
    cases a v <;> rfl

private theorem extend_false {V : Type} {a : V → Bool} {trail : Clause V} {l : Term V}
    (prior : FalseTrail a trail) (next : eval a l = false) : FalseTrail a (l :: trail) := by
  intro v hv
  rcases List.mem_cons.mp hv with h | h
  · simpa [h] using next
  · exact prior v h

theorem unit_forced {V : Type} {a : V → Bool} {c trail : Clause V} {l : Term V}
    (hc : Holds a c) (prior : FalseTrail a trail)
    (others : ∀ v ∈ c, v = l ∨ v ∈ trail) : eval a l = true := by
  obtain ⟨v, hv, yes⟩ := hc
  rcases others v hv with eq | bad
  · simpa [← eq] using yes
  · rw [prior v bad] at yes
    contradiction

inductive Closed {V : Type} (f : CNF V) : Clause V → Prop where
  | conflict {trail} (c : Clause V) (hc : c ∈ f) (dead : ∀ l ∈ c, l ∈ trail) :
      Closed f trail
  | unitStep {trail} (c : Clause V) (l : Term V) (hc : c ∈ f) (hl : l ∈ c)
      (others : ∀ v ∈ c, v = l ∨ v ∈ trail) (child : Closed f (flip l :: trail)) :
      Closed f trail
  | split {trail} (l : Term V) (zero : Closed f (l :: trail))
      (one : Closed f (flip l :: trail)) : Closed f trail

theorem closed_sound {V : Type} {f : CNF V} {trail : Clause V} (p : Closed f trail)
    (a : V → Bool) (m : Models a f) : ¬ FalseTrail a trail := by
  induction p with
  | conflict c hc dead =>
    intro prior
    obtain ⟨l, hl, yes⟩ := m c hc
    rw [prior l (dead l hl)] at yes
    contradiction
  | unitStep c l hc _ others _ ih =>
    intro prior
    have pos := unit_forced (m c hc) prior others
    exact ih (extend_false prior (by simp [eval_flip', pos]))
  | split l _ _ ih0 ih1 =>
    intro prior
    cases h : eval a l with
    | false => exact ih0 (extend_false prior h)
    | true => exact ih1 (extend_false prior (by simp [eval_flip', h]))

theorem refutes_negation_entails {V : Type} {f : CNF V} {c : Clause V}
    (p : Closed f c) (a : V → Bool) (m : Models a f) : Holds a c := by
  classical
  by_cases good : Holds a c
  · exact good
  · apply False.elim
    apply closed_sound p a m
    intro l hl
    cases h : eval a l with
    | false => rfl
    | true => exact False.elim (good ⟨l, hl, h⟩)

def Reasons {S T : Type} (f : CNF S) (g : CNF T) (sigma : T → Term S) : Prop :=
  ∀ c ∈ g, Covered f (c.map (pull sigma)) ∨ Closed f (c.map (pull sigma))

theorem transports_model {S T : Type} {f : CNF S} {g : CNF T} {sigma : T → Term S}
    (ok : Reasons f g sigma) (a : S → Bool) (m : Models a f) : Models (lift sigma a) g := by
  intro c hc
  have ent : Holds a (c.map (pull sigma)) := by
    rcases ok c hc with sub | localProof
    · exact covered_holds m sub
    · exact refutes_negation_entails localProof a m
  obtain ⟨l, hl, yes⟩ := ent
  obtain ⟨v, hv, eq⟩ := List.mem_map.mp hl
  rw [← eq] at yes
  exact ⟨v, hv, (eval_pull sigma a v).symm.trans yes⟩

theorem justified_drop {V : Type} (f g : CNF V) (rest : List (CNF V)) {sigma : V → Term V}
    (ok : Reasons f g sigma) :
    DecisionPruning.AnySat Sat (f :: g :: rest) ↔ DecisionPruning.AnySat Sat (g :: rest) := by
  change (Sat f ∨ Sat g ∨ DecisionPruning.AnySat Sat rest) ↔ (Sat g ∨ DecisionPruning.AnySat Sat rest)
  constructor
  · rintro (⟨a, m⟩ | hr)
    · exact Or.inl ⟨lift sigma a, transports_model ok a m⟩
    · exact hr
  · exact Or.inr

end BoundaryLab.DerivedTransport
