import Formal.SupportLocalization
import Formal.ExactlyOneParity

/-! Semantic components of phase 19. Flipping one fresh coordinate gives both
answers to a parity query, while a satisfying matching can keep every clause
true. The certificate theorem proves the path/branch rule. This file does not
formalize Hall matching, the expander construction, the asymptotic lower bound,
or the Python Gaussian-elimination checker. -/
set_option autoImplicit false

namespace BoundaryLab.ParityQueries
open BoundaryLab.WitnessTransport
open BoundaryLab.SupportLocalization

def query {V : Type} (a : V → Bool) (vs : List V) : Bool :=
  ExactlyOneParity.parity (vs.map a)

private theorem query_cons {V : Type} (a : V → Bool) (v : V) (vs : List V) :
    query a (v :: vs) = Bool.xor (a v) (query a vs) := rfl

private theorem outside_unchanged {V : Type} [DecidableEq V]
    (a : V → Bool) (x : V) (b : Bool) (vs : List V) (outside : x ∉ vs) :
    query (setBit a x b) vs = query a vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    have ne : v ≠ x := by
      intro h
      subst v
      exact outside (by simp)
    have tail : x ∉ vs := fun h => outside (List.mem_cons_of_mem _ h)
    rw [query_cons, query_cons, ih tail]
    simp [setBit, ne]

/-- A coordinate occurring exactly once in a parity query changes its answer.
The non-repetition hypothesis matters: two occurrences would cancel. -/
theorem unique_coordinate_changes_answer {V : Type} [DecidableEq V]
    (a : V → Bool) (x : V) (vs : List V) (unique : vs.Nodup) (hit : x ∈ vs) :
    query (setBit a x false) vs ≠ query (setBit a x true) vs := by
  induction vs with
  | nil => simp at hit
  | cons v vs ih =>
    have nd := List.nodup_cons.mp unique
    by_cases same : v = x
    · subst v
      rw [query_cons, query_cons,
        outside_unchanged a x false vs nd.1,
        outside_unchanged a x true vs nd.1]
      simp only [setBit, if_pos rfl]
      cases query a vs <;> decide
    · have tail : x ∈ vs := by
        rcases List.mem_cons.mp hit with h | h
        · exact False.elim (same h.symm)
        · exact h
      have different := ih nd.2 tail
      rw [query_cons, query_cons]
      simp only [setBit, if_neg same]
      cases a v <;>
        cases query (setBit a x false) vs <;>
        cases query (setBit a x true) vs <;> simp_all

private theorem either_value (p q b : Bool) (different : p ≠ q) : b = p ∨ b = q := by
  cases p <;> cases q <;> cases b <;> simp_all

/-- If a coordinate can be left free while satisfying a CNF, either parity
answer can be realized without changing any other coordinate. -/
theorem free_coordinate_answers {V : Type} [DecidableEq V]
    (f : CNF V) (a : V → Bool) (x : V) (vs : List V)
    (unique : vs.Nodup) (hit : x ∈ vs)
    (free : ∀ b, Models (setBit a x b) f) (answer : Bool) :
    ∃ a', Models a' f ∧ query a' vs = answer ∧
      ∀ v, v ≠ x → a' v = a v := by
  have diff := unique_coordinate_changes_answer a x vs unique hit
  rcases either_value _ _ answer diff with h | h
  · refine ⟨setBit a x false, free false, h.symm, ?_⟩
    intro v ne
    simp [setBit, ne]
  · refine ⟨setBit a x true, free true, h.symm, ?_⟩
    intro v ne
    simp [setBit, ne]

structure Equation (V : Type) where
  variables : List V
  answer : Bool

def Compatible {V : Type} (a : V → Bool) (path : List (Equation V)) : Prop :=
  ∀ row ∈ path, query a row.variables = row.answer

inductive Refutation {V : Type} (f : CNF V) : List (Equation V) → Prop where
  | impossible {path} (clash : ∀ a, Compatible a path → False) : Refutation f path
  | leaf {path} (c : Clause V) (raw : c ∈ f)
      (reject : ∀ a, Compatible a path → ¬ Holds a c) : Refutation f path
  | split {path} (vs : List V)
      (zero : Refutation f (⟨vs, false⟩ :: path))
      (one : Refutation f (⟨vs, true⟩ :: path)) : Refutation f path

/-- Checked path implications and two-way parity coverage give a refutation.
The leaf implication must be established, not supplied as an unchecked axiom. -/
theorem parity_tree_refutes {V : Type} {f : CNF V} {path : List (Equation V)}
    (proof : Refutation f path) :
    ∀ a, Compatible a path → ¬ Models a f := by
  induction proof with
  | impossible clash =>
    intro a hp _
    exact clash a hp
  | leaf c raw reject =>
    intro a hp model
    exact reject a hp (model c raw)
  | split vs zero one ihZero ihOne =>
    intro a hp
    cases h : query a vs with
    | false =>
      apply ihZero a
      intro row member
      rcases List.mem_cons.mp member with eq | old
      · subst row
        exact h
      · exact hp row old
    | true =>
      apply ihOne a
      intro row member
      rcases List.mem_cons.mp member with eq | old
      · subst row
        exact h
      · exact hp row old

/-- Each offered query exposes at most q fresh variables. The absorbed set
then leaves the same 8*M reserve as in phase 18. -/
theorem query_budget_reserve (q k a c s m : Nat)
    (exposed : a ≤ q*k) (budget : q*k + m ≤ s/8) (absorbed : c ≤ 8*a) :
    c + 8*m ≤ s := by
  omega

end BoundaryLab.ParityQueries
