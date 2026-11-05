import Formal.IntegerCertificate

/-! Raw binary implications justify a learned disjunction. An integer
certificate may then use these disjunctions as its input. This proves the
semantic composition, not the Python path search or its complexity. -/
set_option autoImplicit false

namespace BoundaryLab.IntegerFeedback
open BoundaryLab.WitnessTransport

private theorem eval_flip' {V : Type} (a : V → Bool) (l : Term V) :
    eval a (flip l) = !(eval a l) := by
  cases l with
  | value _ => rfl
  | pos _ => rfl
  | neg v =>
    change a v = !(!(a v))
    cases a v <;> rfl

/-- The two list orders represent the same raw binary clause. -/
def Edge {V : Type} (f : CNF V) (p q : Term V) : Prop :=
  [flip p, q] ∈ f ∨ [q, flip p] ∈ f

theorem edge_sound {V : Type} {f : CNF V} {p q : Term V} {a : V → Bool}
    (e : Edge f p q) (model : Models a f) (yes : eval a p = true) :
    eval a q = true := by
  have no : eval a (flip p) = false := by simp [eval_flip', yes]
  rcases e with h | h
  · obtain ⟨u, hu, val⟩ := model _ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with h | h
    · subst u
      rw [no] at val
      contradiction
    · simpa [h] using val
  · obtain ⟨u, hu, val⟩ := model _ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with h | h
    · simpa [h] using val
    · subst u
      rw [no] at val
      contradiction

inductive Path {V : Type} (f : CNF V) : Term V → Term V → Prop where
  | refl (p : Term V) : Path f p p
  | step {p q r} (prior : Path f p q) (edge : Edge f q r) : Path f p r

theorem path_sound {V : Type} {f : CNF V} {p q : Term V}
    (path : Path f p q) {a : V → Bool} (model : Models a f) :
    eval a p = true → eval a q = true := by
  induction path with
  | refl p => exact fun h => h
  | step prior edge ih => exact fun h => edge_sound edge model (ih h)

theorem replace_disjunct {V : Type} {f : CNF V} {p q : Term V} {rest : Clause V}
    (source : p :: rest ∈ f) (path : Path f p q) {a : V → Bool}
    (model : Models a f) : Holds a (q :: rest) := by
  obtain ⟨u, member, val⟩ := model _ source
  rcases List.mem_cons.mp member with h | h
  · subst u
    exact ⟨q, by simp, path_sound path model val⟩
  · exact ⟨u, List.mem_cons_of_mem _ h, val⟩

/-- The integer checker proves its rows from the learned formula; this is the
bridge back to the original formula, on the very same assignment. -/
theorem feedback_refutes {V : Type} (f g : CNF V)
    (liftModel : ∀ a, Models a f → Models a g)
    (vs : List V) (m : Int) (ts : List (Int × IntegerCertificate.Row V))
    (valid : ∀ a, Models a g → ∀ t ∈ ts, IntegerCertificate.Holds vs a t.2)
    (compatible : ∀ t ∈ ts, m ∣ t.1 * t.2.modulus)
    (cancel : ∀ v, m ∣ IntegerCertificate.coefficients ts v)
    (contradiction : ¬ m ∣ IntegerCertificate.rightSides ts) : ¬ Sat f :=
  IntegerCertificate.integer_certificate_refutes f vs m ts
    (fun a h => valid a (liftModel a h)) compatible cancel contradiction

end BoundaryLab.IntegerFeedback
