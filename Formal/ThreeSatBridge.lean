import Std

/-!
# A three-literal OR as binary OR clauses plus a ternary XOR

Each clause gets fresh helpers u,v,w. All three original literals being false
would force u=v=w=true, contradicting even parity. Any true literal allows its
helper to be false and the other two true. Independent helpers compose across
all clauses, while the original assignment is shared.

The formula theorem proves equisatisfiability of these predicates. It does not
formalize a Turing-machine encoding, the polynomial construction time, the
Cook--Levin theorem, or the Python implementation.
-/

set_option autoImplicit false

namespace BoundaryLab.ThreeSatBridge

private instance decidableExistsBool (P : Bool → Prop) [DecidablePred P] :
    Decidable (∃ b : Bool, P b) :=
  decidable_of_iff (P false ∨ P true) (by
    constructor
    · intro h
      cases h with
      | inl hf => exact ⟨false, hf⟩
      | inr ht => exact ⟨true, ht⟩
    · intro h
      obtain ⟨b, hb⟩ := h
      cases b with
      | false => exact Or.inl hb
      | true => exact Or.inr hb)

abbrev Helpers := Bool × Bool × Bool

def Clause (a b c : Bool) : Prop := a = true ∨ b = true ∨ c = true

def Gadget (a b c : Bool) (h : Helpers) : Prop :=
  (a = true ∨ h.1 = true) ∧
  (b = true ∨ h.2.1 = true) ∧
  (c = true ∨ h.2.2 = true) ∧
  Bool.xor (Bool.xor h.1 h.2.1) h.2.2 = false

instance (a b c : Bool) : Decidable (Clause a b c) := by
  unfold Clause
  infer_instance

instance (a b c : Bool) (h : Helpers) : Decidable (Gadget a b c h) := by
  unfold Gadget
  infer_instance

private theorem finite_clause_bridge :
    ∀ a b c : Bool, Clause a b c ↔
      ∃ u v w : Bool, Gadget a b c (u, v, w) := by
  decide

theorem clause_iff_gadget (a b c : Bool) :
    Clause a b c ↔ ∃ h : Helpers, Gadget a b c h := by
  constructor
  · intro hc
    obtain ⟨u, v, w, h⟩ := (finite_clause_bridge a b c).mp hc
    exact ⟨(u, v, w), h⟩
  · intro hg
    obtain ⟨⟨u, v, w⟩, h⟩ := hg
    exact (finite_clause_bridge a b c).mpr ⟨u, v, w, h⟩

theorem clauses_iff_independent_helpers
    {I : Type} (a b c : I → Bool) :
    (∀ i : I, Clause (a i) (b i) (c i)) ↔
      ∃ helpers : I → Helpers, ∀ i : I, Gadget (a i) (b i) (c i) (helpers i) := by
  constructor
  · intro h
    have local_witness : ∀ i : I, ∃ h : Helpers, Gadget (a i) (b i) (c i) h :=
      fun i => (clause_iff_gadget (a i) (b i) (c i)).mp (h i)
    exact ⟨fun i => Classical.choose (local_witness i),
      fun i => Classical.choose_spec (local_witness i)⟩
  · intro h
    obtain ⟨helpers, hh⟩ := h
    intro i
    exact (clause_iff_gadget (a i) (b i) (c i)).mpr ⟨helpers i, hh i⟩

theorem formula_sat_iff
    {X I : Type} (a b c : X → I → Bool) :
    (∃ x : X, ∀ i : I, Clause (a x i) (b x i) (c x i)) ↔
      ∃ x : X, ∃ helpers : I → Helpers,
        ∀ i : I, Gadget (a x i) (b x i) (c x i) (helpers i) := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h
    exact ⟨x, (clauses_iff_independent_helpers (a x) (b x) (c x)).mp hx⟩
  · intro h
    obtain ⟨x, helpers, hh⟩ := h
    exact ⟨x, (clauses_iff_independent_helpers (a x) (b x) (c x)).mpr ⟨helpers, hh⟩⟩

#print axioms clause_iff_gadget
#print axioms clauses_iff_independent_helpers
#print axioms formula_sat_iff

end BoundaryLab.ThreeSatBridge
