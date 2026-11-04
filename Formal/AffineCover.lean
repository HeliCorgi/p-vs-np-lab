import Std

/-!
# Projection and algebraic certificates for an affine-event cover

Projection is stated pointwise at any remaining assignment. The selector
identities are equalities of Boolean functions, where XOR and AND interpret
addition and multiplication over GF(2). The last result shows the semantic
reason an identically-one sum of weighted event indicators certifies cover.
These lemmas do not formalize row reduction, counting, proof search, a PC
degree lower bound, Python code, or a bit-time claim.
-/
set_option autoImplicit false

namespace BoundaryLab.AffineCover

/-- One bit can be lifted iff no common bad event occurs and no pair of bad
slices, potentially from different events, blocks both choices. -/
theorem bit_projection_iff {I : Type} (common : Prop) (event : I → Bool → Prop) :
    (∃ b : Bool, ¬ (common ∨ ∃ i, event i b)) ↔
      ¬ (common ∨ ∃ i j, event i false ∧ event j true) := by
  classical
  constructor
  · intro lifted blocked
    obtain ⟨b, hb⟩ := lifted
    rcases blocked with hc | ⟨i, j, hf, ht⟩
    · exact hb (Or.inl hc)
    · cases b with
      | false => exact hb (Or.inr ⟨i, hf⟩)
      | true => exact hb (Or.inr ⟨j, ht⟩)
  · intro good
    have nc : ¬common := fun hc => good (Or.inl hc)
    by_cases blockedFalse : ∃ i, event i false
    · obtain ⟨i, hi⟩ := blockedFalse
      refine ⟨true, ?_⟩
      intro h
      rcases h with hc | ⟨j, hj⟩
      · exact nc hc
      · exact good (Or.inr ⟨i, j, hi, hj⟩)
    · refine ⟨false, ?_⟩
      intro h
      rcases h with hc | hf
      · exact nc hc
      · exact blockedFalse hf

/-- The third odd-parity selector, in terms of the first two. -/
def third (u v : Bool) : Bool := !(Bool.xor u v)

/-- The falsity indicator of a source clause as a weighted XOR of three
occurrence-hole indicators. This identity does not use the selector-only hole. -/
theorem selector_cubic_identity (f g h u v : Bool) :
    Bool.xor (Bool.xor ((g && h) && (f && u)) ((f && h) && (g && v)))
      ((f && g) && (h && third u v)) = (f && g && h) := by
  cases f <;> cases g <;> cases h <;> cases u <;> cases v <;> rfl

/-- Set u to truth(l1) and v to false(l1)*truth(l2). On substitution the
selector hole and the first two occurrence holes vanish; the last equals
the source-clause falsity indicator. -/
theorem priority_selector_substitution (f g h : Bool) :
    let u := !f
    let v := f && (!g)
    (u && v) = false ∧ (f && u) = false ∧ (g && v) = false ∧
      (h && third u v) = (f && g && h) := by
  cases f <;> cases g <;> cases h <;> decide

/-- Two occurrence-like holes with a single shared selector bit. -/
def compactFirst (f z : Bool) : Bool := f && (!z)
def compactSecond (g h z : Bool) : Bool := g && Bool.xor (!z) h

/-- Source falsity is recovered as g*E1 + f*E2 (Boolean squarefree arithmetic). -/
theorem compact_cubic_identity (f g h z : Bool) :
    Bool.xor (g && compactFirst f z) (f && compactSecond g h z) = (f && g && h) := by
  cases f <;> cases g <;> cases h <;> cases z <;> rfl

/-- A degree-two selector substitution kills E1 and pulls E2 back to its source clause. -/
theorem compact_selector_substitution (f g h : Bool) :
    let z := !((!f) && h)
    compactFirst f z = false ∧ compactSecond g h z = (f && g && h) := by
  cases f <;> cases g <;> cases h <;> decide

/-- A finite GF(2) sum with event labels and arbitrary pointwise multipliers. -/
def weightedXor {X I : Type} (event : I → X → Bool) : List (I × (X → Bool)) → X → Bool
  | [], _ => false
  | (i, w) :: tail, x => Bool.xor (w x && event i x) (weightedXor event tail x)

private theorem weighted_zero {X I : Type} (event : I → X → Bool) (x : X)
    (absent : ∀ i, event i x = false) (terms : List (I × (X → Bool))) :
    weightedXor event terms x = false := by
  induction terms with
  | nil => rfl
  | cons term tail ih =>
    rcases term with ⟨i, w⟩
    simp [weightedXor, absent i, ih]

/-- A semantic constant-one identity implies that the input events cover
at every point. No assumption on how the identity was found. -/
theorem weighted_identity_implies_cover {X I : Type} (event : I → X → Bool)
    (terms : List (I × (X → Bool))) (identity : ∀ x, weightedXor event terms x = true) :
    ∀ x, ∃ i, event i x = true := by
  classical
  intro x
  by_cases found : ∃ i, event i x = true
  · exact found
  · have absent : ∀ i, event i x = false := by
      intro i
      cases h : event i x with
      | false => rfl
      | true => exact False.elim (found ⟨i, h⟩)
    have impossible : (false : Bool) = true :=
      (weighted_zero event x absent terms).symm.trans (identity x)
    cases impossible

end BoundaryLab.AffineCover
