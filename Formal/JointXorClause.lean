import Formal.ExactlyOneParity

/-!
# Clauses implied jointly by an XOR row and binary clauses

For each occurrence in an XOR row, choose a binary clause consisting of a
signed pivot literal on that variable and a partner literal. If every partner
were false, the binary clauses would force every pivot literal true. When the
resulting variable parity disagrees with the row, some partner must be true.

Partners may be signed, may repeat, and may share variables with the pivots.
The same binary clause may provide more than one premise. No freshness or
independence hypothesis is needed for the implication proved below.

These semantic theorems allow arbitrary list length. The Python implementation
searches only original rows of width at most THREE, in one pass over original
binary CNF clauses; this restriction makes discovery polynomial. These
theorems do not verify that discovery implementation, its JSON checker, input
normalization, Gaussian elimination, or its running-time bound.
-/

set_option autoImplicit false

namespace BoundaryLab.JointXorClause

open BoundaryLab.ExactlyOneParity

structure Premise (V : Type) where
  pivot : Literal V
  partner : Literal V

/-- The variable value forced by a true signed pivot literal. -/
def forcedValue {V : Type} (literal : Literal V) : Bool :=
  Bool.xor true literal.negative

def BinaryPremises {V : Type} (assignment : V → Bool)
    (premises : List (Premise V)) : Prop :=
  ∀ premise ∈ premises,
    eval assignment premise.pivot = true ∨ eval assignment premise.partner = true

def RowHolds {V : Type} (assignment : V → Bool)
    (premises : List (Premise V)) (rhs : Bool) : Prop :=
  parity (premises.map (fun p => assignment p.pivot.var)) = rhs

def ForcedParity {V : Type} (premises : List (Premise V)) : Bool :=
  parity (premises.map (fun p => forcedValue p.pivot))

def PartnerClause {V : Type} (assignment : V → Bool)
    (premises : List (Premise V)) : Prop :=
  true ∈ premises.map (fun p => eval assignment p.partner)

private theorem xor_eq_true_iff (a b : Bool) :
    Bool.xor a b = true ↔ a = Bool.xor true b := by
  cases a <;> cases b <;> decide

private theorem values_eq_forced_of_no_partner
    {V : Type} (assignment : V → Bool) :
    ∀ premises : List (Premise V),
      BinaryPremises assignment premises →
      (∀ premise ∈ premises, eval assignment premise.partner ≠ true) →
      premises.map (fun p => assignment p.pivot.var) =
        premises.map (fun p => forcedValue p.pivot) := by
  intro premises
  induction premises with
  | nil =>
      intro _ _
      rfl
  | cons premise premises ih =>
      intro hb hn
      have hp : eval assignment premise.pivot = true :=
        (hb premise (by simp)).resolve_right (hn premise (by simp))
      have hv : assignment premise.pivot.var = forcedValue premise.pivot :=
        (xor_eq_true_iff (assignment premise.pivot.var) premise.pivot.negative).mp hp
      have hbt : BinaryPremises assignment premises := by
        intro p hm
        exact hb p (by simp [hm])
      have hnt : ∀ p ∈ premises, eval assignment p.partner ≠ true := by
        intro p hm
        exact hn p (by simp [hm])
      simp only [List.map_cons]
      rw [hv, ih hbt hnt]

/-- A parity conflict under false partners proves their disjunction. -/
theorem joint_clause_of_forced_parity_conflict
    {V : Type} (assignment : V → Bool) (premises : List (Premise V))
    (rhs : Bool)
    (binary : BinaryPremises assignment premises)
    (row : RowHolds assignment premises rhs)
    (conflict : ForcedParity premises ≠ rhs) :
    PartnerClause assignment premises := by
  by_cases hc : true ∈ premises.map (fun p => eval assignment p.partner)
  · exact hc
  · have hn : ∀ p ∈ premises, eval assignment p.partner ≠ true := by
      intro p hm hp
      exact hc (List.mem_map.mpr ⟨p, hm, hp⟩)
    have hm := values_eq_forced_of_no_partner assignment premises binary hn
    have hp := congrArg parity hm
    exact False.elim (conflict (hp.symm.trans row))

/-- Retaining the original formula and adding justified clauses preserves models. -/
theorem strengthen_preserves_models
    {V I : Type} (original : (V → Bool) → Prop)
    (blocks : I → List (Premise V)) (rightSides : I → Bool)
    (binary : ∀ assignment, original assignment → ∀ i,
      BinaryPremises assignment (blocks i))
    (rows : ∀ assignment, original assignment → ∀ i,
      RowHolds assignment (blocks i) (rightSides i))
    (conflicts : ∀ i, ForcedParity (blocks i) ≠ rightSides i)
    (assignment : V → Bool) :
    original assignment ↔
      original assignment ∧ ∀ i, PartnerClause assignment (blocks i) := by
  constructor
  · intro ho
    refine ⟨ho, ?_⟩
    intro i
    exact joint_clause_of_forced_parity_conflict assignment (blocks i)
      (rightSides i) (binary assignment ho i) (rows assignment ho i) (conflicts i)
  · intro ho
    exact ho.1

/-- Consequently, the justified strengthening preserves satisfiability. -/
theorem strengthen_preserves_sat
    {V I : Type} (original : (V → Bool) → Prop)
    (blocks : I → List (Premise V)) (rightSides : I → Bool)
    (binary : ∀ assignment, original assignment → ∀ i,
      BinaryPremises assignment (blocks i))
    (rows : ∀ assignment, original assignment → ∀ i,
      RowHolds assignment (blocks i) (rightSides i))
    (conflicts : ∀ i, ForcedParity (blocks i) ≠ rightSides i) :
    (∃ assignment, original assignment) ↔
      ∃ assignment,
        original assignment ∧ ∀ i, PartnerClause assignment (blocks i) := by
  constructor
  · intro ho
    obtain ⟨assignment, ha⟩ := ho
    exact ⟨assignment,
      (strengthen_preserves_models original blocks rightSides
        binary rows conflicts assignment).mp ha⟩
  · intro ho
    obtain ⟨assignment, ha, _⟩ := ho
    exact ⟨assignment, ha⟩

#print axioms joint_clause_of_forced_parity_conflict
#print axioms strengthen_preserves_models
#print axioms strengthen_preserves_sat

end BoundaryLab.JointXorClause
