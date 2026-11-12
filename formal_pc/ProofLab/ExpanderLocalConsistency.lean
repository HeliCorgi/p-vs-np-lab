import ProofLab.ExpanderSupport
import ProofLab.AffineIndicators

/-!
# Local consistency of every signing of expanding clause supports

A private variable lets us satisfy one clause after satisfying the other
clauses. This proves actual local satisfying assignments for every signing,
and transfers them to the existing ordinary clause-polynomial encoding.
No polynomial-calculus separator or global UNSAT signing is postulated here.
-/

namespace BoundaryLab.ExpanderLocalConsistency

noncomputable section

open ExpanderSupport AffineIndicators MvPolynomial

variable {I V : Type} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]

/-- One polarity for each variable on each clause support. -/
def signedClause (E : I → Finset V) (sign : I → V → Bool) (i : I) : Finset (V × Bool) :=
  (E i).image (fun v => (v, sign i v))

omit [Fintype I] [Fintype V] [DecidableEq I] in
theorem signedClause_card (E : I → Finset V) (sign : I → V → Bool) (i : I) :
    (signedClause E sign i).card = (E i).card := by
  apply Finset.card_image_of_injective
  intro v w h
  exact congrArg Prod.fst h

/-- Private-variable peeling produces an assignment, for all literal signings. -/
theorem exists_assignment_of_private_boundary (E : I → Finset V)
    (sign : I → V → Bool) (A : Finset I) :
    (∀ D ⊆ A, D.Nonempty → (boundary E D).Nonempty) →
      ∃ x : V → Bool, ∀ i ∈ A, ∃ v ∈ E i, x v = sign i v := by
  induction A using Finset.strongInductionOn with
  | _ A ih =>
    intro hprivate
    rcases A.eq_empty_or_nonempty with hA | hA
    · subst A
      exact ⟨fun _ => false, by simp⟩
    obtain ⟨v, hv⟩ := hprivate A (by rfl) hA
    obtain ⟨i, hi, hvi, huniq⟩ := (mem_boundary E A v).mp hv
    have hless : A.erase i ⊂ A := Finset.erase_ssubset hi
    obtain ⟨x, hx⟩ := ih (A.erase i) hless
      (fun D hD hne => hprivate D (hD.trans (Finset.erase_subset _ _)) hne)
    refine ⟨Function.update x v (sign i v), ?_⟩
    intro j hj
    by_cases hji : j = i
    · subst j
      exact ⟨v, hvi, Function.update_self _ _ _⟩
    obtain ⟨w, hw, hxw⟩ := hx j (Finset.mem_erase.mpr ⟨hji, hj⟩)
    have hwv : w ≠ v := by
      intro heq
      subst w
      exact hji (huniq j hj hw)
    refine ⟨w, hw, ?_⟩
    simpa [Function.update_of_ne hwv] using hxw

/-- Every subformula within the expansion range is satisfiable, for every
signing. This is stronger than merely checking some chosen local subformulas. -/
theorem exists_assignment_of_expansion {E : I → Finset V} {s : ℕ}
    (hexp : HalfBoundaryExpander E s) (sign : I → V → Bool)
    (A : Finset I) (hA : A.card ≤ s) :
    ∃ x : V → Bool, ∀ i ∈ A, ∃ v ∈ E i, x v = sign i v := by
  apply exists_assignment_of_private_boundary E sign A
  intro D hD hne
  have hdpos := Finset.card_pos.mpr hne
  have hex := hexp D hne ((Finset.card_le_card hD).trans hA)
  apply Finset.card_pos.mp
  omega

omit [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V] in
theorem literalForm_mem_cnfClause (L : Finset (V × Bool)) (l : V × Bool) (hl : l ∈ L) :
    literalForm l ∈ cnfClause L := by
  classical
  exact Finset.mem_image.mpr ⟨l, hl, rfl⟩

/-- The local witnesses satisfy the actual raw ordinary-polynomial axioms in
the affine-clause foundation; no change of variable or free quotient is used. -/
theorem exists_clause_polynomial_zeroes {E : I → Finset V} {s : ℕ}
    (hexp : HalfBoundaryExpander E s) (sign : I → V → Bool)
    (A : Finset I) (hA : A.card ≤ s) :
    ∃ x : V → BinaryField, ∀ i ∈ A,
      eval x (falsityPolynomial (cnfClause (signedClause E sign i))) = 0 := by
  classical
  obtain ⟨x, hx⟩ := exists_assignment_of_expansion hexp sign A hA
  let y : V → BinaryField := fun v => if x v then 1 else 0
  refine ⟨y, ?_⟩
  intro i hi
  obtain ⟨v, hv, hxv⟩ := hx i hi
  have hL := Finset.mem_image_of_mem (fun w => (w, sign i w)) hv
  have hC := literalForm_mem_cnfClause (signedClause E sign i) (v, sign i v) hL
  apply (eval_falsityPolynomial_eq_zero (cnfClause (signedClause E sign i)) y).mpr
  refine ⟨literalForm (v, sign i v), hC, ?_⟩
  cases hb : sign i v <;> simp [literalForm, y, hxv, hb]

end

end BoundaryLab.ExpanderLocalConsistency
