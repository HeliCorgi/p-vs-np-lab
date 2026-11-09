import ProofLab.BooleanIdealNormalForm
import ProofLab.NormalFormRestriction

/-!
# Consistency of local normal forms under support enlargement

Private-variable elimination is applied to the actual clause ideals and actual
normal forms. It proves that enlarging a pooled support to any at-most-s clause
set does not alter reduction of a polynomial on the supported variables.
The neighborhood bound on normal-form variables is also derived, not assumed.
-/

namespace BoundaryLab.ExpanderNormalForm

noncomputable section

open MvPolynomial MathResearch.PolynomialCalculus ExpanderSupport
open IdealNormalForm BooleanIdealNormalForm NormalFormRestriction
open AffineIndicators (BinaryField)
open scoped BigOperators

variable {I V : Type} [DecidableEq V]

theorem rawClause_eq_prod (E : I → Finset V) (sign : I → V → Bool) (i : I) :
    rawClause E sign i =
      ∏ v ∈ E i, (if sign i v then 1 - X v else X v : MvPolynomial V BinaryField) := by
  classical
  unfold rawClause
  rw [AffineIndicators.cnfClause_falsityPolynomial]
  unfold ExpanderLocalConsistency.signedClause
  rw [Finset.prod_image]
  intro a _ b _ hab
  exact congrArg Prod.fst hab

def signValue (b : Bool) : BinaryField := if b then 1 else 0

theorem pin_rawClause_satisfied (E : I → Finset V) (sign : I → V → Bool)
    (i : I) (v : V) (hv : v ∈ E i) :
    pin v (signValue (sign i v)) (rawClause E sign i) = 0 := by
  rw [rawClause_eq_prod, map_prod]
  apply Finset.prod_eq_zero hv
  cases sign i v <;> simp [signValue]

theorem pin_rawClause_of_absent (E : I → Finset V) (sign : I → V → Bool)
    (i : I) (v : V) (a : BinaryField) (hv : v ∉ E i) :
    pin v a (rawClause E sign i) = rawClause E sign i := by
  rw [rawClause_eq_prod, map_prod]
  apply Finset.prod_congr rfl
  intro w hw
  have hwv : w ≠ v := by intro h; subst w; exact hv hw
  cases sign i w <;> simp [hwv]

/-- It suffices to map the raw clauses: Boolean generators are discharged for
every binary pinned value. -/
theorem pin_clauseIdeal_of_raw (E : I → Finset V) (sign : I → V → Bool)
    (A D : Finset I) (v : V) (a : BinaryField)
    (hraw : ∀ i ∈ A, pin v a (rawClause E sign i) ∈ clauseIdeal E sign D) :
    ∀ q ∈ clauseIdeal E sign A, pin v a q ∈ clauseIdeal E sign D := by
  have hle : clauseIdeal E sign A ≤ Ideal.comap (pin v a).toRingHom (clauseIdeal E sign D) := by
    apply Ideal.span_le.mpr
    intro q hq
    rcases hq with ⟨w, rfl⟩ | ⟨i, hi, rfl⟩
    · change pin v a (X w ^ 2 - X w) ∈ clauseIdeal E sign D
      by_cases hwv : w = v
      · subst w
        have hconst : (C a : MvPolynomial V BinaryField) ^ 2 - C a = 0 := by
          rw [← map_pow, ← map_sub, sub_eq_zero.mpr (ZMod.pow_card a), map_zero]
        simpa only [map_sub, map_pow, pin_X, ite_true, hconst] using
          (clauseIdeal E sign D).zero_mem
      · rw [map_sub, map_pow, pin_X, ite_eq_right hwv]
        exact booleanBase_subset_clauseIdeal E sign D ⟨w, rfl⟩
    · exact hraw i hi
  exact fun q hq => hle hq

theorem pin_clauseIdeal_of_absent (E : I → Finset V) (sign : I → V → Bool)
    (A : Finset I) (v : V) (a : BinaryField)
    (hv : ∀ i ∈ A, v ∉ E i) :
    ∀ q ∈ clauseIdeal E sign A, pin v a q ∈ clauseIdeal E sign A := by
  apply pin_clauseIdeal_of_raw
  intro i hi
  rw [pin_rawClause_of_absent E sign i v a (hv i hi)]
  exact rawClause_mem_clauseIdeal E sign hi

theorem pin_clauseIdeal_remove_private [DecidableEq I]
    (E : I → Finset V) (sign : I → V → Bool)
    (A : Finset I) (i : I) (v : V) (hvi : v ∈ E i)
    (hprivate : ∀ j ∈ A, v ∈ E j → j = i) :
    ∀ q ∈ clauseIdeal E sign A,
      pin v (signValue (sign i v)) q ∈ clauseIdeal E sign (A.erase i) := by
  apply pin_clauseIdeal_of_raw
  intro j hj
  by_cases hji : j = i
  · subst j
    rw [pin_rawClause_satisfied E sign i v hvi]
    exact (clauseIdeal E sign (A.erase i)).zero_mem
  · have hvj : v ∉ E j := fun hv => hji (hprivate j hj hv)
    rw [pin_rawClause_of_absent E sign j v _ hvj]
    exact rawClause_mem_clauseIdeal E sign (Finset.mem_erase.mpr ⟨hji, hj⟩)

/-- A normal form cannot introduce variables outside the clause neighborhood
and the variables of the input. No expansion hypothesis is needed here. -/
theorem normalForm_vars_subset (m : MonomialOrder V) (E : I → Finset V)
    (sign : I → V → Bool) (A : Finset I) (p : MvPolynomial V BinaryField) :
    (normalForm m (clauseIdeal E sign A) p).vars ⊆ A.biUnion E ∪ p.vars := by
  intro v hv
  by_contra hout
  have hnot : v ∉ A.biUnion E ∧ v ∉ p.vars := by
    simpa only [Finset.mem_union, not_or] using hout
  have hclauses : ∀ i ∈ A, v ∉ E i := by
    intro i hi hvi
    exact hnot.1 (Finset.mem_biUnion.mpr ⟨i, hi, hvi⟩)
  exact notMem_vars_normalForm_of_pin m (clauseIdeal E sign A) v 0
    (pin_clauseIdeal_of_absent E sign A v 0 hclauses) p
    (pin_eq_self_of_notMem_vars v 0 hnot.2) hv

variable [Fintype I] [Fintype V] [DecidableEq I]

/-- A proper enlargement of the pooled support has a private variable outside
the target variables, belonging to a clause outside the pooled support. -/
theorem exists_private_outside_support (E : I → Finset V) (s : ℕ) (T : Finset V)
    (A : Finset I) (hSA : support E s T ⊆ A) (hA : A.card ≤ s)
    (hne : A ≠ support E s T) :
    ∃ i ∈ A, i ∉ support E s T ∧ ∃ v ∈ E i, v ∉ T ∧
      ∀ j ∈ A, v ∈ E j → j = i := by
  have hb : ¬ boundary E A ⊆ T := by
    intro hb
    exact hne (Finset.Subset.antisymm (subset_support E hA hb) hSA)
  obtain ⟨v, hv, hvT⟩ := Finset.not_subset.mp hb
  obtain ⟨i, hi, hvi, huniq⟩ := (mem_boundary E A v).mp hv
  refine ⟨i, hi, ?_, v, hvi, hvT, huniq⟩
  intro hiS
  apply hvT
  apply boundary_support_subset E s T
  exact (mem_boundary E _ v).mpr
    ⟨i, hiS, hvi, fun j hj hvj => huniq j (hSA hj) hvj⟩

/-- Actual normal-form consistency under enlargement of the pooled support.
This is the algebraic content of the support-enlargement lemma, with no
unproved normal-form or ideal-compatibility hypothesis remaining. -/
theorem normalForm_support_enlarge (m : MonomialOrder V) (E : I → Finset V)
    (sign : I → V → Bool) (s : ℕ) (T : Finset V) (p : MvPolynomial V BinaryField)
    (hp : p.vars ⊆ T) (A : Finset I) :
    support E s T ⊆ A → A.card ≤ s →
      normalForm m (clauseIdeal E sign A) p =
        normalForm m (clauseIdeal E sign (support E s T)) p := by
  induction A using Finset.strongInductionOn with
  | _ A ih =>
    intro hSA hA
    by_cases heq : A = support E s T
    · rw [heq]
    obtain ⟨i, hi, hiS, v, hvi, hvT, huniq⟩ :=
      exists_private_outside_support E s T A hSA hA heq
    have hSD : support E s T ⊆ A.erase i := by
      intro j hj
      exact Finset.mem_erase.mpr ⟨by intro h; subst j; exact hiS hj, hSA hj⟩
    have hvp : v ∉ p.vars := fun hv => hvT (hp hv)
    have hstep := (normalForm_eq_of_pin m (clauseIdeal E sign A)
      (clauseIdeal E sign (A.erase i))
      (clauseIdeal_mono E sign (Finset.erase_subset i A)) v (signValue (sign i v))
      (pin_clauseIdeal_remove_private E sign A i v hvi huniq) p
      (pin_eq_self_of_notMem_vars v _ hvp)).1
    exact hstep.trans (ih (A.erase i) (Finset.erase_ssubset hi) hSD
      ((Finset.card_le_card (Finset.erase_subset i A)).trans hA))

end

end BoundaryLab.ExpanderNormalForm
