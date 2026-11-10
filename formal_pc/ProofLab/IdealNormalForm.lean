import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex
import Mathlib.Tactic.Abel

/-!
# Constructed normal forms modulo polynomial ideals

We divide by all nonzero members of an ideal. This is a classical existence
construction, not an algorithm for computing a Groebner basis. The remainder
contains only standard monomials; uniqueness then proves linearity, the exact
kernel, compatibility with ideal enlargement and multiplication, and the
monomial-order degree bound. No normal-form existence or consistency assumption
is added. This supplies the algebraic normal forms needed by the expander route.
-/

namespace BoundaryLab.IdealNormalForm

noncomputable section

open MvPolynomial
open scoped BigOperators MonomialOrder

variable {K V : Type*} [Field K]

/-- A monomial is standard when no leading monomial from the ideal divides it. -/
def Standard (m : MonomialOrder V) (I : Ideal (MvPolynomial V K)) (d : V →₀ ℕ) : Prop :=
  ∀ q ∈ I, q ≠ 0 → ¬ m.degree q ≤ d

theorem standard_of_le {m : MonomialOrder V} {I : Ideal (MvPolynomial V K)}
    {d e : V →₀ ℕ} (he : Standard m I e) (hde : d ≤ e) : Standard m I d := by
  intro q hq hne hqd
  exact he q hq hne (hqd.trans hde)

theorem standard_of_ideal_le {m : MonomialOrder V} {I J : Ideal (MvPolynomial V K)}
    (hIJ : I ≤ J) {d : V →₀ ℕ} (hd : Standard m J d) : Standard m I d := by
  intro q hq hne
  exact hd q (hIJ hq) hne

/-- The actual span of standard monomials, expressed by coefficient support. -/
def standardSpace (m : MonomialOrder V) (I : Ideal (MvPolynomial V K)) :
    Submodule K (MvPolynomial V K) where
  carrier := {p | ∀ d ∈ p.support, Standard m I d}
  zero_mem' := by simp
  add_mem' := by
    classical
    intro p q hp hq d hd
    rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with hd | hd
    · exact hp d hd
    · exact hq d hd
  smul_mem' := by
    intro a p hp d hd
    exact hp d (MvPolynomial.support_smul hd)

theorem eq_zero_of_standard_mem_ideal {m : MonomialOrder V}
    {I : Ideal (MvPolynomial V K)} {p : MvPolynomial V K}
    (hp : p ∈ standardSpace m I) (hI : p ∈ I) : p = 0 := by
  by_contra hne
  exact hp (m.degree p) (m.degree_mem_support hne) p hI hne le_rfl

theorem exists_normal_form (m : MonomialOrder V) (I : Ideal (MvPolynomial V K))
    (p : MvPolynomial V K) :
    ∃ r : MvPolynomial V K, p - r ∈ I ∧ r ∈ standardSpace m I := by
  classical
  let B : Set (MvPolynomial V K) := {q | q ∈ I ∧ q ≠ 0}
  have hB : ∀ q ∈ B, IsUnit (m.leadingCoeff q) := by
    intro q hq
    exact isUnit_iff_ne_zero.mpr (m.leadingCoeff_ne_zero_iff.mpr hq.2)
  obtain ⟨g, r, heq, _, hr⟩ := m.div_set hB p
  refine ⟨r, ?_, ?_⟩
  · rw [heq, add_sub_cancel_right, Finsupp.linearCombination_apply]
    exact I.sum_mem (fun q _ => I.smul_mem (g q) q.property.1)
  · intro d hd q hq hne
    exact hr d hd q ⟨hq, hne⟩

theorem normal_form_unique {m : MonomialOrder V} {I : Ideal (MvPolynomial V K)}
    {p r t : MvPolynomial V K}
    (hrI : p - r ∈ I) (hr : r ∈ standardSpace m I)
    (htI : p - t ∈ I) (ht : t ∈ standardSpace m I) : r = t := by
  apply sub_eq_zero.mp
  apply eq_zero_of_standard_mem_ideal ((standardSpace m I).sub_mem hr ht)
  convert I.sub_mem htI hrI using 1; abel

private def chosenRemainder (m : MonomialOrder V) (I : Ideal (MvPolynomial V K))
    (p : MvPolynomial V K) : MvPolynomial V K :=
  Classical.choose (exists_normal_form m I p)

private theorem chosenRemainder_spec (m : MonomialOrder V) (I : Ideal (MvPolynomial V K))
    (p : MvPolynomial V K) :
    p - chosenRemainder m I p ∈ I ∧ chosenRemainder m I p ∈ standardSpace m I :=
  Classical.choose_spec (exists_normal_form m I p)

/-- The normal-form operator, constructed from division and uniqueness. -/
def normalForm (m : MonomialOrder V) (I : Ideal (MvPolynomial V K)) :
    MvPolynomial V K →ₗ[K] MvPolynomial V K where
  toFun := chosenRemainder m I
  map_add' p q := by
    apply normal_form_unique (chosenRemainder_spec m I (p + q)).1
      (chosenRemainder_spec m I (p + q)).2
    · convert I.add_mem (chosenRemainder_spec m I p).1
        (chosenRemainder_spec m I q).1 using 1; abel
    · exact (standardSpace m I).add_mem (chosenRemainder_spec m I p).2
        (chosenRemainder_spec m I q).2
  map_smul' a p := by
    apply normal_form_unique (chosenRemainder_spec m I (a • p)).1
      (chosenRemainder_spec m I (a • p)).2
    · rw [RingHom.id_apply, ← smul_sub]
      exact (I.restrictScalars K).smul_mem a (chosenRemainder_spec m I p).1
    · exact (standardSpace m I).smul_mem a (chosenRemainder_spec m I p).2

theorem sub_normalForm_mem (m : MonomialOrder V) (I : Ideal (MvPolynomial V K))
    (p : MvPolynomial V K) : p - normalForm m I p ∈ I :=
  (chosenRemainder_spec m I p).1

theorem normalForm_mem_standardSpace (m : MonomialOrder V) (I : Ideal (MvPolynomial V K))
    (p : MvPolynomial V K) : normalForm m I p ∈ standardSpace m I :=
  (chosenRemainder_spec m I p).2

theorem normalForm_eq_of_spec {m : MonomialOrder V} {I : Ideal (MvPolynomial V K)}
    {p r : MvPolynomial V K} (hI : p - r ∈ I) (hr : r ∈ standardSpace m I) :
    normalForm m I p = r :=
  normal_form_unique (sub_normalForm_mem m I p) (normalForm_mem_standardSpace m I p) hI hr

theorem normalForm_eq_self {m : MonomialOrder V} {I : Ideal (MvPolynomial V K)}
    {p : MvPolynomial V K} (hp : p ∈ standardSpace m I) : normalForm m I p = p :=
  normalForm_eq_of_spec (by simp) hp

theorem normalForm_eq_zero_iff (m : MonomialOrder V) (I : Ideal (MvPolynomial V K))
    (p : MvPolynomial V K) : normalForm m I p = 0 ↔ p ∈ I := by
  constructor
  · intro hp
    simpa [hp] using sub_normalForm_mem m I p
  · intro hp
    exact normalForm_eq_of_spec (by simpa using hp) (standardSpace m I).zero_mem

theorem normalForm_idempotent (m : MonomialOrder V) (I : Ideal (MvPolynomial V K))
    (p : MvPolynomial V K) : normalForm m I (normalForm m I p) = normalForm m I p :=
  normalForm_eq_self (normalForm_mem_standardSpace m I p)

theorem normalForm_congr {m : MonomialOrder V} {I : Ideal (MvPolynomial V K)}
    {p q : MvPolynomial V K} (hpq : p - q ∈ I) : normalForm m I p = normalForm m I q := by
  apply normalForm_eq_of_spec
  · convert I.add_mem hpq (sub_normalForm_mem m I q) using 1; abel
  · exact normalForm_mem_standardSpace m I q

/-- Normalization commutes with multiplication after enlarging the ideal.
This is the normal-form compatibility used by the graph reduction. -/
theorem normalForm_mul_normalForm {m : MonomialOrder V}
    {I J : Ideal (MvPolynomial V K)} (hIJ : I ≤ J) (p q : MvPolynomial V K) :
    normalForm m J (p * normalForm m I q) = normalForm m J (p * q) := by
  apply normalForm_congr
  rw [← mul_sub]
  apply J.mul_mem_left p
  apply hIJ
  simpa only [neg_sub] using I.neg_mem (sub_normalForm_mem m I q)

/-- Even though the division set is infinite, the selected remainder cannot
increase the leading monomial. -/
theorem normalForm_degree_le (m : MonomialOrder V) (I : Ideal (MvPolynomial V K))
    (p : MvPolynomial V K) : m.degree (normalForm m I p) ≼[m] m.degree p := by
  by_contra h
  have hlt : m.degree p ≺[m] m.degree (normalForm m I p) := lt_of_not_ge h
  have hrne : normalForm m I p ≠ 0 := by
    intro hz
    simp only [hz, m.degree_zero, map_zero] at hlt
    exact (m.zero_le _).not_gt hlt
  have hdiff : normalForm m I p - p ∈ I := by
    simpa only [neg_sub] using I.neg_mem (sub_normalForm_mem m I p)
  have hd := m.degree_sub_of_lt hlt
  have hne : normalForm m I p - p ≠ 0 := by
    intro hz
    have heq := sub_eq_zero.mp hz
    rw [heq] at hlt
    exact lt_irrefl _ hlt
  have hs := normalForm_mem_standardSpace m I p
  exact hs _ (m.degree_mem_support hrne) _ hdiff hne (by rw [hd])

theorem normalForm_totalDegree_le [LinearOrder V] [WellFoundedGT V]
    (I : Ideal (MvPolynomial V K)) (p : MvPolynomial V K) :
    (normalForm MonomialOrder.degLex I p).totalDegree ≤ p.totalDegree :=
  MvPolynomial.degLex_totalDegree_monotone (normalForm_degree_le _ I p)

end

end BoundaryLab.IdealNormalForm
