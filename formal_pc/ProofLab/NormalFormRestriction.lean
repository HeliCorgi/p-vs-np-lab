import ProofLab.IdealNormalForm
import Mathlib.Algebra.MvPolynomial.Variables

/-!
# One-variable restrictions preserve standard monomials

Replacing one variable by a field constant erases that coordinate from each
monomial. Standardness is downward closed under divisibility, so restriction
preserves it. This gives a proved normal-form comparison for a restriction
that maps a larger ideal into a smaller one while fixing the input polynomial.
-/

namespace BoundaryLab.NormalFormRestriction

noncomputable section

open MvPolynomial IdealNormalForm
open scoped BigOperators MonomialOrder

variable {K V : Type*} [Field K] [DecidableEq V]

def pin (v : V) (a : K) : MvPolynomial V K →ₐ[K] MvPolynomial V K :=
  aeval (fun w => if w = v then C a else X w)

@[simp]
theorem pin_X (v w : V) (a : K) : pin v a (X w) = if w = v then C a else X w := by
  simp [pin]

@[simp]
theorem pin_C (v : V) (a b : K) : pin v a (C b) = C b := by
  simp [pin]

theorem pin_monomial (v : V) (a c : K) (d : V →₀ ℕ) :
    pin v a (monomial d c) = monomial (d.erase v) (c * a ^ d v) := by
  classical
  change eval₂ C (fun w => if w = v then C a else X w) (monomial d c) = _
  rw [eval₂_monomial, monomial_eq]
  rw [← Finsupp.mul_prod_erase' d v
    (fun w e => (if w = v then C a else X w : MvPolynomial V K) ^ e) (by simp)]
  have hprod : (d.erase v).prod
      (fun w e => (if w = v then C a else X w : MvPolynomial V K) ^ e) =
      (d.erase v).prod (fun w e => (X w : MvPolynomial V K) ^ e) := by
    apply Finsupp.prod_congr
    intro w hw
    have hwv : w ≠ v := by
      intro h
      subst w
      simp at hw
    simp only [ite_eq_right hwv]
  rw [hprod]
  simp only [ite_true, map_mul, map_pow, mul_assoc]

theorem pin_standard (m : MonomialOrder V) (J : Ideal (MvPolynomial V K))
    (v : V) (a : K) {p : MvPolynomial V K} (hp : p ∈ standardSpace m J) :
    pin v a p ∈ standardSpace m J := by
  classical
  rw [p.as_sum, map_sum]
  apply Submodule.sum_mem
  intro d hd
  rw [pin_monomial]
  intro e he
  have heq := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset he)
  subst e
  apply standard_of_le (hp d hd)
  intro w
  by_cases hw : w = v
  · subst w
    simp
  · simp [Finsupp.erase_ne hw]

theorem notMem_vars_pin (v : V) (a : K) (p : MvPolynomial V K) :
    v ∉ (pin v a p).vars := by
  classical
  intro hv
  obtain ⟨e, he, hv⟩ := (mem_vars_iff_mem_support v).mp hv
  have he' : e ∈ (∑ d ∈ p.support, pin v a (monomial d (p.coeff d))).support := by
    simpa only [← map_sum, ← p.as_sum] using he
  obtain ⟨d, hd, he⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum he')
  rw [pin_monomial] at he
  have heq := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset he)
  subst e
  simp at hv

theorem pin_eq_self_of_notMem_vars (v : V) (a : K) {p : MvPolynomial V K}
    (hv : v ∉ p.vars) : pin v a p = p := by
  calc
    pin v a p = aeval (X : V → MvPolynomial V K) p := by
      apply eval₂Hom_congr' rfl ?_ rfl
      intro w hw _
      have hwv : w ≠ v := by intro h; subst w; exact hv hw
      simp [hwv]
    _ = p := aeval_X_left_apply p

/-- Enlarging an ideal does not change the normal form of an input fixed by
a restriction that eliminates the added generators. All maps are explicit. -/
theorem normalForm_eq_of_pin (m : MonomialOrder V)
    (J L : Ideal (MvPolynomial V K)) (hLJ : L ≤ J) (v : V) (a : K)
    (hmap : ∀ q ∈ J, pin v a q ∈ L) (p : MvPolynomial V K) (hp : pin v a p = p) :
    normalForm m J p = normalForm m L p ∧
      pin v a (normalForm m J p) = normalForm m J p := by
  have hdiff : p - pin v a (normalForm m J p) ∈ L := by
    simpa only [map_sub, hp] using hmap _ (sub_normalForm_mem m J p)
  have hstd := pin_standard m J v a (normalForm_mem_standardSpace m J p)
  have heq : normalForm m J p = pin v a (normalForm m J p) :=
    normalForm_eq_of_spec (hLJ hdiff) hstd
  have hstdL : pin v a (normalForm m J p) ∈ standardSpace m L := by
    intro d hd
    exact standard_of_ideal_le hLJ (hstd d hd)
  have heqL := normalForm_eq_of_spec hdiff hstdL
  exact ⟨heq.trans heqL.symm, heq.symm⟩

/-- If a restriction preserves the ideal and input, no new occurrence of its
pinned variable can appear in the normal form. -/
theorem notMem_vars_normalForm_of_pin (m : MonomialOrder V)
    (J : Ideal (MvPolynomial V K)) (v : V) (a : K)
    (hmap : ∀ q ∈ J, pin v a q ∈ J) (p : MvPolynomial V K) (hp : pin v a p = p) :
    v ∉ (normalForm m J p).vars := by
  have heq := (normalForm_eq_of_pin m J J le_rfl v a hmap p hp).2
  rw [← heq]
  exact notMem_vars_pin v a _

end

end BoundaryLab.NormalFormRestriction
