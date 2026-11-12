import ProofLab.MaskedDAG
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Degree-accounted substitution for ordinary polynomial calculus

Substituting degree-at-most-D coordinates into a degree-B ordinary-PC proof
costs at most D*B, provided the images of its input axioms have derivations
at that budget. Multiplication by a substituted coordinate is expanded using
the proved completed-line multiplication theorem, not added as a new rule.

For finite Boolean original variables, definitional extensions are discharged
using the degree-accounted Boolean-vanishing theorem. Their substituted
equations must vanish on the entire Boolean cube, not merely on models of F.
The latter condition would be vacuous for an inconsistent F.

This is a degree-transfer result. It is not a proof-size simulation or a
lower bound against unrestricted extensions or general computation.
-/

set_option autoImplicit false

namespace BoundaryLab.ExtensionSubstitution
noncomputable section
open MvPolynomial MathResearch.PolynomialCalculus
open scoped BigOperators

variable {K V W : Type} [Field K]

theorem substitution_degree (g : V → Poly K W) (D : ℕ)
    (hg : ∀ v, (g v).totalDegree ≤ D) (p : Poly K V) :
    (aeval g p).totalDegree ≤ D * p.totalDegree := by
  classical
  change (eval₂ C g p).totalDegree ≤ D * p.totalDegree
  rw [eval₂_eq]
  apply totalDegree_finsetSum_le
  intro d hd
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add]
  apply (totalDegree_finsetProd _ _).trans
  calc
    (∑ v ∈ d.support, (g v ^ d v).totalDegree) ≤ ∑ v ∈ d.support, D * d v := by
      apply Finset.sum_le_sum
      intro v _
      exact (totalDegree_pow (g v) (d v)).trans
        (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left (d v) (hg v))
    _ = D * d.sum (fun _ n => n) := by
      change (∑ v ∈ d.support, D * d v) = D * ∑ v ∈ d.support, d v
      rw [Finset.mul_sum]
    _ ≤ D * p.totalDegree := Nat.mul_le_mul_left D (le_totalDegree hd)

theorem derives_substitution {F : Set (Poly K V)} {G : Set (Poly K W)}
    (g : V → Poly K W) (D B : ℕ) (hg : ∀ v, (g v).totalDegree ≤ D)
    (hinputs : ∀ p ∈ F, p.totalDegree ≤ B → Derives G (D * B) (aeval g p))
    {p : Poly K V} (hp : Derives F B p) :
    Derives G (D * B) (aeval g p) := by
  induction hp with
  | zero => simpa using (Derives.zero : Derives G (D * B) 0)
  | hyp hf hd => exact hinputs _ hf hd
  | add _ _ ih jh => simpa using Derives.add ih jh
  | smul a _ ih => simpa using Derives.smul a ih
  | @mul_var v f hf hd ih =>
    by_cases hz : f = 0
    · simp only [hz, mul_zero, map_zero]
      exact .zero
    have hfd : f.totalDegree + 1 ≤ B := by
      simpa [totalDegree_mul_of_isDomain (X_ne_zero v) hz, totalDegree_X,
        Nat.add_comm] using hd
    have hcost : (g v).totalDegree + (aeval g f).totalDegree ≤ D * B := by
      calc
        _ ≤ D + D * f.totalDegree :=
          Nat.add_le_add (hg v) (substitution_degree g D hg f)
        _ = D * (f.totalDegree + 1) := by ring
        _ ≤ D * B := Nat.mul_le_mul_left D hfd
    have h := (ih.mul_polynomial (g v)).mono (Set.Subset.refl _)
      (max_le le_rfl hcost)
    simpa only [map_mul, aeval_X] using h

theorem refutation_substitution {F : Set (Poly K V)} {G : Set (Poly K W)}
    (g : V → Poly K W) (D B : ℕ) (hg : ∀ v, (g v).totalDegree ≤ D)
    (hinputs : ∀ p ∈ F, p.totalDegree ≤ B → Derives G (D * B) (aeval g p))
    (h : Derives F B 1) : Derives G (D * B) 1 := by
  simpa only [map_one] using derives_substitution g D B hg hinputs h

section BinaryExtensions
variable {A Z : Type}

def coordinates (q : Z → Poly (ZMod 2) A) : A ⊕ Z → Poly (ZMod 2) A
  | .inl a => X a
  | .inr z => q z

theorem coordinates_degree (q : Z → Poly (ZMod 2) A) (D : ℕ)
    (hD : 1 ≤ D) (hq : ∀ z, (q z).totalDegree ≤ D) :
    ∀ v, (coordinates q v).totalDegree ≤ D := by
  intro v
  cases v with
  | inl a => simpa [coordinates] using hD
  | inr z => exact hq z

theorem original_substitution (q : Z → Poly (ZMod 2) A) (p : Poly (ZMod 2) A) :
    aeval (coordinates q) (rename Sum.inl p) = p := by
  rw [aeval_rename]
  change aeval X p = p
  exact aeval_X_left_apply p

def extendedBase (F : Set (Poly (ZMod 2) A))
    (E : Set (Poly (ZMod 2) (A ⊕ Z))) : Set (Poly (ZMod 2) (A ⊕ Z)) :=
  (rename Sum.inl '' F) ∪ booleanBase ∪ E

variable [Fintype A] [DecidableEq A]

/-- All-cube vanishing is an explicit condition on the definitions, not on F. -/
theorem extension_derives_transfer (F : Set (Poly (ZMod 2) A))
    (E : Set (Poly (ZMod 2) (A ⊕ Z))) (q : Z → Poly (ZMod 2) A)
    (D B : ℕ) (hD : 1 ≤ D) (hq : ∀ z, (q z).totalDegree ≤ D)
    (hbool : booleanBase ⊆ F)
    (hE : ∀ e ∈ E, ∀ x : A → ZMod 2, eval x (aeval (coordinates q) e) = 0)
    {p : Poly (ZMod 2) (A ⊕ Z)} (hp : Derives (extendedBase F E) B p) :
    Derives F (D * B) (aeval (coordinates q) p) := by
  have hg := coordinates_degree q D hD hq
  apply derives_substitution (coordinates q) D B hg ?_ hp
  intro e he hd
  have hdegree : (aeval (coordinates q) e).totalDegree ≤ D * B :=
    (substitution_degree _ D hg e).trans (Nat.mul_le_mul_left D hd)
  rcases he with (hold | hboolean) | hdefinition
  · obtain ⟨f, hf, rfl⟩ := hold
    rw [original_substitution] at hdegree ⊢
    exact .hyp hf hdegree
  · obtain ⟨v, rfl⟩ := hboolean
    apply MaskedDAG.boolean_zero_pc hbool hdegree
    intro x
    simp only [map_sub, map_pow, aeval_X]
    exact sub_eq_zero.mpr (ZMod.pow_card _)
  · exact MaskedDAG.boolean_zero_pc hbool hdegree (hE _ hdefinition)

theorem extension_refutation_transfer (F : Set (Poly (ZMod 2) A))
    (E : Set (Poly (ZMod 2) (A ⊕ Z))) (q : Z → Poly (ZMod 2) A)
    (D B : ℕ) (hD : 1 ≤ D) (hq : ∀ z, (q z).totalDegree ≤ D)
    (hbool : booleanBase ⊆ F)
    (hE : ∀ e ∈ E, ∀ x : A → ZMod 2, eval x (aeval (coordinates q) e) = 0)
    (hp : Derives (extendedBase F E) B 1) : Derives F (D * B) 1 := by
  simpa only [map_one] using extension_derives_transfer F E q D B hD hq hbool hE hp

theorem extension_lower_bound (F : Set (Poly (ZMod 2) A))
    (E : Set (Poly (ZMod 2) (A ⊕ Z))) (q : Z → Poly (ZMod 2) A)
    (D B : ℕ) (hD : 1 ≤ D) (hq : ∀ z, (q z).totalDegree ≤ D)
    (hbool : booleanBase ⊆ F)
    (hE : ∀ e ∈ E, ∀ x : A → ZMod 2, eval x (aeval (coordinates q) e) = 0)
    (hnot : ¬ Derives F (D * B) 1) : ¬ Derives (extendedBase F E) B 1 :=
  fun hp => hnot (extension_refutation_transfer F E q D B hD hq hbool hE hp)

end BinaryExtensions

/-- Concrete AND definitions with squarefree coordinate polynomials satisfy
the all-cube premise. The ordinary polynomial equation need not be zero. -/
theorem and_definition_vanishes {A Z : Type} [DecidableEq A]
    (g : Z → Poly (ZMod 2) A) (a b z : Z)
    (hz : g z = squarefreePart (g a * g b)) (x : A → ZMod 2) :
    eval x (aeval g (X z - X a * X b : Poly (ZMod 2) Z)) = 0 := by
  simp only [map_sub, map_mul, aeval_X]
  rw [hz, squarefreePart_eval, map_mul, sub_self]

theorem xor_definition_vanishes {A Z : Type}
    (g : Z → Poly (ZMod 2) A) (a b z : Z)
    (hz : g z = g a + g b) (x : A → ZMod 2) :
    eval x (aeval g (X z - (X a + X b) : Poly (ZMod 2) Z)) = 0 := by
  simp only [map_sub, map_add, aeval_X, hz, sub_self, map_zero]

theorem not_definition_vanishes {A Z : Type}
    (g : Z → Poly (ZMod 2) A) (a z : Z)
    (hz : g z = 1 - g a) (x : A → ZMod 2) :
    eval x (aeval g (X z - (1 - X a) : Poly (ZMod 2) Z)) = 0 := by
  simp only [map_sub, map_one, aeval_X, hz, sub_self, map_zero]

theorem supportMonomial_ne_zero {A : Type} (S : Finset A) :
    supportMonomial S ≠ 0 := by
  classical
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => X_ne_zero i)

theorem supportMonomial_exact_degree {A : Type} (S : Finset A) :
    (supportMonomial S).totalDegree = S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [supportMonomial]
  | @insert i S hi ih =>
    rw [supportMonomial, Finset.prod_insert hi]
    change (X i * supportMonomial S).totalDegree = (insert i S).card
    rw [totalDegree_mul_of_isDomain (X_ne_zero i) (supportMonomial_ne_zero S), totalDegree_X]
    rw [ih, Finset.card_insert_of_notMem hi]
    omega

/-- Any ordinary polynomial representing AND of S on the Boolean cube has
degree at least |S|. Replacing the coordinate polynomial cannot avoid this. -/
theorem and_representation_degree_lower_bound {A : Type} [Fintype A] [DecidableEq A]
    (S : Finset A) (p : Poly (ZMod 2) A)
    (hp : ∀ x : A → ZMod 2, eval x p = eval x (supportMonomial S)) :
    S.card ≤ p.totalDegree := by
  have hz : squarefreePart p - supportMonomial S = 0 := by
    apply MvPolynomial.eq_zero_of_eval_eq_zero A (ZMod 2)
    · intro x
      rw [map_sub, squarefreePart_eval, hp x, sub_self]
    · simpa using (restrictDegree A (ZMod 2) 1).sub_mem
        (squarefreePart_restricted p) (supportMonomial_restricted S)
  have he := sub_eq_zero.mp hz
  calc
    S.card = (supportMonomial S).totalDegree := (supportMonomial_exact_degree S).symm
    _ = (squarefreePart p).totalDegree := congrArg totalDegree he.symm
    _ ≤ p.totalDegree := squarefreePart_degree p

/-- The D-fold loss is sharp for line-by-line substitution already on a
single extension Boolean axiom. This is not a refutation lower bound. -/
theorem and_boolean_axiom_exact_degree {A : Type} (S : Finset A) (hS : S.Nonempty) :
    (supportMonomial S ^ 2 - supportMonomial S).totalDegree = 2 * S.card := by
  have hsquare : (supportMonomial S ^ 2).totalDegree = 2 * S.card := by
    rw [pow_two, totalDegree_mul_of_isDomain (supportMonomial_ne_zero S)
      (supportMonomial_ne_zero S), supportMonomial_exact_degree]
    omega
  have hpos := Finset.card_pos.mpr hS
  have hlt : (-supportMonomial S).totalDegree < (supportMonomial S ^ 2).totalDegree := by
    rw [totalDegree_neg, supportMonomial_exact_degree, hsquare]
    omega
  rw [sub_eq_add_neg, totalDegree_add_eq_left_of_totalDegree_lt hlt, hsquare]

theorem and_boolean_axiom_replay_cost {A : Type} (S : Finset A) (hS : S.Nonempty)
    (F : Set (Poly (ZMod 2) A)) (B : ℕ)
    (hp : Derives F B (supportMonomial S ^ 2 - supportMonomial S)) :
    2 * S.card ≤ B := by
  simpa only [and_boolean_axiom_exact_degree S hS] using hp.degree_le

end
end BoundaryLab.ExtensionSubstitution
