import ProofLab.IdealNormalForm
import ProofLab.ExpanderLocalConsistency
import claims.BooleanReduction

/-!
# Boolean and local clause ideals with actual normal forms

Including the explicit Boolean generators forces the constructed normal form
to be multilinear. Modulo the Boolean ideal alone, it fixes every multilinear
polynomial, by evaluation and uniqueness on the binary cube. Local clause
ideals are defined from the actual signed raw clause polynomials.
-/

namespace BoundaryLab.BooleanIdealNormalForm

noncomputable section

open MvPolynomial MathResearch.PolynomialCalculus IdealNormalForm
open AffineIndicators (BinaryField)
open scoped BigOperators MonomialOrder

variable {V : Type} [DecidableEq V]

def booleanIdeal : Ideal (MvPolynomial V BinaryField) := Ideal.span booleanBase

theorem boolean_generator_degree (m : MonomialOrder V) (v : V) :
    m.degree (X v ^ 2 - X v : MvPolynomial V BinaryField) = Finsupp.single v 2 := by
  have hpow : m.degree (X v ^ 2 : MvPolynomial V BinaryField) = Finsupp.single v 2 := by
    rw [m.degree_pow, m.degree_X]
    ext w
    simp [Finsupp.single_apply]
  have hlt : m.degree (X v : MvPolynomial V BinaryField) ≺[m]
      m.degree (X v ^ 2 : MvPolynomial V BinaryField) := by
    rw [m.degree_X, hpow]
    apply m.toSyn_strictMono
    apply lt_of_le_of_ne
    · exact Finsupp.single_le_iff.mpr (by simp)
    · intro heq
      have := congrArg (fun d : V →₀ ℕ => d v) heq
      simp at this
  rw [m.degree_sub_of_lt hlt, hpow]

theorem boolean_generator_ne_zero (m : MonomialOrder V) (v : V) :
    (X v ^ 2 - X v : MvPolynomial V BinaryField) ≠ 0 := by
  intro h
  have hd := boolean_generator_degree m v
  rw [h, m.degree_zero] at hd
  have := congrArg (fun d : V →₀ ℕ => d v) hd
  simp at this

/-- The squarefree property follows from standardness and the explicit Boolean
generators. It is not an extra condition on the selected remainder. -/
theorem normalForm_multilinear (m : MonomialOrder V)
    (J : Ideal (MvPolynomial V BinaryField))
    (hbool : booleanBase ⊆ (J : Set (MvPolynomial V BinaryField)))
    (p : MvPolynomial V BinaryField) : normalForm m J p ∈ restrictDegree V BinaryField 1 := by
  apply (mem_restrictDegree V _ 1).mpr
  intro d hd v
  by_contra hn
  have htwo : 2 ≤ d v := by omega
  have hgen : (X v ^ 2 - X v : MvPolynomial V BinaryField) ∈ J :=
    hbool ⟨v, rfl⟩
  have hs := normalForm_mem_standardSpace m J p d hd
  apply hs _ hgen (boolean_generator_ne_zero m v)
  rw [boolean_generator_degree]
  exact Finsupp.single_le_iff.mpr htwo

omit [DecidableEq V] in
theorem booleanIdeal_eval_zero (x : V → BinaryField)
    {p : MvPolynomial V BinaryField} (hp : p ∈ booleanIdeal (V := V)) : eval x p = 0 := by
  have hle : booleanIdeal (V := V) ≤ RingHom.ker (eval x) := by
    apply Ideal.span_le.mpr
    rintro p ⟨v, rfl⟩
    change eval x (X v ^ 2 - X v) = 0
    simp only [map_sub, map_pow, eval_X]
    exact sub_eq_zero.mpr (ZMod.pow_card _)
  exact hle hp

omit [DecidableEq V] in
theorem normalForm_boolean_eval (m : MonomialOrder V)
    (p : MvPolynomial V BinaryField) (x : V → BinaryField) :
    eval x (normalForm m booleanIdeal p) = eval x p := by
  have hz := booleanIdeal_eval_zero x (sub_normalForm_mem m booleanIdeal p)
  rw [map_sub, sub_eq_zero] at hz
  exact hz.symm

/-- No clause axioms means genuine Boolean reduction: every squarefree
polynomial is fixed, with no unspecified choice of fixed basis. -/
theorem normalForm_boolean_eq_self [Fintype V] (m : MonomialOrder V)
    (p : MvPolynomial V BinaryField) (hp : p ∈ restrictDegree V BinaryField 1) :
    normalForm m booleanIdeal p = p := by
  apply sub_eq_zero.mp
  apply MvPolynomial.eq_zero_of_eval_eq_zero V BinaryField
  · intro x
    rw [map_sub, normalForm_boolean_eval, sub_self]
  · exact (restrictDegree V BinaryField 1).sub_mem
      (normalForm_multilinear m booleanIdeal (fun _ h => Ideal.subset_span h) p) hp

theorem normalForm_boolean_supportMonomial [Fintype V] (m : MonomialOrder V) (T : Finset V) :
    normalForm m booleanIdeal (supportMonomial T) = supportMonomial T :=
  normalForm_boolean_eq_self m _ (supportMonomial_restricted T)

variable {I : Type}

def rawClause (E : I → Finset V) (sign : I → V → Bool) (i : I) :
    MvPolynomial V BinaryField :=
  AffineIndicators.falsityPolynomial
    (AffineIndicators.cnfClause (ExpanderLocalConsistency.signedClause E sign i))

def clauseBase (E : I → Finset V) (sign : I → V → Bool) (A : Finset I) :
    Set (MvPolynomial V BinaryField) := booleanBase ∪ rawClause E sign '' (A : Set I)

def clauseIdeal (E : I → Finset V) (sign : I → V → Bool) (A : Finset I) :
    Ideal (MvPolynomial V BinaryField) := Ideal.span (clauseBase E sign A)

@[simp]
theorem clauseIdeal_empty (E : I → Finset V) (sign : I → V → Bool) :
    clauseIdeal E sign ∅ = booleanIdeal := by
  simp [clauseIdeal, clauseBase, booleanIdeal]

theorem clauseIdeal_mono (E : I → Finset V) (sign : I → V → Bool)
    {A D : Finset I} (hAD : A ⊆ D) : clauseIdeal E sign A ≤ clauseIdeal E sign D := by
  apply Ideal.span_mono
  exact Set.union_subset_union_right _ (Set.image_mono hAD)

theorem booleanBase_subset_clauseIdeal (E : I → Finset V) (sign : I → V → Bool)
    (A : Finset I) : booleanBase ⊆ (clauseIdeal E sign A : Set (MvPolynomial V BinaryField)) := by
  intro p hp
  exact Ideal.subset_span (Or.inl hp)

theorem rawClause_mem_clauseIdeal (E : I → Finset V) (sign : I → V → Bool)
    {A : Finset I} {i : I} (hi : i ∈ A) : rawClause E sign i ∈ clauseIdeal E sign A :=
  Ideal.subset_span (Or.inr ⟨i, hi, rfl⟩)

theorem clauseIdeal_eval_zero (E : I → Finset V) (sign : I → V → Bool)
    (A : Finset I) (x : V → BinaryField)
    (hx : ∀ i ∈ A, eval x (rawClause E sign i) = 0)
    {p : MvPolynomial V BinaryField} (hp : p ∈ clauseIdeal E sign A) : eval x p = 0 := by
  have hle : clauseIdeal E sign A ≤ RingHom.ker (eval x) := by
    apply Ideal.span_le.mpr
    intro p hp
    rcases hp with hb | ⟨i, hi, rfl⟩
    · exact booleanIdeal_eval_zero x (Ideal.subset_span hb)
    · exact hx i hi
  exact hle hp

theorem normalForm_clause_eval (m : MonomialOrder V) (E : I → Finset V)
    (sign : I → V → Bool) (A : Finset I) (x : V → BinaryField)
    (hx : ∀ i ∈ A, eval x (rawClause E sign i) = 0) (p : MvPolynomial V BinaryField) :
    eval x (normalForm m (clauseIdeal E sign A) p) = eval x p := by
  have hz := clauseIdeal_eval_zero E sign A x hx (sub_normalForm_mem m _ p)
  rw [map_sub, sub_eq_zero] at hz
  exact hz.symm

/-- Local consistency proves that the actual local ideal is proper, for every
signing, rather than assuming its consistency at the algebraic interface. -/
theorem clauseIdeal_ne_top_of_expansion [Fintype I] [Fintype V] [DecidableEq I]
    {E : I → Finset V} {s : ℕ}
    (hexp : ExpanderSupport.HalfBoundaryExpander E s) (sign : I → V → Bool)
    (A : Finset I) (hA : A.card ≤ s) : clauseIdeal E sign A ≠ ⊤ := by
  obtain ⟨x, hx⟩ := ExpanderLocalConsistency.exists_clause_polynomial_zeroes hexp sign A hA
  intro htop
  have hone : (1 : MvPolynomial V BinaryField) ∈ clauseIdeal E sign A := by rw [htop]; trivial
  have hz := clauseIdeal_eval_zero E sign A x hx hone
  exact one_ne_zero (by simpa only [map_one] using hz)

end

end BoundaryLab.BooleanIdealNormalForm
