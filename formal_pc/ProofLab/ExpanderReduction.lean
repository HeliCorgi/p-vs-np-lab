import ProofLab.ExpanderNormalForm
import ProofLab.ExpanderMonomials

/-!
# The actual graph-reduction operator

On an ordinary monomial, reduce modulo the ideal of its actual pooled support;
extend by the ordinary monomial basis. The local normal forms are constructed
and their support-enlargement consistency is proved in the imported modules.
No operator existence, input annihilation, or separation is postulated.

This formalizes the support-based reduction method of Mikša–Nordström,
"A Generalized Method for Proving Polynomial Calculus Degree Lower Bounds"
(JACM 71(6), 2024), for the clause incidence structure used in this lab.
Normal forms are built in the ordinary polynomial ring with Boolean generators.
This is classical proof infrastructure, not an efficient SAT algorithm or a
claim that the underlying reduction method is new.
-/

namespace BoundaryLab.ExpanderReduction

noncomputable section

open MvPolynomial MathResearch.PolynomialCalculus ExpanderSupport
open IdealNormalForm BooleanIdealNormalForm ExpanderNormalForm ExpanderMonomials
open AffineIndicators (BinaryField)
open scoped BigOperators

variable {I V : Type} [Fintype I] [DecidableEq I] [Fintype V] [LinearOrder V]

def termReduction (E : I → Finset V) (sign : I → V → Bool) (s : ℕ) (d : V →₀ ℕ) :
    MvPolynomial V BinaryField :=
  normalForm MonomialOrder.degLex (clauseIdeal E sign (support E s d.support)) (monomial d 1)

def reduction (E : I → Finset V) (sign : I → V → Bool) (s : ℕ) :
    MvPolynomial V BinaryField →ₗ[BinaryField] MvPolynomial V BinaryField :=
  (basisMonomials V BinaryField).constr BinaryField (termReduction E sign s)

theorem reduction_monomial_one (E : I → Finset V) (sign : I → V → Bool)
    (s : ℕ) (d : V →₀ ℕ) : reduction E sign s (monomial d 1) = termReduction E sign s d :=
  (basisMonomials V BinaryField).constr_basis BinaryField (termReduction E sign s) d

theorem reduction_monomial (E : I → Finset V) (sign : I → V → Bool)
    (s : ℕ) (d : V →₀ ℕ) (a : BinaryField) :
    reduction E sign s (monomial d a) =
      normalForm MonomialOrder.degLex (clauseIdeal E sign (support E s d.support)) (monomial d a) := by
  have hm : monomial d a = a • (monomial d 1 : MvPolynomial V BinaryField) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hm, map_smul, map_smul, reduction_monomial_one]
  rfl

omit [Fintype V] [LinearOrder V] in
theorem support_card_le_degree (d : V →₀ ℕ) : d.support.card ≤ d.degree := by
  classical
  change d.support.card ≤ ∑ v ∈ d.support, d v
  calc
    d.support.card = ∑ _v ∈ d.support, 1 := by simp
    _ ≤ _ := Finset.sum_le_sum (fun v hv => Nat.one_le_iff_ne_zero.mpr
      (Finsupp.mem_support_iff.mp hv))

theorem termReduction_degree (E : I → Finset V) (sign : I → V → Bool)
    (s : ℕ) (d : V →₀ ℕ) : (termReduction E sign s d).totalDegree ≤ d.degree := by
  exact (normalForm_totalDegree_le _ (monomial d 1)).trans
    (totalDegree_monomial_le d (1 : BinaryField))

theorem reduction_degree (E : I → Finset V) (sign : I → V → Bool)
    (s : ℕ) (p : MvPolynomial V BinaryField) :
    (reduction E sign s p).totalDegree ≤ p.totalDegree := by
  have heq : reduction E sign s p =
      ∑ d ∈ p.support, p.coeff d • termReduction E sign s d := by
    conv_lhs => rw [p.as_sum, map_sum]
    apply Finset.sum_congr rfl
    intro d _
    have hm : monomial d (p.coeff d) = p.coeff d • (monomial d 1 : MvPolynomial V BinaryField) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hm, map_smul, reduction_monomial_one]
  rw [heq]
  apply totalDegree_finsetSum_le
  intro d hd
  exact (totalDegree_smul_le _ _).trans ((termReduction_degree E sign s d).trans
    (le_totalDegree hd))

theorem reduction_fixes_good_monomial (E : I → Finset V) (sign : I → V → Bool)
    (s : ℕ) (T : Finset V) (hT : support E s T = ∅) :
    reduction E sign s (supportMonomial T) = supportMonomial T := by
  rw [supportMonomial_eq_monomial, reduction_monomial]
  rw [supportExponent_support, hT, clauseIdeal_empty, ← supportMonomial_eq_monomial]
  exact normalForm_boolean_supportMonomial _ T

theorem reduction_fixes_goodSpace (E : I → Finset V) (sign : I → V → Bool)
    (s k : ℕ) {p : MvPolynomial V BinaryField} (hp : p ∈ goodSpace E s k) :
    reduction E sign s p = p := by
  have hfix : goodSpace E s k ≤ LinearMap.ker (reduction E sign s - LinearMap.id) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨T, rfl⟩
    change reduction E sign s (supportMonomial T.val) - supportMonomial T.val = 0
    exact sub_eq_zero.mpr (reduction_fixes_good_monomial E sign s T.val
      ((mem_goodSupports E s k T.val).mp T.property).2)
  exact sub_eq_zero.mp (hfix hp)

/-- If one small clause set contains the pooled support of every term, the
graph operator agrees with ordinary normalization modulo that clause set. -/
theorem reduction_eq_normalForm_of_cover (E : I → Finset V) (sign : I → V → Bool)
    (s : ℕ) (A : Finset I) (hA : A.card ≤ s) (p : MvPolynomial V BinaryField)
    (hcover : ∀ d ∈ p.support, support E s d.support ⊆ A) :
    reduction E sign s p = normalForm MonomialOrder.degLex (clauseIdeal E sign A) p := by
  conv_lhs => rw [p.as_sum, map_sum]
  conv_rhs => rw [p.as_sum, map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [reduction_monomial]
  apply (normalForm_support_enlarge _ E sign s d.support (monomial d (p.coeff d))
    ?_ A (hcover d hd) hA).symm
  rw [vars_monomial (mem_support_iff.mp hd)]

theorem reduction_boolean_generator (E : I → Finset V) (sign : I → V → Bool)
    (s : ℕ) (v : V) : reduction E sign s (X v ^ 2 - X v) = 0 := by
  rw [map_sub, X_pow_eq_monomial]
  change reduction E sign s (monomial (Finsupp.single v 2) 1) -
    reduction E sign s (monomial (Finsupp.single v 1) 1) = 0
  rw [reduction_monomial, reduction_monomial]
  simp only [Finsupp.support_single v (by decide : (2 : ℕ) ≠ 0),
    Finsupp.support_single v (by decide : (1 : ℕ) ≠ 0)]
  apply sub_eq_zero.mpr
  apply normalForm_congr
  apply booleanBase_subset_clauseIdeal E sign _
  refine ⟨v, ?_⟩
  change monomial (Finsupp.single v 2) 1 - X v = X v ^ 2 - X v
  rw [X_pow_eq_monomial]

omit [Fintype I] [DecidableEq I] [Fintype V] in
theorem rawClause_vars_subset (E : I → Finset V) (sign : I → V → Bool) (i : I) :
    (rawClause E sign i).vars ⊆ E i := by
  rw [rawClause_eq_prod]
  apply (vars_prod _).trans
  intro v hv
  obtain ⟨w, hw, hvw⟩ := Finset.mem_biUnion.mp hv
  have hvars : (if sign i w then 1 - X w else X w : MvPolynomial V BinaryField).vars ⊆ {w} := by
    cases hb : sign i w
    · simp
    · simp
  have hveq : v = w := Finset.mem_singleton.mp (hvars hvw)
  simpa [hveq] using hw

theorem boundary_singleton (E : I → Finset V) (i : I) : boundary E {i} = E i := by
  ext v
  simp

theorem reduction_rawClause {E : I → Finset V} {s B : ℕ}
    (hexp : HalfBoundaryExpander E s) (hroom : 4 * B ≤ s) (hB : 1 ≤ B)
    (sign : I → V → Bool) (i : I) (hwidth : (E i).card ≤ B) :
    reduction E sign s (rawClause E sign i) = 0 := by
  let A := support E s (E i)
  have hsmall : A.card ≤ s := by
    have hs := support_card_le hexp hroom hwidth
    change (support E s (E i)).card ≤ s
    omega
  have hcover : ∀ d ∈ (rawClause E sign i).support, support E s d.support ⊆ A := by
    intro d hd
    exact support_mono E s ((support_subset_vars_of_mem_support hd).trans
      (rawClause_vars_subset E sign i))
  rw [reduction_eq_normalForm_of_cover E sign s A hsmall _ hcover]
  apply (normalForm_eq_zero_iff _ _ _).mpr
  apply rawClause_mem_clauseIdeal
  have hsingle : ({i} : Finset I).card ≤ s := by simp; omega
  exact subset_support E hsingle (by rw [boundary_singleton]) (Finset.mem_singleton_self i)

/-- The multiplication step uses a common pooled support for both sides.
Ordinary powers, including a repeated variable, are handled by the same proof. -/
theorem reduction_mul_term {E : I → Finset V} {s B : ℕ}
    (hexp : HalfBoundaryExpander E s) (hroom : 4 * B ≤ s)
    (sign : I → V → Bool) (v : V) (d : V →₀ ℕ) (hd : d.degree < B) :
    reduction E sign s (X v * monomial d 1) =
      reduction E sign s (X v * termReduction E sign s d) := by
  let T := insert v d.support
  let A := support E s T
  have hT : T.card ≤ B := (Finset.card_insert_le v d.support).trans
    (by have := support_card_le_degree d; omega)
  have hA : A.card ≤ s := by
    have := support_card_le hexp hroom hT
    change (support E s T).card ≤ s
    omega
  have hSA : support E s d.support ⊆ A :=
    support_mono E s (Finset.subset_insert v d.support)
  have hvars : (termReduction E sign s d).vars ⊆ A.biUnion E ∪ T := by
    apply (normalForm_vars_subset _ E sign _ _).trans
    rw [vars_monomial (by decide : (1 : BinaryField) ≠ 0)]
    exact Finset.union_subset_union (Finset.biUnion_subset_biUnion_of_subset_left E hSA)
      (Finset.subset_insert v d.support)
  have hmulvars : (X v * termReduction E sign s d).vars ⊆ A.biUnion E ∪ T := by
    apply (vars_mul _ _).trans
    apply Finset.union_subset
    · simpa only [vars_X, Finset.singleton_subset_iff] using
        (Finset.mem_union_right (A.biUnion E) (Finset.mem_insert_self v d.support))
    · exact hvars
  have hmuldeg : (X v * termReduction E sign s d).totalDegree ≤ B := by
    have h := totalDegree_mul (X v) (termReduction E sign s d)
    rw [totalDegree_X] at h
    have hr := termReduction_degree E sign s d
    omega
  have hcover : ∀ e ∈ (X v * termReduction E sign s d).support,
      support E s e.support ⊆ A := by
    intro e he
    apply support_absorbs hexp hroom hT
      ((support_card_le_degree e).trans ((le_totalDegree he).trans hmuldeg))
    exact (support_subset_vars_of_mem_support he).trans hmulvars
  rw [reduction_eq_normalForm_of_cover E sign s A hA _ hcover]
  change reduction E sign s (X v * monomial d 1) =
    normalForm MonomialOrder.degLex (clauseIdeal E sign A)
      (X v * normalForm MonomialOrder.degLex
        (clauseIdeal E sign (support E s d.support)) (monomial d 1))
  rw [normalForm_mul_normalForm (clauseIdeal_mono E sign hSA)]
  have hsupport : (Finsupp.single v 1 + d).support = T := by
    simp [T, Finsupp.support_add_eq_union]
  change reduction E sign s (monomial (Finsupp.single v 1) 1 * monomial d 1) = _
  rw [monomial_mul_monomial, one_mul, reduction_monomial, hsupport]
  rw [X, monomial_mul_monomial, one_mul]

theorem reduction_mul_var {E : I → Finset V} {s B : ℕ}
    (hexp : HalfBoundaryExpander E s) (hroom : 4 * B ≤ s)
    (sign : I → V → Bool) (v : V) (p : MvPolynomial V BinaryField)
    (hp : p.totalDegree < B) :
    reduction E sign s (X v * p) = reduction E sign s (X v * reduction E sign s p) := by
  have hexpand : p = ∑ d ∈ p.support, p.coeff d • (monomial d 1 : MvPolynomial V BinaryField) := by
    conv_lhs => rw [p.as_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [smul_monomial, smul_eq_mul, mul_one]
  conv_lhs => rw [hexpand, Finset.mul_sum, map_sum]
  conv_rhs => rw [hexpand, map_sum, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [map_smul, mul_smul_comm, reduction_monomial_one]
  rw [reduction_mul_term hexp hroom sign v d ((le_totalDegree hd).trans_lt hp)]

/-- The constructed operator annihilates every ordinary-PC derivation of
degree at most B from the actual signed input clauses and Boolean axioms. -/
theorem reduction_derives_zero {E : I → Finset V} {s B : ℕ}
    (hexp : HalfBoundaryExpander E s) (hroom : 4 * B ≤ s) (hB : 1 ≤ B)
    (sign : I → V → Bool) (hwidth : ∀ i, (E i).card ≤ B)
    {p : MvPolynomial V BinaryField}
    (hp : Derives (clauseBase E sign Finset.univ) B p) : reduction E sign s p = 0 := by
  induction hp with
  | zero => exact map_zero _
  | hyp hf _ =>
    rcases hf with ⟨v, rfl⟩ | ⟨i, _, rfl⟩
    · exact reduction_boolean_generator E sign s v
    · exact reduction_rawClause hexp hroom hB sign i (hwidth i)
  | add _ _ ih jh => simp only [map_add, ih, jh, add_zero]
  | smul a _ ih => simp only [map_smul, ih, smul_zero]
  | @mul_var v f _ hdeg ih =>
    by_cases hf : f = 0
    · simp [hf]
    · have hsmall : f.totalDegree < B := by
        rw [totalDegree_mul_of_isDomain (X_ne_zero v) hf, totalDegree_X] at hdeg
        omega
      rw [reduction_mul_var hexp hroom sign v f hsmall, ih, mul_zero, map_zero]

/-- Separation is now a theorem of expansion and clause width, not an input
assumption. It holds uniformly for every signing of the incidence structure. -/
theorem goodSpace_separated {E : I → Finset V} {s B : ℕ}
    (hexp : HalfBoundaryExpander E s) (hroom : 4 * B ≤ s) (hB : 1 ≤ B)
    (sign : I → V → Bool) (hwidth : ∀ i, (E i).card ≤ B) (k : ℕ)
    (p : MvPolynomial V BinaryField) (hp : p ∈ goodSpace E s k)
    (hderive : Derives (clauseBase E sign Finset.univ) B p) : p = 0 := by
  rw [← reduction_fixes_goodSpace E sign s k hp]
  exact reduction_derives_zero hexp hroom hB sign hwidth hderive

end

end BoundaryLab.ExpanderReduction
