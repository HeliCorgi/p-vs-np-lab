import ProofLab.ExpanderSupport
import ProofLab.DistinctAffineFlats

/-!
# The concrete good-monomial space and its exact dimension

The support family is the one in `ExpanderSupport`, not an arbitrary supplied
vector space. Squarefree monomials on its good k-sets are linearly independent,
have degree at most k, and span a space of exactly the good-set cardinality.
The generic DAG corollary in this module explicitly assumes ordinary-PC
separation. `ExpanderReduction` constructs the operator and proves separation;
`ExpanderDAGLowerBound` discharges that hypothesis for the actual clause family.
-/

namespace BoundaryLab.ExpanderMonomials

noncomputable section

open MvPolynomial MathResearch.PolynomialCalculus
open AffineIndicators (BinaryField)
open scoped BigOperators

variable {V : Type} [DecidableEq V]

def supportExponent (T : Finset V) : V →₀ ℕ := ∑ v ∈ T, Finsupp.single v 1

@[simp]
theorem supportExponent_apply (T : Finset V) (v : V) :
    supportExponent T v = if v ∈ T then 1 else 0 := by
  classical
  simp [supportExponent, Finsupp.single_apply]

@[simp]
theorem supportExponent_support (T : Finset V) : (supportExponent T).support = T := by
  ext v
  simp [supportExponent_apply]

theorem supportExponent_injective : Function.Injective (supportExponent (V := V)) := by
  intro T D h
  simpa using congrArg Finsupp.support h

theorem supportMonomial_eq_monomial (T : Finset V) :
    supportMonomial T = monomial (supportExponent T) (1 : BinaryField) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [supportMonomial, supportExponent]
  | @insert v T hv ih =>
    rw [supportMonomial, Finset.prod_insert hv]
    change X v * supportMonomial T = monomial (supportExponent (insert v T)) 1
    rw [ih]
    simp only [supportExponent, Finset.sum_insert hv]
    exact monomial_mul_monomial

theorem supportMonomial_linearIndependent :
    LinearIndependent BinaryField (supportMonomial (V := V)) := by
  simpa only [coe_basisMonomials, Function.comp_def, ← supportMonomial_eq_monomial] using
    (basisMonomials V BinaryField).linearIndependent.comp
      supportExponent supportExponent_injective

variable [Fintype V] {I : Type} [Fintype I] [DecidableEq I]

/-- Exactly the k-sets containing no boundary of a nonempty small clause set. -/
def goodSupports (E : I → Finset V) (s k : ℕ) : Finset (Finset V) := by
  classical
  exact Finset.univ.powersetCard k |>.filter (fun T => ExpanderSupport.support E s T = ∅)

@[simp]
theorem mem_goodSupports (E : I → Finset V) (s k : ℕ) (T : Finset V) :
    T ∈ goodSupports E s k ↔ T.card = k ∧ ExpanderSupport.support E s T = ∅ := by
  classical
  simp [goodSupports]

def goodSpace (E : I → Finset V) (s k : ℕ) : Submodule BinaryField (MvPolynomial V BinaryField) :=
  Submodule.span BinaryField (Set.range (fun T : goodSupports E s k => supportMonomial T.val))

theorem finrank_goodSpace (E : I → Finset V) (s k : ℕ) :
    Module.finrank BinaryField (goodSpace E s k) = (goodSupports E s k).card := by
  classical
  have hli : LinearIndependent BinaryField
      (fun T : goodSupports E s k => supportMonomial T.val) :=
    (supportMonomial_linearIndependent (V := V)).comp
      (fun T : goodSupports E s k => T.val) Subtype.val_injective
  change Module.finrank BinaryField (Submodule.span BinaryField
    (Set.range (fun T : goodSupports E s k => supportMonomial T.val))) = _
  rw [finrank_span_eq_card hli]
  exact Fintype.card_coe _

theorem goodSpace_degree (E : I → Finset V) (s k : ℕ)
    (p : MvPolynomial V BinaryField) (hp : p ∈ goodSpace E s k) : p.totalDegree ≤ k := by
  have hle : goodSpace E s k ≤ degreeSpace k := by
    apply Submodule.span_le.mpr
    rintro _ ⟨T, rfl⟩
    have hc := ((mem_goodSupports E s k T.val).mp T.property).1
    change (supportMonomial T.val).totalDegree ≤ k
    exact (supportMonomial_degree T.val).trans hc.le
  exact hle hp

/-- This connects the actual good-set cardinality to distinct source flats.
It does not discharge `hsep` or assert the asymptotic counting estimate. -/
theorem goodSupports_le_distinct_budget {S k R : ℕ}
    {F : Set (MvPolynomial V BinaryField)}
    (hbool : (booleanBase : Set (MvPolynomial V BinaryField)) ⊆ F)
    (clauses : Fin S → AffineIndicators.Clause V) (initial : Fin S → Bool)
    (dag : AffineClauseDAG.ClauseDAG F clauses initial)
    (hAffine : ∀ i, AffineIndicators.IsAffineClause (clauses i))
    (hinputWidth : ∀ i, initial i = true → (clauses i).card ≤ R)
    (finish : Fin S) (hfinish : clauses finish = ∅)
    (E : I → Finset V) (s : ℕ)
    (hsep : ∀ p ∈ goodSpace E s k, Derives F (k + 3 * R) p → p = 0) :
    (goodSupports E s k).card ≤
      (DistinctAffineFlats.distinctFlats clauses
        (fun i => AffineIndicators.spanRank (clauses i) ≤ R)).card *
      BooleanFunctionSpace.booleanBudget k (Fintype.card V - R - 1) := by
  rw [← finrank_goodSpace E s k]
  exact DistinctAffineFlats.affine_clause_separated_distinct_count hbool clauses initial dag
    hAffine hinputWidth finish hfinish (goodSpace E s k) (goodSpace_degree E s k) hsep

end

end BoundaryLab.ExpanderMonomials
