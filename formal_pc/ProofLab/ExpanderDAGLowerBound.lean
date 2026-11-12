import ProofLab.ExpanderReduction

/-!
# Source-DAG lower bounds from an actual boundary expander

The source axioms are the actual signed raw clauses of E, together with the
explicit Boolean generators. The separating space and its PC separation are
constructed internally. Neither hsep nor an abstract reduction operator is an
assumption of these endpoints. Quantitative good-set density and the existence
of a suitable asymptotic CNF family remain separate proof obligations.
-/

namespace BoundaryLab.ExpanderDAGLowerBound

noncomputable section

open MvPolynomial MathResearch.PolynomialCalculus ExpanderSupport
open BooleanIdealNormalForm ExpanderMonomials ExpanderReduction
open AffineIndicators (BinaryField)

variable {I V : Type} [Fintype I] [DecidableEq I] [Fintype V] [LinearOrder V]

/-- The distinct-flat budget with ordinary-PC separation discharged from
boundary expansion, uniformly for all signs on the actual source clauses. -/
theorem expander_goodSupports_le_distinct_budget
    {E : I → Finset V} {s k R S : ℕ}
    (hexp : HalfBoundaryExpander E s) (hroom : 4 * (k + 3 * R) ≤ s)
    (hB : 1 ≤ k + 3 * R) (sign : I → V → Bool)
    (hwidth : ∀ i, (E i).card ≤ k + 3 * R)
    (clauses : Fin S → AffineIndicators.Clause V) (initial : Fin S → Bool)
    (dag : AffineClauseDAG.ClauseDAG (clauseBase E sign Finset.univ) clauses initial)
    (hAffine : ∀ i, AffineIndicators.IsAffineClause (clauses i))
    (hinputWidth : ∀ i, initial i = true → (clauses i).card ≤ R)
    (finish : Fin S) (hfinish : clauses finish = ∅) :
    (goodSupports E s k).card ≤
      (DistinctAffineFlats.distinctFlats clauses
        (fun i => AffineIndicators.spanRank (clauses i) ≤ R)).card *
      BooleanFunctionSpace.booleanBudget k (Fintype.card V - R - 1) := by
  exact goodSupports_le_distinct_budget (fun _ hp => Or.inl hp)
    clauses initial dag hAffine hinputWidth finish hfinish E s
    (goodSpace_separated hexp hroom hB sign hwidth k)

/-- In particular, the same budget bounds the total source-DAG line count. -/
theorem expander_goodSupports_le_line_budget
    {E : I → Finset V} {s k R S : ℕ}
    (hexp : HalfBoundaryExpander E s) (hroom : 4 * (k + 3 * R) ≤ s)
    (hB : 1 ≤ k + 3 * R) (sign : I → V → Bool)
    (hwidth : ∀ i, (E i).card ≤ k + 3 * R)
    (clauses : Fin S → AffineIndicators.Clause V) (initial : Fin S → Bool)
    (dag : AffineClauseDAG.ClauseDAG (clauseBase E sign Finset.univ) clauses initial)
    (hAffine : ∀ i, AffineIndicators.IsAffineClause (clauses i))
    (hinputWidth : ∀ i, initial i = true → (clauses i).card ≤ R)
    (finish : Fin S) (hfinish : clauses finish = ∅) :
    (goodSupports E s k).card ≤
      S * BooleanFunctionSpace.booleanBudget k (Fintype.card V - R - 1) := by
  exact (expander_goodSupports_le_distinct_budget hexp hroom hB sign hwidth
    clauses initial dag hAffine hinputWidth finish hfinish).trans
    (Nat.mul_le_mul_right _ (DistinctAffineFlats.card_distinctFlats_le clauses _))

end

end BoundaryLab.ExpanderDAGLowerBound
