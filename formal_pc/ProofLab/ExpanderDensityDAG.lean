import ProofLab.ExpanderDensity

/-!
# A quantitative source-DAG budget with density proved internally

The degree k is selected from the actual good-set family and works for every
signing and every source DAG obeying the stated width and degree room. The
endpoint assumes neither PC separation nor a good-set density bound. Existence
of the expanding support family and the final binomial/exponential estimate
are still separate obligations.
-/

namespace BoundaryLab.ExpanderDensityDAG

noncomputable section

open ExpanderSupport ExpanderObstructions LinearClauseBoundary ExpanderDensity
open ExpanderDAGLowerBound BooleanIdealNormalForm
open AffineIndicators (BinaryField)

variable {I V : Type} [Fintype I] [DecidableEq I] [Fintype V] [LinearOrder V]

theorem bounded_occurrence_dense_dag_budget {E : I → Finset V} {s Δ : ℕ}
    (hexp : HalfBoundaryExpander E s) (hwidth : ∀ i, (E i).card = 3)
    (hlinear : LinearSupports E) (hocc : ∀ v, (occurrences E v).card ≤ Δ)
    (hm : Fintype.card I = 12 * Fintype.card V)
    {ε p : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hpdef : p = ε / (1024 * (((max 1 (3 * Δ) : ℕ) : ℝ) ^ 2) ^ 2))
    (hpn : 16 ≤ p * Fintype.card V) :
    ∃ k, k ≤ Fintype.card V ∧ p * Fintype.card V / 2 ≤ (k : ℝ) ∧
      (k : ℝ) ≤ 2 * (p * Fintype.card V) ∧
      ∀ (sign : I → V → Bool) (R S : ℕ), 3 ≤ R → 4 * (k + 3 * R) ≤ s →
      ∀ (clauses : Fin S → AffineIndicators.Clause V) (initial : Fin S → Bool),
      AffineClauseDAG.ClauseDAG (clauseBase E sign Finset.univ) clauses initial →
      (∀ i, AffineIndicators.IsAffineClause (clauses i)) →
      (∀ i, initial i = true → (clauses i).card ≤ R) →
      ∀ finish : Fin S, clauses finish = ∅ →
      let L := ((1 / 2 : ℝ) * Real.exp (-168 * Fintype.card V *
        (((max 1 (3 * Δ) : ℕ) : ℝ) ^ 2) ^ 4 * p ^ 3)) *
        ((Fintype.card V).choose k : ℝ)
      L ≤ (DistinctAffineFlats.distinctFlats clauses
        (fun i => AffineIndicators.spanRank (clauses i) ≤ R)).card *
          (BooleanFunctionSpace.booleanBudget k (Fintype.card V - R - 1) : ℝ) ∧
      L ≤ S * (BooleanFunctionSpace.booleanBudget k (Fintype.card V - R - 1) : ℝ) := by
  obtain ⟨k, hkn, hlo, hhi, hdensity⟩ := bounded_occurrence_dense_goodSupports
    hexp hwidth hlinear hocc hm hε hε1 hpdef hpn
  refine ⟨k, hkn, hlo, hhi, ?_⟩
  intro sign R S hR hroom clauses initial dag hAffine hinputWidth finish hfinish
  have hB : 1 ≤ k + 3 * R := by omega
  have hw : ∀ i, (E i).card ≤ k + 3 * R := by intro i; rw [hwidth i]; omega
  have hdistinct := expander_goodSupports_le_distinct_budget hexp hroom hB sign hw
    clauses initial dag hAffine hinputWidth finish hfinish
  have hlines := expander_goodSupports_le_line_budget hexp hroom hB sign hw
    clauses initial dag hAffine hinputWidth finish hfinish
  constructor
  · exact hdensity.trans (by exact_mod_cast hdistinct)
  · exact hdensity.trans (by exact_mod_cast hlines)

end

end BoundaryLab.ExpanderDensityDAG
