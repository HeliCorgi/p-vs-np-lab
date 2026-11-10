import ProofLab.CNFFamilyExistence

/-!
# The complete phase-20 existence and exponential lower-bound theorem

For every n above an explicit constant there is an unsatisfiable proper linear
3-CNF with 12n clauses, maximum occurrence 4096, and the required expansion.
Every original-variable affine-clause source DAG refuting it has exponentially
many nodes and distinct nonempty false flats above the chosen rank threshold.

This is a theorem about the specified proof system, not a separation of P and NP.
-/

namespace BoundaryLab.Phase20

noncomputable section
open TripleCounting TriplePruning CNFFamilyExistence CNFSigning ExponentialBudget
open BooleanIdealNormalForm AffineIndicators

theorem numericalThreshold_ge_familyThreshold : 1000000 ≤ numericalThreshold := by
  norm_num [numericalThreshold, probabilityDenominator, expansionScale]

/-- No CNF-family existence, separation, density or asymptotic estimate occurs
among the assumptions. The only external size assumption is the displayed
explicit threshold. DAG validity and its endpoint are the proof-system inputs. -/
theorem exists_unsat_exponential_lower_bound (n : ℕ) (hn : numericalThreshold ≤ n) :
    ∃ H : Finset (Triple (Fin n)), Admissible H ∧
      ∃ sign : H → Fin n → Bool, ¬ Satisfiable (supportOn H) sign ∧
        ∀ (S : ℕ) (clauses : Fin S → Clause (Fin n)) (initial : Fin S → Bool),
          AffineClauseDAG.ClauseDAG (clauseBase (supportOn H) sign Finset.univ) clauses initial →
          (∀ i, IsAffineClause (clauses i)) →
          (∀ i, initial i = true → (clauses i).card ≤ 3) →
          ∀ finish : Fin S, clauses finish = ∅ →
            (1 / 4 : ℝ) * Real.exp ((n : ℝ) / (81 * 2 ^ 65 * 10 ^ 32)) ≤
              (DistinctAffineFlats.distinctFlats clauses
                (fun i => spanRank (clauses i) ≤ rankThreshold n)).card ∧
            (1 / 4 : ℝ) * Real.exp ((n : ℝ) / (81 * 2 ^ 65 * 10 ^ 32)) ≤ S := by
  have hnF : 1000000 ≤ Fintype.card (Fin n) := by
    simpa only [Fintype.card_fin] using numericalThreshold_ge_familyThreshold.trans hn
  obtain ⟨H, hH, ⟨sign, hunsat⟩, _⟩ := exists_unsatisfiable_family hnF
  refine ⟨H, hH, sign, hunsat, ?_⟩
  intro S clauses initial dag hAffine hinput finish hfinish
  have hm : Fintype.card H = 12 * Fintype.card (Fin n) := by
    simpa only [Fintype.card_coe] using hH.1
  have hb := bounded_occurrence_exponential_dag
    (by simpa only [Fintype.card_fin] using hn) hH.2.2.2 (supportOn_width H)
    hH.2.1 hH.2.2.1 hm sign S clauses initial dag hAffine hinput finish hfinish
  simpa only [Fintype.card_fin, exponentDenominator, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat] using hb

end

end BoundaryLab.Phase20
