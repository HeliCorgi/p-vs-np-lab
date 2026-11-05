import ProofLab.AffineIndicators
import ProofLab.MaskedDAG

/-!
# From affine-clause DAGs to ordinary polynomial DAGs

The source certificate contains affine clauses, an explicit Boolean tag for
initial nodes, and semantic unary/binary steps with strictly earlier parents.
Actual initial nodes use their raw CNF-style product, which belongs to the
original polynomial axiom set. Derived nodes use the basis-compressed product
constructed in `AffineIndicators`. No proof is eliminated from `Prop` to
decide which polynomial to use: the initial-node tags are explicit data.

This adapter proves the polynomial DAG, its falsity semantics, its literal
constant-one finish, and the retained-node degree bound. The replay corollary
uses the actual ordinary-PC theorem. The rank appearing here is the span rank
of affine polynomials including constants; it is not silently identified with
the geometric codimension of a zero-flat.
-/

set_option autoImplicit false

namespace BoundaryLab.AffineClauseDAG

noncomputable section

open MvPolynomial
open BoundaryLab.AffineIndicators

variable {V : Type} {S k R : ℕ}

/-- A raw initial clause or a sound unary/binary inference. The initial-node
tag is part of the source data and must agree with the kind of the step. -/
inductive ClauseStep (F : Set (Poly V))
    (clauses : Fin S → Clause V) (initial : Fin S → Bool) (i : Fin S) : Prop
  | input (tag : initial i = true)
      (member : falsityPolynomial (clauses i) ∈ F) :
      ClauseStep F clauses initial i
  | unary (tag : initial i = false) (parent : Fin S)
      (earlier : parent.val < i.val)
      (sound : ∀ x : V → BinaryField,
        clauseHolds (clauses parent) x → clauseHolds (clauses i) x) :
      ClauseStep F clauses initial i
  | binary (tag : initial i = false) (left right : Fin S)
      (earlierLeft : left.val < i.val) (earlierRight : right.val < i.val)
      (sound : ∀ x : V → BinaryField,
        clauseHolds (clauses left) x → clauseHolds (clauses right) x →
          clauseHolds (clauses i) x) :
      ClauseStep F clauses initial i

/-- A topologically indexed clause DAG, allowing arbitrary parent reuse. -/
def ClauseDAG (F : Set (Poly V))
    (clauses : Fin S → Clause V) (initial : Fin S → Bool) : Prop :=
  ∀ i, ClauseStep F clauses initial i

/-- Initial lines retain their actual raw axiom; derived lines are compressed
by the already-proved basis-subclause construction. -/
def nodePolynomial (clauses : Fin S → Clause V) (initial : Fin S → Bool)
    (i : Fin S) : Poly V :=
  if initial i then falsityPolynomial (clauses i)
  else compressedPolynomial (clauses i)

/-- The ordinary degree budget supplied by the two kinds of node. -/
def nodeDegreeBudget (clauses : Fin S → Clause V) (initial : Fin S → Bool)
    (i : Fin S) : ℕ :=
  if initial i then (clauses i).card else spanRank (clauses i)

theorem nodePolynomial_of_input
    (clauses : Fin S → Clause V) (initial : Fin S → Bool) (i : Fin S)
    (h : initial i = true) :
    nodePolynomial clauses initial i = falsityPolynomial (clauses i) := by
  simp [nodePolynomial, h]

theorem nodePolynomial_of_derived
    (clauses : Fin S → Clause V) (initial : Fin S → Bool) (i : Fin S)
    (h : initial i = false) :
    nodePolynomial clauses initial i = compressedPolynomial (clauses i) := by
  simp [nodePolynomial, h]

/-- Both node representations have exactly the raw clause's Boolean values. -/
theorem nodePolynomial_eval_eq_raw
    (clauses : Fin S → Clause V) (initial : Fin S → Bool)
    (i : Fin S) (x : V → BinaryField) :
    eval x (nodePolynomial clauses initial i) =
      eval x (falsityPolynomial (clauses i)) := by
  cases h : initial i <;> simp [nodePolynomial, h, compressedPolynomial_eval]

theorem nodePolynomial_eval_zero_iff
    (clauses : Fin S → Clause V) (initial : Fin S → Bool)
    (i : Fin S) (x : V → BinaryField) :
    eval x (nodePolynomial clauses initial i) = 0 ↔ clauseHolds (clauses i) x := by
  rw [nodePolynomial_eval_eq_raw, eval_falsityPolynomial_eq_zero]

theorem nodePolynomial_eval_one_iff
    (clauses : Fin S → Clause V) (initial : Fin S → Bool)
    (i : Fin S) (x : V → BinaryField) :
    eval x (nodePolynomial clauses initial i) = 1 ↔ clauseZero (clauses i) x := by
  rw [nodePolynomial_eval_eq_raw, eval_falsityPolynomial_eq_one]

/-- This is the precise interface needed for a restriction-map cover of the
discarded nodes. Empty zero-flats give an empty nonzero locus automatically. -/
theorem nodePolynomial_eval_ne_zero_iff
    (clauses : Fin S → Clause V) (initial : Fin S → Bool)
    (i : Fin S) (x : V → BinaryField) :
    eval x (nodePolynomial clauses initial i) ≠ 0 ↔ clauseZero (clauses i) x := by
  constructor
  · intro hne
    rcases binary_eq_zero_or_one (eval x (nodePolynomial clauses initial i)) with hz | ho
    · exact False.elim (hne hz)
    · exact (nodePolynomial_eval_one_iff clauses initial i x).mp ho
  · intro hz
    have ho := (nodePolynomial_eval_one_iff clauses initial i x).mpr hz
    exact fun he => one_ne_zero (ho.symm.trans he)

/-- The empty source clause produces the literal ordinary constant one,
regardless of its initial/derived tag. -/
theorem nodePolynomial_of_empty
    (clauses : Fin S → Clause V) (initial : Fin S → Bool)
    (i : Fin S) (h : clauses i = ∅) :
    nodePolynomial clauses initial i = 1 := by
  simp [nodePolynomial, h, falsityPolynomial]

/-- Actual source membership and clause-level semantic soundness construct
the polynomial DAG; polynomial soundness is not an extra hypothesis. -/
theorem polynomialDag_of_clauseDag {F : Set (Poly V)}
    (clauses : Fin S → Clause V) (initial : Fin S → Bool)
    (dag : ClauseDAG F clauses initial) :
    MaskedDAG.SemanticDAG F (nodePolynomial clauses initial) := by
  intro i
  cases dag i with
  | input htag hmember =>
    exact .input (by simpa [nodePolynomial, htag] using hmember)
  | unary _htag parent hearlier hsound =>
    exact .unary parent hearlier (fun x hp =>
      (nodePolynomial_eval_zero_iff clauses initial i x).mpr
        (hsound x ((nodePolynomial_eval_zero_iff clauses initial parent x).mp hp)))
  | binary _htag left right hearlierLeft hearlierRight hsound =>
    exact .binary left right hearlierLeft hearlierRight (fun x hl hr =>
      (nodePolynomial_eval_zero_iff clauses initial i x).mpr
        (hsound x
          ((nodePolynomial_eval_zero_iff clauses initial left x).mp hl)
          ((nodePolynomial_eval_zero_iff clauses initial right x).mp hr)))

theorem nodePolynomial_degree
    (clauses : Fin S → Clause V) (initial : Fin S → Bool)
    (i : Fin S) (h : IsAffineClause (clauses i)) :
    (nodePolynomial clauses initial i).totalDegree ≤
      nodeDegreeBudget clauses initial i := by
  cases htag : initial i with
  | false =>
    simpa [nodePolynomial, nodeDegreeBudget, htag] using
      compressedPolynomial_degree (clauses i) h
  | true =>
    simpa [nodePolynomial, nodeDegreeBudget, htag] using
      falsityPolynomial_degree (clauses i) h

/-- Raw input width and retained derived-node span rank suffice for the
retained degree condition of the ordinary-PC replay theorem. -/
theorem retained_degree_bound
    (clauses : Fin S → Clause V) (initial : Fin S → Bool)
    (hAffine : ∀ i, IsAffineClause (clauses i)) (Low : Fin S → Prop)
    (hinputWidth : ∀ i, initial i = true → (clauses i).card ≤ R)
    (hderivedRank : ∀ i, initial i = false → Low i → spanRank (clauses i) ≤ R) :
    ∀ i, Low i → (nodePolynomial clauses initial i).totalDegree ≤ R := by
  intro i hlow
  apply (nodePolynomial_degree clauses initial i (hAffine i)).trans
  cases htag : initial i with
  | false =>
    simpa [nodeDegreeBudget, htag] using hderivedRank i htag hlow
  | true =>
    simpa [nodeDegreeBudget, htag] using hinputWidth i htag

/-- Complete clause-level weighted replay. The hypotheses refer to actual
raw input membership, clause truth, clause zero-sets, raw input width, and
derived span rank. Final ordinary-PC derivability is obtained internally. -/
theorem affine_clause_dag_replay [Fintype V] [DecidableEq V]
    {F : Set (Poly V)}
    (hbool : (MathResearch.PolynomialCalculus.booleanBase : Set (Poly V)) ⊆ F)
    (clauses : Fin S → Clause V) (initial : Fin S → Bool)
    (dag : ClauseDAG F clauses initial)
    (hAffine : ∀ i, IsAffineClause (clauses i)) (Low : Fin S → Prop)
    (hinputWidth : ∀ i, initial i = true → (clauses i).card ≤ R)
    (hderivedRank : ∀ i, initial i = false → Low i → spanRank (clauses i) ≤ R)
    {f : Poly V} (hf : f.totalDegree ≤ k)
    (hvanish : ∀ i, ¬ Low i → ∀ x : V → BinaryField,
      clauseZero (clauses i) x → eval x f = 0)
    (finish : Fin S) (hfinish : clauses finish = ∅) :
    MathResearch.PolynomialCalculus.Derives F (k + 3 * R) f := by
  refine MaskedDAG.masked_dag_replay hbool
    (polynomialDag_of_clauseDag clauses initial dag) Low hf
    (retained_degree_bound clauses initial hAffine Low hinputWidth hderivedRank)
    ?_ finish (nodePolynomial_of_empty clauses initial finish hfinish)
  intro i hi x hq
  exact hvanish i hi x ((nodePolynomial_eval_ne_zero_iff clauses initial i x).mp hq)

end

end BoundaryLab.AffineClauseDAG
