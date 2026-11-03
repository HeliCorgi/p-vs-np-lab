import Std

/-!
# An elementary obstruction to bounded-width boundary clauses

Five boundary vertices are adjacent to one hidden vertex.  There are five
available colors.  Eliminating the hidden vertex permits precisely those
boundary colorings having an equal pair.

The representation language below has only equality and disequality atoms
between boundary vertices.  Clauses are disjunctions, CNFs are conjunctions,
and neither representation introduces auxiliary variables.

The finite computations in this file use the kernel's ordinary decision
procedure.  The lower-bound argument for an arbitrary clause is symbolic:
each one-pair collision supplies a separate required equality literal.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BoundaryLab.Star5

abbrev Color := Fin 5
abbrev Port := Fin 5
abbrev Pair := Fin 10

/- Lean 4.19 supplies bounded natural-number existential decisions, but does
   not register the corresponding `Fin` wrapper.  This constructive adapter
   preserves kernel evaluation of the finite checks below. -/
private instance decidableExistsFin {n : Nat} (P : Fin n → Prop)
    [DecidablePred P] : Decidable (∃ i : Fin n, P i) :=
  decidable_of_iff (∃ m : Nat, ∃ h : m < n, P ⟨m, h⟩)
    ⟨fun ⟨m, h, hp⟩ => ⟨⟨m, h⟩, hp⟩,
      fun ⟨i, hp⟩ => ⟨i.val, i.isLt, hp⟩⟩

/-- The five boundary colors; the hidden center is not a field. -/
structure Boundary where
  c0 : Color
  c1 : Color
  c2 : Color
  c3 : Color
  c4 : Color
  deriving DecidableEq, Repr

/-- Read a boundary color at one of the five ordered ports. -/
def Boundary.color (b : Boundary) (i : Port) : Color :=
  match i.val with
  | 0 => b.c0
  | 1 => b.c1
  | 2 => b.c2
  | 3 => b.c3
  | _ => b.c4

/-- Lexicographic enumeration of all ten unordered distinct port pairs. -/
def pairEnds (p : Pair) : Port × Port :=
  match p.val with
  | 0 => (0, 1)
  | 1 => (0, 2)
  | 2 => (0, 3)
  | 3 => (0, 4)
  | 4 => (1, 2)
  | 5 => (1, 3)
  | 6 => (1, 4)
  | 7 => (2, 3)
  | 8 => (2, 4)
  | _ => (3, 4)

def EqAt (b : Boundary) (p : Pair) : Prop :=
  b.color (pairEnds p).1 = b.color (pairEnds p).2

instance (b : Boundary) (p : Pair) : Decidable (EqAt b p) := by
  unfold EqAt
  infer_instance

/-- Exactly the proper-coloring constraints of the hidden center's star. -/
def StarExtends (b : Boundary) : Prop :=
  ∃ x : Color, ∀ i : Port, x ≠ b.color i

instance (b : Boundary) : Decidable (StarExtends b) := by
  unfold StarExtends
  infer_instance

def HasCollision (b : Boundary) : Prop :=
  ∃ p : Pair, EqAt b p

instance (b : Boundary) : Decidable (HasCollision b) := by
  unfold HasCollision
  infer_instance

private theorem finite_star_iff_collision :
    ∀ a0 a1 a2 a3 a4 : Color,
      StarExtends ⟨a0, a1, a2, a3, a4⟩ ↔
        HasCollision ⟨a0, a1, a2, a3, a4⟩ := by
  decide

/-- Eliminating the hidden star center gives the equal-pair relation. -/
theorem star_iff_collision (b : Boundary) :
    StarExtends b ↔ HasCollision b := by
  cases b with
  | mk a0 a1 a2 a3 a4 =>
      exact finite_star_iff_collision a0 a1 a2 a3 a4

def allDistinct : Boundary := ⟨0, 1, 2, 3, 4⟩

/-- Identify just the endpoints of `p`, leaving every other color distinct. -/
def pairWitness (p : Pair) : Boundary :=
  let ends := pairEnds p
  let recolor : Color → Color := fun c => if c = ends.2 then ends.1 else c
  ⟨recolor 0, recolor 1, recolor 2, recolor 3, recolor 4⟩

theorem allDistinct_not_extendible : ¬ StarExtends allDistinct := by
  decide

private theorem finite_pairWitness_extends :
    ∀ p : Pair, StarExtends (pairWitness p) := by
  decide

theorem pairWitness_extends (p : Pair) : StarExtends (pairWitness p) :=
  finite_pairWitness_extends p

private theorem finite_pairWitness_eq_iff :
    ∀ p q : Pair, EqAt (pairWitness p) q ↔ q = p := by
  decide

theorem pairWitness_eq_iff (p q : Pair) :
    EqAt (pairWitness p) q ↔ q = p :=
  finite_pairWitness_eq_iff p q

private theorem finite_allDistinct_no_equalities :
    ∀ p : Pair, ¬ EqAt allDistinct p := by
  decide

inductive Literal where
  | eq (pair : Pair)
  | ne (pair : Pair)
  deriving DecidableEq, Repr

def LiteralHolds (b : Boundary) : Literal → Prop
  | .eq p => EqAt b p
  | .ne p => ¬ EqAt b p

abbrev Clause := List Literal
abbrev CNF := List Clause

def ClauseHolds (b : Boundary) (c : Clause) : Prop :=
  ∃ l : Literal, l ∈ c ∧ LiteralHolds b l

def ValidClause (c : Clause) : Prop :=
  ∀ b : Boundary, StarExtends b → ClauseHolds b c

def CNFHolds (b : Boundary) (f : CNF) : Prop :=
  ∀ c : Clause, c ∈ f → ClauseHolds b c

def RepresentsStar (f : CNF) : Prop :=
  ∀ b : Boundary, StarExtends b ↔ CNFHolds b f

/--
Any valid clause that rejects the all-distinct coloring contains every one
of the ten equality literals.  This quantifies over arbitrary finite clauses,
including clauses with repetitions and disequality literals.
-/
theorem valid_rejecting_clause_contains_all_equalities
    (c : Clause) (hvalid : ValidClause c)
    (hreject : ¬ ClauseHolds allDistinct c) :
    ∀ p : Pair, Literal.eq p ∈ c := by
  intro p
  obtain ⟨l, hmem, hholds⟩ := hvalid (pairWitness p) (pairWitness_extends p)
  cases l with
  | eq q =>
      have hqp : q = p := (pairWitness_eq_iff p q).mp hholds
      simpa only [hqp] using hmem
  | ne q =>
      exact False.elim (hreject
        ⟨Literal.ne q, hmem, finite_allDistinct_no_equalities q⟩)

/--
Every exact auxiliary-free CNF for the star projection has a clause containing
all ten distinct equality literals.  Replacing one wide clause by arbitrarily
many narrower clauses therefore cannot express this same relation.
-/
theorem every_exact_CNF_has_all_equalities_clause
    (f : CNF) (hexact : RepresentsStar f) :
    ∃ c : Clause, c ∈ f ∧ ∀ p : Pair, Literal.eq p ∈ c := by
  classical
  have hrejected : ¬ CNFHolds allDistinct f := by
    intro h
    exact allDistinct_not_extendible ((hexact allDistinct).mpr h)
  have hbad : ∃ c : Clause, c ∈ f ∧ ¬ ClauseHolds allDistinct c := by
    apply Classical.byContradiction
    intro hnone
    apply hrejected
    intro c hmem
    apply Classical.byContradiction
    intro hfalse
    exact hnone ⟨c, hmem, hfalse⟩
  obtain ⟨c, hmem, hfalse⟩ := hbad
  refine ⟨c, hmem, valid_rejecting_clause_contains_all_equalities c ?_ hfalse⟩
  intro b hb
  exact (hexact b).mp hb c hmem

/-- The width-ten clause is also sufficient. -/
def allEqualityClause : Clause :=
  [.eq 0, .eq 1, .eq 2, .eq 3, .eq 4,
   .eq 5, .eq 6, .eq 7, .eq 8, .eq 9]

private theorem equality_mem_allEqualityClause :
    ∀ p : Pair, Literal.eq p ∈ allEqualityClause := by
  decide

private theorem disequality_not_mem_allEqualityClause :
    ∀ p : Pair, Literal.ne p ∉ allEqualityClause := by
  decide

theorem allEqualityClause_length : allEqualityClause.length = 10 := rfl

theorem allEqualityClause_nodup : allEqualityClause.Nodup := by
  decide

theorem star_iff_allEqualityClause (b : Boundary) :
    StarExtends b ↔ ClauseHolds b allEqualityClause := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := (star_iff_collision b).mp h
    exact ⟨Literal.eq p, equality_mem_allEqualityClause p, hp⟩
  · intro h
    obtain ⟨l, hmem, hholds⟩ := h
    apply (star_iff_collision b).mpr
    cases l with
    | eq p => exact ⟨p, hholds⟩
    | ne p => exact False.elim (disequality_not_mem_allEqualityClause p hmem)

#print axioms star_iff_collision
#print axioms valid_rejecting_clause_contains_all_equalities
#print axioms every_exact_CNF_has_all_equalities_clause
#print axioms star_iff_allEqualityClause

end BoundaryLab.Star5
