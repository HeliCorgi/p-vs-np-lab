import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# Counting connected vertex sets by explicit walks

Connectivity is expressed by an edge across every nontrivial cut. A closed
walk visiting a t-set in exactly 2(t-1) steps is constructed by inserting a
two-edge detour at an already visited vertex. This proves the bounded-degree
count without assuming a spanning-tree enumeration or traversal theorem.
-/

namespace BoundaryLab.ConnectedSetCounting

noncomputable section

open SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

def CutConnected (G : SimpleGraph V) (A : Finset V) : Prop :=
  A.Nonempty ∧ ∀ D ⊆ A, D.Nonempty → D ≠ A →
    ∃ i ∈ D, ∃ j ∈ A, j ∉ D ∧ G.Adj i j

def neighbors (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter (G.Adj v)

omit [DecidableEq V] in
@[simp]
theorem mem_neighbors (G : SimpleGraph V) (v w : V) : w ∈ neighbors G v ↔ G.Adj v w := by
  classical
  simp [neighbors]

def traces (G : SimpleGraph V) : ℕ → V → Finset (List V)
  | 0, v => {[v]}
  | n + 1, v => (neighbors G v).biUnion (fun w => (traces G n w).image (List.cons v))

theorem traces_card_le (G : SimpleGraph V) (q : ℕ)
    (hq : ∀ v, (neighbors G v).card ≤ q) (n : ℕ) (v : V) :
    (traces G n v).card ≤ q ^ n := by
  induction n generalizing v with
  | zero => simp [traces]
  | succ n ih =>
    calc
      _ ≤ ∑ w ∈ neighbors G v, ((traces G n w).image (List.cons v)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _w ∈ neighbors G v, q ^ n := Finset.sum_le_sum (fun w _ =>
        (Finset.card_image_le).trans (ih w))
      _ = (neighbors G v).card * q ^ n := by simp
      _ ≤ q * q ^ n := Nat.mul_le_mul_right _ (hq v)
      _ = q ^ (n + 1) := by rw [pow_succ, mul_comm]

theorem walk_support_mem_traces {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    p.support ∈ traces G p.length u := by
  induction p with
  | nil => simp [traces]
  | @cons u w v h p ih =>
    apply Finset.mem_biUnion.mpr
    exact ⟨w, (mem_neighbors G u w).mpr h, Finset.mem_image.mpr ⟨p.support, ih, rfl⟩⟩

omit [Fintype V] in
/-- Insert one out-and-back edge at an occurrence of a visited vertex. -/
theorem exists_detour {G : SimpleGraph V} {r i j : V} (p : G.Walk r r)
    (hi : i ∈ p.support) (hij : G.Adj i j) :
    ∃ q : G.Walk r r, q.length = p.length + 2 ∧
      q.support.toFinset = insert j p.support.toFinset := by
  let a := p.takeUntil i hi
  let b := p.dropUntil i hi
  let d : G.Walk i i := .cons hij (.cons hij.symm .nil)
  refine ⟨a.append (d.append b), ?_, ?_⟩
  · have hlen := congrArg Walk.length (p.take_spec hi)
    simp only [Walk.length_append] at hlen
    simp only [Walk.length_append]
    change a.length + (2 + b.length) = p.length + 2
    change a.length + b.length = p.length at hlen
    omega
  · ext v
    have hsplit : v ∈ p.support ↔ v ∈ a.support ∨ v ∈ b.support := by
      rw [← p.take_spec hi, Walk.mem_support_append_iff]
    have hiA : i ∈ a.support := a.end_mem_support
    simp only [List.mem_toFinset, Finset.mem_insert, Walk.mem_support_append_iff]
    change (v ∈ a.support ∨ (v ∈ [i, j, i] ∨ v ∈ b.support)) ↔ v = j ∨ v ∈ p.support
    simp only [List.mem_cons] at *
    aesop

omit [Fintype V] in
theorem exists_tour_prefix {G : SimpleGraph V} {A : Finset V}
    (hA : CutConnected G A) (r : V) (hr : r ∈ A) (n : ℕ) (hn : n < A.card) :
    ∃ p : G.Walk r r, p.length = 2 * n ∧ p.support.toFinset ⊆ A ∧
      p.support.toFinset.card = n + 1 := by
  induction n with
  | zero => exact ⟨.nil, by simp, by simpa using hr, by simp⟩
  | succ n ih =>
    obtain ⟨p, hp, hsub, hcard⟩ := ih (by omega)
    have hne : p.support.toFinset ≠ A := by
      intro heq
      rw [heq] at hcard
      omega
    have hnonempty : p.support.toFinset.Nonempty :=
      ⟨r, List.mem_toFinset.mpr p.start_mem_support⟩
    obtain ⟨i, hi, j, hj, hjnot, hij⟩ := hA.2 _ hsub hnonempty hne
    obtain ⟨q, hq, hqs⟩ := exists_detour p (List.mem_toFinset.mp hi) hij
    refine ⟨q, by omega, ?_, ?_⟩
    · rw [hqs]
      exact Finset.insert_subset hj hsub
    · rw [hqs, Finset.card_insert_of_notMem hjnot, hcard]

omit [Fintype V] in
/-- Every connected t-set has a closed traversal of length exactly 2(t-1). -/
theorem exists_tour {G : SimpleGraph V} {A : Finset V} (hA : CutConnected G A) :
    ∃ r, ∃ p : G.Walk r r, p.length = 2 * (A.card - 1) ∧ p.support.toFinset = A := by
  obtain ⟨r, hr⟩ := hA.1
  have hpos : 0 < A.card := Finset.card_pos.mpr ⟨r, hr⟩
  obtain ⟨p, hp, hsub, hcard⟩ := exists_tour_prefix hA r hr (A.card - 1) (by omega)
  exact ⟨r, p, hp, Finset.eq_of_subset_of_card_le hsub (by omega)⟩

def connectedSets (G : SimpleGraph V) (t : ℕ) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter (fun A => A.card = t ∧ CutConnected G A)

/-- The standard m q^(2(t-1)) connected-set bound, including empty edge cases. -/
theorem connectedSets_card_le (G : SimpleGraph V) (q : ℕ)
    (hq : ∀ v, (neighbors G v).card ≤ q) (t : ℕ) :
    (connectedSets G t).card ≤ Fintype.card V * q ^ (2 * (t - 1)) := by
  classical
  let W := Finset.univ.biUnion (traces G (2 * (t - 1)))
  have hsub : connectedSets G t ⊆ W.image List.toFinset := by
    intro A hA
    obtain ⟨hcard, hconn⟩ := (Finset.mem_filter.mp hA).2
    obtain ⟨r, p, hp, hs⟩ := exists_tour hconn
    apply Finset.mem_image.mpr
    refine ⟨p.support, Finset.mem_biUnion.mpr ⟨r, Finset.mem_univ r, ?_⟩, hs⟩
    simpa only [hp, hcard] using walk_support_mem_traces p
  calc
    _ ≤ (W.image List.toFinset).card := Finset.card_le_card hsub
    _ ≤ W.card := Finset.card_image_le
    _ ≤ ∑ v : V, (traces G (2 * (t - 1)) v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v : V, q ^ (2 * (t - 1)) :=
      Finset.sum_le_sum (fun v _ => traces_card_le G q hq _ v)
    _ = _ := by simp

end

end BoundaryLab.ConnectedSetCounting
