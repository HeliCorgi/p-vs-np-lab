import ProofLab.ExpanderLocalConsistency
import Mathlib.Data.Fintype.BigOperators

/-!
# An unsatisfiable signing of any sufficiently dense proper 3-uniform support

There are exactly eight local sign patterns per clause. For each assignment,
seven of them satisfy the clause. Counting over all assignments proves the
existence of an unsatisfiable signing without any probabilistic hypothesis.
-/

namespace BoundaryLab.CNFSigning

noncomputable section

open scoped BigOperators

variable {I V : Type} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]

def Satisfiable (E : I → Finset V) (sign : I → V → Bool) : Prop :=
  ∃ x : V → Bool, ∀ i, ∃ v ∈ E i, x v = sign i v

theorem exists_unsatisfiable_signing (E : I → Finset V)
    (hwidth : ∀ i, (E i).card = 3) (hn : 0 < Fintype.card V)
    (hm : Fintype.card I = 12 * Fintype.card V) :
    ∃ sign : I → V → Bool, ¬ Satisfiable E sign := by
  classical
  let Pattern := fun i => (E i) → Bool
  let bad : (V → Bool) → (i : I) → Pattern i := fun x i v => !(x v)
  let good : (V → Bool) → Finset ((i : I) → Pattern i) := fun x =>
    Fintype.piFinset (fun i => Finset.univ.erase (bad x i))
  have hc (i : I) : Fintype.card (Pattern i) = 8 := by
    simp [Pattern, hwidth]
  have hg (x : V → Bool) : (good x).card = 7 ^ Fintype.card I := by
    simp [good, hc]
  have htotal : Fintype.card ((i : I) → Pattern i) = 8 ^ Fintype.card I := by
    simp [Fintype.card_pi, hc]
  let covered := (Finset.univ : Finset (V → Bool)).biUnion good
  have hcover : covered.card ≤ 2 ^ Fintype.card V * 7 ^ Fintype.card I := by
    calc
      covered.card ≤ ∑ x : V → Bool, (good x).card := Finset.card_biUnion_le
      _ = _ := by simp [hg]
  have hstrict : 2 ^ Fintype.card V * 7 ^ Fintype.card I < 8 ^ Fintype.card I := by
    rw [hm, pow_mul, pow_mul, ← mul_pow]
    exact pow_lt_pow_left₀ (by norm_num : (2 : ℕ) * 7 ^ 12 < 8 ^ 12) (by positivity) hn.ne'
  have hnotall : ¬ (Finset.univ : Finset ((i : I) → Pattern i)) ⊆ covered := by
    intro h
    have hh := Finset.card_le_card h
    rw [Finset.card_univ, htotal] at hh
    omega
  obtain ⟨σ, _, hσ⟩ := Finset.not_subset.mp hnotall
  let sign : I → V → Bool := fun i v => if hv : v ∈ E i then σ i ⟨v, hv⟩ else false
  refine ⟨sign, ?_⟩
  rintro ⟨x, hx⟩
  apply hσ
  apply Finset.mem_biUnion.mpr
  refine ⟨x, Finset.mem_univ _, Fintype.mem_piFinset.mpr ?_⟩
  intro i
  apply Finset.mem_erase.mpr
  refine ⟨?_, Finset.mem_univ _⟩
  intro heq
  obtain ⟨v, hv, hxv⟩ := hx i
  have hb := congrFun heq ⟨v, hv⟩
  have hs : x v = σ i ⟨v, hv⟩ := by simpa [sign, hv] using hxv
  change σ i ⟨v, hv⟩ = !(x v) at hb
  have hfalse : x v = !(x v) := hs.trans hb
  cases hvx : x v <;> simp only [hvx, Bool.not_false, Bool.not_true, Bool.false_eq_true,
    Bool.true_eq_false] at hfalse

omit [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V] in
theorem all_positive_satisfiable (E : I → Finset V)
    (hwidth : ∀ i, (E i).Nonempty) : Satisfiable E (fun _ _ => true) := by
  refine ⟨fun _ => true, ?_⟩
  intro i
  obtain ⟨v, hv⟩ := hwidth i
  exact ⟨v, hv, rfl⟩

end

end BoundaryLab.CNFSigning
