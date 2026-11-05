/-
Weighted replay of a finite semantic DAG in ordinary polynomial calculus.

All proof lines below are ordinary multivariate polynomials over ZMod 2.
Boolean identities are derived from the explicit Boolean axioms, via the
same-degree NS certificate and the proved NS-to-PC inclusion. The completed
line multiplication lemma expands into the primitive variable rule; no
quotient-ring reduction or semantic inference rule is added to Derives.

This file formalizes the replay layer of docs/affine_dag_annihilator.md,
Sections 2--4. It does not prove a separated-space construction, a dimension
bound for affine restrictions, or any conclusion about P versus NP.
-/
import claims.BooleanReduction

set_option autoImplicit false

namespace BoundaryLab.MaskedDAG

noncomputable section

open MvPolynomial MathResearch.PolynomialCalculus

variable {V : Type} {S k R : ℕ}

/-- A sound input, unary inference, or binary inference. Zero evaluation means
the corresponding clause is satisfied. Strictly earlier parent indices permit
arbitrary sharing of previous nodes. -/
inductive SemanticStep (F : Set (Poly (ZMod 2) V))
    (q : Fin S → Poly (ZMod 2) V) (i : Fin S) : Prop
  | input (member : q i ∈ F) : SemanticStep F q i
  | unary (parent : Fin S) (earlier : parent.val < i.val)
      (sound : ∀ x : V → ZMod 2,
        eval x (q parent) = 0 → eval x (q i) = 0) : SemanticStep F q i
  | binary (left right : Fin S)
      (earlierLeft : left.val < i.val) (earlierRight : right.val < i.val)
      (sound : ∀ x : V → ZMod 2,
        eval x (q left) = 0 → eval x (q right) = 0 → eval x (q i) = 0) :
      SemanticStep F q i

/-- The order is part of the data; there is no restriction on DAG depth,
parent reuse, or the number of children of a node. -/
def SemanticDAG (F : Set (Poly (ZMod 2) V))
    (q : Fin S → Poly (ZMod 2) V) : Prop :=
  ∀ i, SemanticStep F q i

variable [Fintype V] [DecidableEq V]

/-- A polynomial that vanishes on the Boolean cube has an ordinary-PC
derivation at its stated ordinary degree, when the explicit Boolean axioms
are available. This uses only NS ⊆ PC, never the converse. -/
theorem boolean_zero_pc {F : Set (Poly (ZMod 2) V)}
    (hbool : (booleanBase : Set (Poly (ZMod 2) V)) ⊆ F)
    {p : Poly (ZMod 2) V} {D : ℕ}
    (hdegree : p.totalDegree ≤ D)
    (hvanish : ∀ x : V → ZMod 2, eval x p = 0) : Derives F D p := by
  have hn : p ∈ nsSpace (booleanBase : Set (Poly (ZMod 2) V)) D :=
    boolean_vanishing_ns_bound p D hdegree hvanish
  have hp : Derives (booleanBase : Set (Poly (ZMod 2) V)) D p :=
    nsSpace_le_pcSpace booleanBase D hn
  exact hp.mono hbool le_rfl

private theorem zero_or_one (z : ZMod 2) : z = 0 ∨ z = 1 := by
  fin_cases z <;> simp

private theorem one_sub_degree (p : Poly (ZMod 2) V) :
    (1 - p).totalDegree ≤ p.totalDegree := by
  simpa using totalDegree_sub (1 : Poly (ZMod 2) V) p

private theorem mul_degree_le {p q : Poly (ZMod 2) V} {a b : ℕ}
    (hp : p.totalDegree ≤ a) (hq : q.totalDegree ≤ b) :
    (p * q).totalDegree ≤ a + b :=
  (totalDegree_mul p q).trans (Nat.add_le_add hp hq)

/-- Reuse the completed line, preserving the old proof ceiling. -/
private theorem completed_mul {F : Set (Poly (ZMod 2) V)} {D : ℕ}
    {p q : Poly (ZMod 2) V} (hp : Derives F D p)
    (hdegree : q.totalDegree + p.totalDegree ≤ D) :
    Derives F D (q * p) :=
  (hp.mul_polynomial q).mono (fun _ h => h) (max_le le_rfl hdegree)

private theorem weighted_input {F : Set (Poly (ZMod 2) V)}
    {f a : Poly (ZMod 2) V} (hf : f.totalDegree ≤ k)
    (ha : a.totalDegree ≤ R) (hinput : a ∈ F) :
    Derives F (k + 3 * R) (f * a) := by
  have hp : Derives F R a := .hyp hinput ha
  exact (hp.mul_polynomial f).mono (fun _ h => h) (by omega)

/-- Both retained parents: the correction has ordinary degree at most k+3R.
The formulas are polynomial identities before any Boolean reduction. -/
private theorem weighted_low_low {F : Set (Poly (ZMod 2) V)}
    (hbool : (booleanBase : Set (Poly (ZMod 2) V)) ⊆ F)
    {f a b c : Poly (ZMod 2) V}
    (hf : f.totalDegree ≤ k) (ha : a.totalDegree ≤ R)
    (hb : b.totalDegree ≤ R) (hc : c.totalDegree ≤ R)
    (hsound : ∀ x : V → ZMod 2,
      eval x a = 0 → eval x b = 0 → eval x c = 0)
    (hpa : Derives F (k + 3 * R) (f * a))
    (hpb : Derives F (k + 3 * R) (f * b)) :
    Derives F (k + 3 * R) (f * c) := by
  have hfa := mul_degree_le hf ha
  have hfb := mul_degree_le hf hb
  have hca := mul_degree_le ((one_sub_degree a).trans ha) hc
  have hfirst : Derives F (k + 3 * R) (c * (f * a)) :=
    completed_mul hpa (by omega)
  have hsecond : Derives F (k + 3 * R) (((1 - a) * c) * (f * b)) :=
    completed_mul hpb (by omega)
  have hfc := mul_degree_le hf hc
  have hfca := mul_degree_le hfc ((one_sub_degree a).trans ha)
  have hfcab := mul_degree_le hfca ((one_sub_degree b).trans hb)
  have hcorrection : Derives F (k + 3 * R) (f * c * (1 - a) * (1 - b)) := by
    apply boolean_zero_pc hbool (by omega)
    intro x
    rcases zero_or_one (eval x a) with ha0 | ha1
    · rcases zero_or_one (eval x b) with hb0 | hb1
      · simp [map_mul, map_sub, ha0, hb0, hsound x ha0 hb0]
      · simp [map_mul, map_sub, hb1]
    · simp [map_mul, map_sub, ha1]
  have hid : c * (f * a) + ((1 - a) * c) * (f * b) +
      f * c * (1 - a) * (1 - b) = f * c := by ring
  rw [← hid]
  exact .add (.add hfirst hsecond) hcorrection

/-- A discarded first parent is used only through the vanishing of the one
common mask. Its degree and a derivation of its weighted line are not assumed. -/
private theorem weighted_high_low {F : Set (Poly (ZMod 2) V)}
    (hbool : (booleanBase : Set (Poly (ZMod 2) V)) ⊆ F)
    {f a b c : Poly (ZMod 2) V}
    (hf : f.totalDegree ≤ k) (hb : b.totalDegree ≤ R)
    (hc : c.totalDegree ≤ R)
    (hsound : ∀ x : V → ZMod 2,
      eval x a = 0 → eval x b = 0 → eval x c = 0)
    (hkill : ∀ x : V → ZMod 2, eval x a ≠ 0 → eval x f = 0)
    (hpb : Derives F (k + 3 * R) (f * b)) :
    Derives F (k + 3 * R) (f * c) := by
  have hfb := mul_degree_le hf hb
  have hfirst : Derives F (k + 3 * R) (c * (f * b)) :=
    completed_mul hpb (by omega)
  have hfc := mul_degree_le hf hc
  have hfcb := mul_degree_le hfc ((one_sub_degree b).trans hb)
  have hcorrection : Derives F (k + 3 * R) (f * c * (1 - b)) := by
    apply boolean_zero_pc hbool (by omega)
    intro x
    by_cases hb0 : eval x b = 0
    · by_cases ha0 : eval x a = 0
      · simp [map_mul, map_sub, hsound x ha0 hb0]
      · simp [map_mul, map_sub, hkill x ha0]
    · have hb1 : eval x b = 1 := (zero_or_one (eval x b)).resolve_left hb0
      simp [map_mul, map_sub, hb1]
  have hid : c * (f * b) + f * c * (1 - b) = f * c := by ring
  rw [← hid]
  exact .add hfirst hcorrection

/-- With two discarded parents, the whole weighted conclusion vanishes. -/
private theorem weighted_high_high {F : Set (Poly (ZMod 2) V)}
    (hbool : (booleanBase : Set (Poly (ZMod 2) V)) ⊆ F)
    {f a b c : Poly (ZMod 2) V}
    (hf : f.totalDegree ≤ k) (hc : c.totalDegree ≤ R)
    (hsound : ∀ x : V → ZMod 2,
      eval x a = 0 → eval x b = 0 → eval x c = 0)
    (hkillA : ∀ x : V → ZMod 2, eval x a ≠ 0 → eval x f = 0)
    (hkillB : ∀ x : V → ZMod 2, eval x b ≠ 0 → eval x f = 0) :
    Derives F (k + 3 * R) (f * c) := by
  have hfc := mul_degree_le hf hc
  apply boolean_zero_pc hbool (by omega)
  intro x
  by_cases ha0 : eval x a = 0
  · by_cases hb0 : eval x b = 0
    · simp [map_mul, hsound x ha0 hb0]
    · simp [map_mul, hkillB x hb0]
  · simp [map_mul, hkillA x ha0]

/-- The induction can use either an already derived retained line or the
semantic vanishing supplied for a discarded line. -/
private def ParentReady (F : Set (Poly (ZMod 2) V))
    (f : Poly (ZMod 2) V) (R D : ℕ) (p : Poly (ZMod 2) V) : Prop :=
  (p.totalDegree ≤ R ∧ Derives F D (f * p)) ∨
    (∀ x : V → ZMod 2, eval x p ≠ 0 → eval x f = 0)

private theorem weighted_binary {F : Set (Poly (ZMod 2) V)}
    (hbool : (booleanBase : Set (Poly (ZMod 2) V)) ⊆ F)
    {f a b c : Poly (ZMod 2) V}
    (hf : f.totalDegree ≤ k) (hc : c.totalDegree ≤ R)
    (hsound : ∀ x : V → ZMod 2,
      eval x a = 0 → eval x b = 0 → eval x c = 0)
    (ha : ParentReady F f R (k + 3 * R) a)
    (hb : ParentReady F f R (k + 3 * R) b) :
    Derives F (k + 3 * R) (f * c) := by
  rcases ha with ⟨haDegree, haProof⟩ | haKill
  · rcases hb with ⟨hbDegree, hbProof⟩ | hbKill
    · exact weighted_low_low hbool hf haDegree hbDegree hc hsound haProof hbProof
    · exact weighted_high_low hbool hf haDegree hc
        (fun x hb0 ha0 => hsound x ha0 hb0) hbKill haProof
  · rcases hb with ⟨hbDegree, hbProof⟩ | hbKill
    · exact weighted_high_low hbool hf hbDegree hc hsound haKill hbProof
    · exact weighted_high_high hbool hf hc hsound haKill hbKill

/-- Weighted replay on all retained nodes. One polynomial `f` must vanish on
the falsity set of every discarded node. Only retained nodes need a degree
bound. Inputs are the actual polynomials in `F`, and arbitrary earlier lines
may be reused. All naturals, including k=0 and R=0, are allowed.

The statement does not require inputs to be retained: a discarded input is
covered by the same vanishing hypothesis as any other discarded node. -/
theorem replay_low_nodes {F : Set (Poly (ZMod 2) V)}
    (hbool : (booleanBase : Set (Poly (ZMod 2) V)) ⊆ F)
    {q : Fin S → Poly (ZMod 2) V} (dag : SemanticDAG F q)
    (Low : Fin S → Prop) {f : Poly (ZMod 2) V}
    (hf : f.totalDegree ≤ k)
    (hdegree : ∀ i, Low i → (q i).totalDegree ≤ R)
    (hvanish : ∀ i, ¬ Low i → ∀ x : V → ZMod 2,
      eval x (q i) ≠ 0 → eval x f = 0) :
    ∀ i, Low i → Derives F (k + 3 * R) (f * q i) := by
  classical
  have replay : ∀ t : ℕ, ∀ i : Fin S, i.val = t →
      Low i → Derives F (k + 3 * R) (f * q i) := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro i hi hlow
      have ready : ∀ j : Fin S, j.val < i.val →
          ParentReady F f R (k + 3 * R) (q j) := by
        intro j hj
        by_cases hjlow : Low j
        · exact Or.inl ⟨hdegree j hjlow, ih j.val (by omega) j rfl hjlow⟩
        · exact Or.inr (hvanish j hjlow)
      cases dag i with
      | input hinput =>
        exact weighted_input hf (hdegree i hlow) hinput
      | unary parent hearlier hsound =>
        exact weighted_binary hbool hf (hdegree i hlow)
          (fun x hparent _ => hsound x hparent)
          (ready parent hearlier) (ready parent hearlier)
      | binary left right hearlierLeft hearlierRight hsound =>
        exact weighted_binary hbool hf (hdegree i hlow) hsound
          (ready left hearlierLeft) (ready right hearlierRight)
  intro i hlow
  exact replay i.val i rfl hlow

/-- A final falsity polynomial equal to one yields a derivation of the common
mask. If the final node was discarded, the mask vanishes everywhere, which
is itself handled by the explicit Boolean axioms at degree k. -/
theorem masked_dag_replay {F : Set (Poly (ZMod 2) V)}
    (hbool : (booleanBase : Set (Poly (ZMod 2) V)) ⊆ F)
    {q : Fin S → Poly (ZMod 2) V} (dag : SemanticDAG F q)
    (Low : Fin S → Prop) {f : Poly (ZMod 2) V}
    (hf : f.totalDegree ≤ k)
    (hdegree : ∀ i, Low i → (q i).totalDegree ≤ R)
    (hvanish : ∀ i, ¬ Low i → ∀ x : V → ZMod 2,
      eval x (q i) ≠ 0 → eval x f = 0)
    (finish : Fin S) (hfinish : q finish = 1) :
    Derives F (k + 3 * R) f := by
  classical
  by_cases hlow : Low finish
  · simpa only [hfinish, mul_one] using
      replay_low_nodes hbool dag Low hf hdegree hvanish finish hlow
  · have hzero : ∀ x : V → ZMod 2, eval x f = 0 := by
      intro x
      exact hvanish finish hlow x (by simp [hfinish])
    exact (boolean_zero_pc hbool hf hzero).mono (fun _ h => h) (by omega)

/-- Submodule form for the kernel-to-PC step in the dimension argument. -/
theorem masked_dag_mem_pcSpace {F : Set (Poly (ZMod 2) V)}
    (hbool : (booleanBase : Set (Poly (ZMod 2) V)) ⊆ F)
    {q : Fin S → Poly (ZMod 2) V} (dag : SemanticDAG F q)
    (Low : Fin S → Prop) {f : Poly (ZMod 2) V}
    (hf : f.totalDegree ≤ k)
    (hdegree : ∀ i, Low i → (q i).totalDegree ≤ R)
    (hvanish : ∀ i, ¬ Low i → ∀ x : V → ZMod 2,
      eval x (q i) ≠ 0 → eval x f = 0)
    (finish : Fin S) (hfinish : q finish = 1) :
    f ∈ pcSpace F (k + 3 * R) :=
  masked_dag_replay hbool dag Low hf hdegree hvanish finish hfinish

end

end BoundaryLab.MaskedDAG
