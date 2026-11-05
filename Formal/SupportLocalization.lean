import Formal.IntegerFeedback

/-! Components of the localization and coprime-gluing arguments. The CNF
repair lemma below is semantic. The rank theorem assumes subadditivity
and the expansion gap; it does not formalize the graph construction or
Hall's theorem. All integer statements include modulus zero. -/
set_option autoImplicit false

namespace BoundaryLab.SupportLocalization
open BoundaryLab.WitnessTransport

def Uses {V : Type} (c : Clause V) (x : V) : Prop :=
  Term.pos x ∈ c ∨ Term.neg x ∈ c

def setBit {V : Type} [DecidableEq V] (a : V → Bool) (x : V) (b : Bool) :
    V → Bool := fun y => if y = x then b else a y

private theorem stable {V : Type} [DecidableEq V] {c : Clause V} {x : V}
    (free : ¬ Uses c x) (a : V → Bool) (b : Bool) {l : Term V} (mem : l ∈ c) :
    eval (setBit a x b) l = eval a l := by
  cases l with
  | value _ => rfl
  | pos y =>
    have ne : y ≠ x := by
      intro h
      subst y
      exact free (Or.inl mem)
    simp [eval, setBit, ne]
  | neg y =>
    have ne : y ≠ x := by
      intro h
      subst y
      exact free (Or.inr mem)
    simp [eval, setBit, ne]

private theorem unchanged {V : Type} [DecidableEq V] {c : Clause V} {x : V}
    (free : ¬ Uses c x) (a : V → Bool) (b : Bool) :
    Holds (setBit a x b) c ↔ Holds a c := by
  constructor
  · rintro ⟨l, mem, val⟩
    exact ⟨l, mem, (stable free a b mem).symm.trans val⟩
  · rintro ⟨l, mem, val⟩
    exact ⟨l, mem, (stable free a b mem).trans val⟩

/-- A private variable absent from the target lets us delete its only source
clause without losing entailment. Thus it cannot occur in a minimal support. -/
theorem drop_private {V : Type} [DecidableEq V] (f : CNF V) (c target : Clause V)
    (x : V) (used : Uses c x) (rest : ∀ d ∈ f, ¬ Uses d x)
    (outside : ¬ Uses target x)
    (entails : ∀ a, Models a (c :: f) → Holds a target) :
    ∀ a, Models a f → Holds a target := by
  intro a model
  have repair : ∃ b, Holds (setBit a x b) c := by
    rcases used with pos | neg
    · exact ⟨true, Term.pos x, pos, by simp [eval, setBit]⟩
    · exact ⟨false, Term.neg x, neg, by simp [eval, setBit]⟩
  obtain ⟨b, hc⟩ := repair
  apply (unchanged outside a b).mp
  apply entails
  intro d member
  rcases List.mem_cons.mp member with h | h
  · subst d
    exact hc
  · exact (unchanged (rest d h) a b).mpr (model d h)

def Private {C V : Type} (occ : C → V → Prop) (u : C → Prop) (x : V) : Prop :=
  ∃ c, u c ∧ occ c x ∧ ∀ d, u d → occ d x → d = c

theorem boundary_union {C V : Type} (occ : C → V → Prop) (u v : C → Prop)
    (inside : V → Prop) (hu : ∀ x, Private occ u x → inside x)
    (hv : ∀ x, Private occ v x → inside x) :
    ∀ x, Private occ (fun c => u c ∨ v c) x → inside x := by
  rintro x ⟨c, member, hit, unique⟩
  rcases member with left | right
  · exact hu x ⟨c, left, hit, fun d hd h => unique d (Or.inl hd) h⟩
  · exact hv x ⟨c, right, hit, fun d hd h => unique d (Or.inr hd) h⟩

inductive Ranked (k s : Nat) : Nat → Prop where
  | source {r : Nat} (small : r ≤ 1) (gap : r ≤ s → r ≤ k) : Ranked k s r
  | weaken {i r : Nat} (parent : Ranked k s i) (small : r ≤ i) : Ranked k s r
  | binary {i j r : Nat} (left : Ranked k s i) (right : Ranked k s j)
      (subadd : r ≤ i + j) (gap : r ≤ s → r ≤ k) : Ranked k s r

/-- The support size cannot jump across the expansion gap in a binary proof. -/
theorem support_gap {k s r : Nat} (one : 1 ≤ s) (twice : k + k ≤ s)
    (tree : Ranked k s r) : r ≤ k := by
  induction tree with
  | source small gap => exact gap (Nat.le_trans small one)
  | weaken parent small ih => exact Nat.le_trans small ih
  | binary left right subadd gap ihLeft ihRight =>
    apply gap
    omega

/-- A full two-coordinate Boolean face isolates its mixed coefficient
by taking the alternating difference of four polynomial values. -/
theorem face_coefficient (m c u v z : Int)
    (h00 : m ∣ c) (h10 : m ∣ c + u) (h01 : m ∣ c + v)
    (h11 : m ∣ c + u + v + z) : m ∣ z := by
  have h := Int.dvd_add (Int.dvd_sub (Int.dvd_sub h11 h10) h01) h00
  have e : (c + u + v + z - (c + u) - (c + v)) + c = z := by omega
  rwa [e] at h

/-- Two scaled integer witnesses glue when their normalizations have a
Bezout combination equal to one. No nonnegativity is implied. -/
theorem glue_congruence (m a b u v x y r : Int) (norm : u*a + v*b = 1)
    (hx : m ∣ x - a*r) (hy : m ∣ y - b*r) : m ∣ u*x + v*y - r := by
  have scale (w t : Int) (ht : m ∣ t) : m ∣ w*t := by
    obtain ⟨k, hk⟩ := ht
    exact ⟨w*k, by rw [hk, ← Int.mul_assoc, Int.mul_comm w m, Int.mul_assoc]⟩
  have e : u*(a*r) + v*(b*r) = r := by
    rw [← Int.mul_assoc, ← Int.mul_assoc, ← Int.add_mul, norm, Int.one_mul]
  have total := Int.dvd_add (scale u _ hx) (scale v _ hy)
  have replaceSum : u*(x-a*r) + v*(y-b*r) = u*x + v*y - r := by
    rw [Int.mul_sub, Int.mul_sub]
    omega
  rwa [replaceSum] at total

/-- Integer arithmetic in the absorbed-set bound: |C| < 8 |A|. -/
theorem absorbed_size (t n fresh a : Nat) (expands : 7*t < 4*n)
    (deficient : 8*fresh ≤ 13*t) (removed : n ≤ fresh + a) : t < 8*a := by
  omega

/-- Fresh expansion 13/8 and at most three occurrences per clause leave
more than t/4 unique neighbors after the maintained assignment. -/
theorem residual_boundary (t n boundary : Nat) (fresh : 13*t < 8*n)
    (incidences : 2*n ≤ 3*t + boundary) : t < 4*boundary := by
  omega

/-- Evidence of k independent two-sided offers in a tree with n leaves.
A forced answer may discard the other subtree, but cannot shrink its parent. -/
inductive Offers : Nat → Nat → Prop where
  | terminal {n : Nat} (positive : 1 ≤ n) : Offers 0 n
  | forced {k n m : Nat} (child : Offers k n) (leaves : n ≤ m) : Offers k m
  | free {k l r : Nat} (left : Offers k l) (right : Offers k r) :
      Offers (k+1) (l+r)

theorem free_choice_leaves {k n : Nat} (proof : Offers k n) : 2^k ≤ n := by
  induction proof with
  | terminal positive => simpa using positive
  | forced child leaves ih => exact Nat.le_trans ih leaves
  | free left right ihLeft ihRight =>
    rw [Nat.pow_succ]
    omega

end BoundaryLab.SupportLocalization
