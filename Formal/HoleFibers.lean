import Formal.AffineFrontier

/-!
# Puncturing two XOR summands

The elementary witness facts used when a flat is stored with one forbidden
point. The last theorem assumes closure under the supplied direction and
the two-pair description of equal-sum fibers; it does not prove those rank
conditions, check the Python linear algebra, or formalize the running time.
-/
set_option autoImplicit false

namespace BoundaryLab.HoleFibers

private theorem one_of_two {X Y : Type} (a b h : X) (u v k : Y)
    (ha : a ≠ h) (hb : b ≠ h) (huv : u ≠ v) :
    (a ≠ h ∧ u ≠ k) ∨ (b ≠ h ∧ v ≠ k) := by
  classical
  by_cases hu : u = k
  · exact Or.inr ⟨hb, fun hv => huv (hu.trans hv.symm)⟩
  · exact Or.inl ⟨ha, hu⟩

/-- At most one point per side is forbidden. Three decompositions with
pairwise distinct lefts and pairwise distinct rights cannot all be blocked. -/
theorem three_pairs_escape {X Y : Type} (a b c h : X) (u v w k : Y)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    (a ≠ h ∧ u ≠ k) ∨ (b ≠ h ∧ v ≠ k) ∨ (c ≠ h ∧ w ≠ k) := by
  classical
  by_cases ha : a = h
  · exact Or.inr (one_of_two b c h v w k (fun hb => hab (ha.trans hb.symm))
      (fun hc => hac (ha.trans hc.symm)) hvw)
  · by_cases hb : b = h
    · rcases one_of_two a c h u w k ha (fun hc => hbc (hb.trans hc.symm)) huw with p | p
      · exact Or.inl p
      · exact Or.inr (Or.inr p)
    · rcases one_of_two a b h u v k ha hb huv with p | p
      · exact Or.inl p
      · exact Or.inr (Or.inl p)

/-- The two-pair fiber loses both choices precisely when the two holes cross. -/
theorem two_pairs_blocked_iff_cross {X Y : Type} (a b h : X) (u v k : Y)
    (hab : a ≠ b) (huv : u ≠ v) :
    (¬ ((a ≠ h ∧ u ≠ k) ∨ (b ≠ h ∧ v ≠ k))) ↔
      (a = h ∧ v = k) ∨ (b = h ∧ u = k) := by
  classical
  constructor
  · intro blocked
    by_cases ha : a = h
    · have hb : b ≠ h := fun h' => hab (ha.trans h'.symm)
      by_cases hv : v = k
      · exact Or.inl ⟨ha, hv⟩
      · exact False.elim (blocked (Or.inr ⟨hb, hv⟩))
    · by_cases hu : u = k
      · have hv : v ≠ k := fun h' => huv (hu.trans h'.symm)
        by_cases hb : b = h
        · exact Or.inr ⟨hb, hu⟩
        · exact False.elim (blocked (Or.inr ⟨hb, hv⟩))
      · exact False.elim (blocked (Or.inl ⟨ha, hu⟩))
  · intro cross good
    rcases cross with ⟨ha, hv⟩ | ⟨hb, hu⟩
    · rcases good with p | p
      · exact p.1 ha
      · exact p.2 hv
    · rcases good with p | p
      · exact p.2 hu
      · exact p.1 hb

open BoundaryLab.AffineFrontier (Mask plus)

private theorem shift_twice {ι : Type} (x d : Mask ι) : plus (plus x d) d = x := by
  funext i
  change Bool.xor (Bool.xor (x i) (d i)) (d i) = x i
  cases x i <;> cases d i <;> rfl

private theorem shift_both {ι : Type} (x y d : Mask ι) :
    plus (plus x d) (plus y d) = plus x y := by
  funext i
  change Bool.xor (Bool.xor (x i) (d i)) (Bool.xor (y i) (d i)) = Bool.xor (x i) (y i)
  cases x i <;> cases y i <;> cases d i <;> rfl

private theorem shift_right {ι : Type} (x y d : Mask ι) :
    plus x (plus y d) = plus (plus x y) d := by
  funext i
  change Bool.xor (x i) (Bool.xor (y i) (d i)) = Bool.xor (Bool.xor (x i) (y i)) (d i)
  cases x i <;> cases y i <;> cases d i <;> rfl

private theorem shift_left {ι : Type} (x y d : Mask ι) :
    plus (plus x d) y = plus (plus x y) d := by
  funext i
  change Bool.xor (Bool.xor (x i) (d i)) (y i) = Bool.xor (Bool.xor (x i) (y i)) (d i)
  cases x i <;> cases y i <;> cases d i <;> rfl

/-- On an attainable target with exactly the stated two-point fibers, removing
one allowed point `h` and `k` in the two summands removes exactly `h XOR k XOR d`.
Here `moved` expresses that the supplied shift is fixed-point-free. -/
theorem two_point_fiber_puncture {ι : Type} (A B : Mask ι → Prop) (h k d t : Mask ι)
    (hh : A h) (hk : B k) (moved : ∀ x, x ≠ plus x d)
    (leftClosed : ∀ x, A x → A (plus x d)) (rightClosed : ∀ y, B y → B (plus y d))
    (fiber : ∀ x y a b, A x → B y → A a → B b → plus x y = plus a b →
      (x = a ∧ y = b) ∨ (x = plus a d ∧ y = plus b d))
    (attainable : ∃ x y, A x ∧ B y ∧ plus x y = t) :
    (∃ x y, A x ∧ B y ∧ x ≠ h ∧ y ≠ k ∧ plus x y = t) ↔
      t ≠ plus (plus h k) d := by
  classical
  constructor
  · intro witness bad
    obtain ⟨x, y, hx, hy, nx, ny, hxy⟩ := witness
    have same : plus x y = plus h (plus k d) :=
      hxy.trans (bad.trans (shift_right h k d).symm)
    rcases fiber x y h (plus k d) hx hy hh (rightClosed k hk) same with p | p
    · exact nx p.1
    · exact ny (p.2.trans (shift_twice k d))
  · intro notBad
    obtain ⟨x, y, hx, hy, hxy⟩ := attainable
    by_cases good : (x ≠ h ∧ y ≠ k) ∨ (plus x d ≠ h ∧ plus y d ≠ k)
    · rcases good with p | p
      · exact ⟨x, y, hx, hy, p.1, p.2, hxy⟩
      · exact ⟨plus x d, plus y d, leftClosed x hx, rightClosed y hy,
          p.1, p.2, (shift_both x y d).trans hxy⟩
    · rcases (two_pairs_blocked_iff_cross x (plus x d) h y (plus y d) k
        (moved x) (moved y)).mp good with ⟨hl, hr⟩ | ⟨hl, hr⟩
      · apply False.elim
        apply notBad
        rw [← hl, ← hr, ← shift_right, shift_twice]
        exact hxy.symm
      · apply False.elim
        apply notBad
        rw [← hl, ← hr, ← shift_left, shift_twice]
        exact hxy.symm

end BoundaryLab.HoleFibers
