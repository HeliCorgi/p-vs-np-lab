import Formal.WitnessTransport

/-! A semantic kernel for local Boolean truth tables and modular row proofs.
No field conversion is applied to a row. The cross-field rule requires a
Boolean implication; the proof of the summation rule below uses only addition
with zero, distributivity and interchange. The concrete contradiction theorems
instantiate these finite arithmetic laws at moduli 3 and 4 by kernel computation.
It is not a formalization of scope discovery or Python's Gaussian elimination. -/
set_option autoImplicit false

namespace BoundaryLab.ModularHull
open WitnessTransport

structure Eqn (V R : Type) where
  coeff : V → R
  rhs : R

def dot {V R : Type} [Zero R] [Add R] (a : V → Bool) (c : V → R) : List V → R
  | [] => 0
  | v :: rest => if a v then c v + dot a c rest else dot a c rest

def Valid {V R : Type} [Zero R] [Add R] (vs : List V) (a : V → Bool) (r : Eqn V R) : Prop :=
  dot a r.coeff vs = r.rhs

/-- A table checked against clauses selected from the original formula may
be applied to the actual bits in any global Boolean model of that formula. -/
theorem local_table_sound {I V R : Type} [Zero R] [Add R]
    (f : CNF V) (g : CNF I) (sigma : I → Term V)
    (selected : ∀ c ∈ g, c.map (pull sigma) ∈ f)
    (vs : List I) (r : Eqn I R) (checked : ∀ b, Models b g → Valid vs b r)
    (a : V → Bool) (model : Models a f) : Valid vs (lift sigma a) r := by
  apply checked
  intro c hc
  obtain ⟨u, hu, yes⟩ := model _ (selected c hc)
  obtain ⟨v, hv, eq⟩ := List.mem_map.mp hu
  rw [← eq] at yes
  exact ⟨v,hv,(eval_pull sigma a v).symm.trans yes⟩

def sumCoeff {V R : Type} [Zero R] [Add R] [Mul R] :
    List (R × Eqn V R) → V → R
  | [], _ => 0
  | t :: rest, v => t.1 * t.2.coeff v + sumCoeff rest v

def sumRhs {V R : Type} [Zero R] [Add R] [Mul R] : List (R × Eqn V R) → R
  | [] => 0
  | t :: rest => t.1 * t.2.rhs + sumRhs rest

private theorem dot_zero {V R : Type} [Zero R] [Add R] (zz : (0:R) + 0 = 0)
    (a : V → Bool) (vs : List V) : dot a (fun _ => (0:R)) vs = 0 := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    cases h : a v <;> simp [dot,h,ih,zz]

private theorem dot_add {V R : Type} [Zero R] [Add R] (zz : (0:R) + 0 = 0)
    (swap : ∀ x y z w : R, (x+y)+(z+w) = (x+z)+(y+w))
    (a : V → Bool) (c d : V → R) (vs : List V) :
    dot a (fun v => c v + d v) vs = dot a c vs + dot a d vs := by
  induction vs with
  | nil => exact zz.symm
  | cons v vs ih =>
    cases h : a v with
    | false => simpa [dot,h] using ih
    | true => simpa [dot,h,ih] using swap (c v) (d v) (dot a c vs) (dot a d vs)

private theorem dot_mul {V R : Type} [Zero R] [Add R] [Mul R]
    (mz : ∀ k : R, k * 0 = 0)
    (dist : ∀ k x y : R, k*(x+y) = k*x + k*y)
    (a : V → Bool) (k : R) (c : V → R) (vs : List V) :
    dot a (fun v => k * c v) vs = k * dot a c vs := by
  induction vs with
  | nil => exact (mz k).symm
  | cons v vs ih =>
    cases h : a v with
    | false => simpa [dot,h] using ih
    | true => simpa [dot,h,ih] using (dist k (c v) (dot a c vs)).symm

theorem weighted_sum_sound {V R : Type} [Zero R] [Add R] [Mul R]
    (zz : (0:R) + 0 = 0) (mz : ∀ k : R, k*0 = 0)
    (swap : ∀ x y z w : R, (x+y)+(z+w) = (x+z)+(y+w))
    (dist : ∀ k x y : R, k*(x+y) = k*x + k*y) (vs : List V)
    (a : V → Bool) (ts : List (R × Eqn V R))
    (ok : ∀ t ∈ ts, Valid vs a t.2) : dot a (sumCoeff ts) vs = sumRhs ts := by
  induction ts with
  | nil => exact dot_zero zz a vs
  | cons t ts ih =>
    have first : dot a t.2.coeff vs = t.2.rhs := ok t (by simp)
    have tail := ih (fun u hu => ok u (List.mem_cons_of_mem _ hu))
    change dot a (fun v => t.1*t.2.coeff v + sumCoeff ts v) vs = t.1*t.2.rhs + sumRhs ts
    rw [dot_add zz swap, dot_mul mz dist, first, tail]

/-- Per-variable cancellation with nonzero RHS refutes original models. -/
theorem mod_three_refutes {V : Type} (f : CNF V) (vs : List V)
    (ts : List (Fin 3 × Eqn V (Fin 3)))
    (ok : ∀ a, Models a f → ∀ t ∈ ts, Valid vs a t.2)
    (cancel : ∀ v, sumCoeff ts v = 0) (one : sumRhs ts = 1) :
    ¬ Sat f := by
  intro sat
  obtain ⟨a,model⟩ := sat
  have sh : ∀ x y z w : Fin 3, (x+y)+(z+w) = (x+z)+(y+w) := by decide
  have di : ∀ k x y : Fin 3, k*(x+y) = k*x + k*y := by decide
  have mz : ∀ k : Fin 3, k*0 = 0 := by decide
  have eq := weighted_sum_sound (by decide : (0:Fin 3)+0=0) mz sh di vs a ts (ok a model)
  have co : sumCoeff ts = (fun _ => 0) := funext cancel
  rw [co, dot_zero (by decide : (0:Fin 3)+0=0), one] at eq
  exact (by decide : (0:Fin 3) ≠ 1) eq

/-- Over the composite modulus, 0=2 is already a contradiction: nothing
in this theorem divides by a putative nonzero pivot. -/
theorem mod_four_refutes {V : Type} (f : CNF V) (vs : List V)
    (ts : List (Fin 4 × Eqn V (Fin 4)))
    (ok : ∀ a, Models a f → ∀ t ∈ ts, Valid vs a t.2)
    (cancel : ∀ v, sumCoeff ts v = 0) (nonzero : sumRhs ts ≠ 0) :
    ¬ Sat f := by
  intro sat
  obtain ⟨a,model⟩ := sat
  have sh : ∀ x y z w : Fin 4, (x+y)+(z+w) = (x+z)+(y+w) := by decide
  have di : ∀ k x y : Fin 4, k*(x+y) = k*x + k*y := by decide
  have mz : ∀ k : Fin 4, k*0 = 0 := by decide
  have eq := weighted_sum_sound (by decide : (0:Fin 4)+0=0) mz sh di vs a ts (ok a model)
  have co : sumCoeff ts = (fun _ => 0) := funext cancel
  rw [co, dot_zero (by decide : (0:Fin 4)+0=0)] at eq
  exact nonzero eq.symm

/-- A bridge can change arithmetic domains only through an explicitly checked
implication on the SAME Boolean words. The two row codomains can differ. -/
theorem boolean_bridge_sound {I R S : Type} [Zero R] [Add R] [Zero S] [Add S]
    (vs : List I) (premises : List (Eqn I R)) (target : Eqn I S)
    (checked : ∀ b : I → Bool, (∀ r ∈ premises, Valid vs b r) → Valid vs b target)
    (actual : I → Bool) (known : ∀ r ∈ premises, Valid vs actual r) : Valid vs actual target :=
  checked actual known

end BoundaryLab.ModularHull
