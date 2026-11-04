import Formal.ModularHull

/-!
# Integer congruence certificates and conditional refutation

The modulus is an arbitrary integer, not a preselected prime.  Modulus zero
means exact equality.  Local truth-table checking and the discovery of the
integer row combination remain outside this file.  The premises below are
exactly the semantic obligations that the independent Python checker checks.
No division by a nonunit, Smith algorithm, or running-time bound is assumed.
-/

set_option autoImplicit false

namespace BoundaryLab.IntegerCertificate

open BoundaryLab.WitnessTransport
open BoundaryLab.ModularHull (dot)

structure Row (V : Type) where
  coeff : V → Int
  rhs : Int
  modulus : Int

def Holds {V : Type} (vs : List V) (a : V → Bool) (r : Row V) : Prop :=
  r.modulus ∣ dot a r.coeff vs - r.rhs

def coefficients {V : Type} : List (Int × Row V) → V → Int
  | [], _ => 0
  | t :: ts, v => t.1 * t.2.coeff v + coefficients ts v

def rightSides {V : Type} : List (Int × Row V) → Int
  | [] => 0
  | t :: ts => t.1 * t.2.rhs + rightSides ts

def errors {V : Type} (vs : List V) (a : V → Bool) : List (Int × Row V) → Int
  | [] => 0
  | t :: ts => t.1 * (dot a t.2.coeff vs - t.2.rhs) + errors vs a ts

private theorem dot_add {V : Type} (vs : List V) (a : V → Bool) (c d : V → Int) :
    dot a (fun v => c v + d v) vs = dot a c vs + dot a d vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    cases h : a v <;> simp [dot, h, ih] <;> omega

private theorem dot_scale {V : Type} (vs : List V) (a : V → Bool)
    (w : Int) (c : V → Int) :
    dot a (fun v => w * c v) vs = w * dot a c vs := by
  induction vs with
  | nil => simp [dot]
  | cons v vs ih =>
    cases h : a v <;> simp [dot, h, ih, Int.mul_add]

private theorem dot_zero {V : Type} (vs : List V) (a : V → Bool) :
    dot a (fun _ => (0 : Int)) vs = 0 := by
  induction vs with
  | nil => rfl
  | cons v vs ih => cases h : a v <;> simp [dot, h, ih]

private theorem error_identity {V : Type} (vs : List V) (a : V → Bool)
    (ts : List (Int × Row V)) :
    errors vs a ts = dot a (coefficients ts) vs - rightSides ts := by
  induction ts with
  | nil => simp [errors, coefficients, rightSides, dot_zero]
  | cons t ts ih =>
    change t.1 * (dot a t.2.coeff vs - t.2.rhs) + errors vs a ts =
      dot a (fun v => t.1 * t.2.coeff v + coefficients ts v) vs -
        (t.1 * t.2.rhs + rightSides ts)
    rw [dot_add, dot_scale, ih, Int.mul_sub]
    omega

/-- A congruence of modulus d can be used at modulus m with weight w only
when m divides w*d.  This includes d=0, namely a local exact equality. -/
theorem scale_congruence (m d w u b : Int)
    (local : d ∣ u - b) (compatible : m ∣ w * d) :
    m ∣ w * (u - b) := by
  obtain ⟨k, hk⟩ := local
  obtain ⟨q, hq⟩ := compatible
  refine ⟨q * k, ?_⟩
  rw [hk, ← Int.mul_assoc, hq, Int.mul_assoc]

private theorem errors_divisible {V : Type} (vs : List V) (a : V → Bool)
    (m : Int) (ts : List (Int × Row V))
    (valid : ∀ t ∈ ts, Holds vs a t.2)
    (compatible : ∀ t ∈ ts, m ∣ t.1 * t.2.modulus) :
    m ∣ errors vs a ts := by
  induction ts with
  | nil => exact ⟨0, by simp [errors]⟩
  | cons t ts ih =>
    apply Int.dvd_add
    · exact scale_congruence m t.2.modulus t.1 (dot a t.2.coeff vs) t.2.rhs
        (valid t (by simp)) (compatible t (by simp))
    · exact ih (fun u hu => valid u (List.mem_cons_of_mem _ hu))
        (fun u hu => compatible u (List.mem_cons_of_mem _ hu))

private theorem dot_divisible {V : Type} (vs : List V) (a : V → Bool)
    (m : Int) (c : V → Int) (divides : ∀ v, m ∣ c v) : m ∣ dot a c vs := by
  induction vs with
  | nil => exact ⟨0, by simp [dot]⟩
  | cons v vs ih =>
    cases h : a v
    · simpa [dot, h] using ih
    · simpa [dot, h] using Int.dvd_add (divides v) ih

/-- Independently valid local laws, a legal change of modulus, and coefficient
cancellation modulo m refute the original formula when the RHS is not divisible
by m.  Composite and dynamically discovered moduli are allowed; m=0 also works. -/
theorem integer_certificate_refutes {V : Type} (f : CNF V) (vs : List V)
    (m : Int) (ts : List (Int × Row V))
    (valid : ∀ a, Models a f → ∀ t ∈ ts, Holds vs a t.2)
    (compatible : ∀ t ∈ ts, m ∣ t.1 * t.2.modulus)
    (cancel : ∀ v, m ∣ coefficients ts v)
    (contradiction : ¬ m ∣ rightSides ts) : ¬ Sat f := by
  rintro ⟨a, model⟩
  have h := errors_divisible vs a m ts (valid a model) compatible
  rw [error_identity] at h
  have hdot := dot_divisible vs a m (coefficients ts) cancel
  have hb := Int.dvd_sub hdot h
  have eq : dot a (coefficients ts) vs -
      (dot a (coefficients ts) vs - rightSides ts) = rightSides ts := by omega
  rw [eq] at hb
  exact contradiction hb

/-- If one Boolean value has a refutation, every model must take the other.
The conditional proof may use any sound arithmetic certificate. -/
theorem refuted_value_forces {V : Type} (f : CNF V) (v : V) (b : Bool)
    (refuted : ¬ ∃ a, Models a f ∧ a v = b) :
    ∀ a, Models a f → a v = !b := by
  intro a ha
  have hn : a v ≠ b := fun h => refuted ⟨a, ha, h⟩
  cases b <;> cases h : a v <;> simp_all

/-- Two checked conditional refutations eliminate the split altogether. -/
theorem both_values_refute {V : Type} (f : CNF V) (v : V)
    (zero : ¬ ∃ a, Models a f ∧ a v = false)
    (one : ¬ ∃ a, Models a f ∧ a v = true) : ¬ Sat f := by
  rintro ⟨a, ha⟩
  cases h : a v
  · exact zero ⟨a, ha, h⟩
  · exact one ⟨a, ha, h⟩

end BoundaryLab.IntegerCertificate
