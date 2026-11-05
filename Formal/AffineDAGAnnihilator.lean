import Formal.ParityQueries

/-! Semantic components of the direct common-annihilator argument.
These theorems do not formalize ordinary polynomial calculus, graph reduction,
the counting argument, or the unrestricted-DAG lower bound as a whole. -/
set_option autoImplicit false

namespace BoundaryLab.AffineDAGAnnihilator

def Cube : Nat → Type
  | 0 => Unit
  | n+1 => Bool × Cube n

/-- Coefficients of a squarefree F2 polynomial, separated by the last bit. -/
def ANF : Nat → Type
  | 0 => Bool
  | n+1 => ANF n × ANF n

def eval : (n : Nat) → ANF n → Cube n → Bool
  | 0, p, _ => p
  | n+1, (lo, hi), (b, a) => Bool.xor (eval n lo a) (b && eval n hi a)

def zero : (n : Nat) → ANF n
  | 0 => false
  | n+1 => (zero n, zero n)

theorem eval_zero (n : Nat) (a : Cube n) : eval n (zero n) a = false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases a with ⟨b, a⟩
    simp [eval, zero, ih]

/-- A multilinear F2 polynomial vanishing on every Boolean word is zero.
This is the uniqueness fact used after explicit Boolean-ideal reduction. -/
theorem multilinear_vanishing_unique (n : Nat) (p : ANF n)
    (vanishes : ∀ a, eval n p a = false) : p = zero n := by
  induction n with
  | zero => exact vanishes ()
  | succ n ih =>
    rcases p with ⟨lo, hi⟩
    have hlo : lo = zero n := by
      apply ih lo
      intro a
      simpa [eval] using vanishes (false, a)
    have hhi : hi = zero n := by
      apply ih hi
      intro a
      have h := vanishes (true, a)
      simpa [eval, hlo, eval_zero] using h
    exact Prod.ext hlo hhi

/-- Both retained parent indicators suffice for a sound binary step. -/
theorem two_low_identity (f a b c : Bool)
    (sound : c = true → a = true ∨ b = true) :
    (f && c) = Bool.xor ((f && a) && c) (((f && b) && c) && !a) := by
  cases f <;> cases a <;> cases b <;> cases c <;> simp_all

/-- A discarded parent is replaced by the common annihilation condition. -/
theorem one_high_identity (f a b c : Bool)
    (sound : c = true → a = true ∨ b = true)
    (killed : a = true → f = false) :
    (f && c) = ((f && b) && c) := by
  cases f <;> cases a <;> cases b <;> cases c <;> simp_all

theorem two_high_vanishing (f a b c : Bool)
    (sound : c = true → a = true ∨ b = true)
    (killA : a = true → f = false) (killB : b = true → f = false) :
    (f && c) = false := by
  cases f <;> cases a <;> cases b <;> cases c <;> simp_all

/-- The selected degree and rank budgets stay inside the old PC barrier. -/
theorem rank_cut_degree_budget (k r s : Nat)
    (degree : k ≤ s / 256) (rank : r ≤ s / 16) :
    k + 3*r ≤ s / 4 := by
  omega

end BoundaryLab.AffineDAGAnnihilator
