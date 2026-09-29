import SuperpermutationUpperBound.Foundation.Words
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Rat.Defs

/-! Exact arithmetic expressions for the stated bounds. These definitions
assert no existence of a superpermutation or validity of a circle cover. -/
namespace SuperpermutationUpperBound

/-- The first three factorial terms, with natural subtraction of indices. -/
def F3 (K : Nat) : Nat :=
  Nat.factorial K + Nat.factorial (K - 1) + Nat.factorial (K - 2)

/-- The factorial scale of the fourth term. -/
def Fourth (K : Nat) : Nat := Nat.factorial (K - 3)

/-- The current finite-parameter expression. Its intended construction theorem
requires `9 ≤ m` and `2 ≤ a ≤ m`; the expression alone makes no such theorem.
Every subtraction in an index/coefficient is performed in Nat before casting,
and every division displayed here is in the rational numbers. -/
def CircleBound (m a : Nat) : ℚ :=
  (F3 (m + 2) : ℚ)
    + ((2729 : ℚ) / 5040) * (Nat.factorial (m - 1) : ℚ)
    + ((a - 2 : Nat) : ℚ) * ((377 : ℚ) / 5040) * (Nat.factorial (m - 1) : ℚ)
        / ((m - 1 : Nat) : ℚ)
    + ((m - a : Nat) : ℚ) *
        min (((377 : ℚ) / 5040) * (Nat.factorial (m - 1) : ℚ) / ((m - 1 : Nat) : ℚ))
          ((Nat.factorial (m + 1) : ℚ) / (Nat.factorial (a + 1) : ℚ))

/-- A named proposition for the uniform three-fifths statement. -/
def UniformThreeFifthsStatement : Prop :=
  ∀ K : Nat, 10 ≤ K → ∃ w : Word K, IsSuperpermutation w ∧
    5 * w.length ≤ 5 * F3 K + 3 * Fourth K

/-- A named proposition for the uniform statement starting at eight. -/
def Uniform101Over120Statement : Prop :=
  ∀ K : Nat, 8 ≤ K → ∃ w : Word K, IsSuperpermutation w ∧
    120 * w.length ≤ 120 * F3 K + 101 * Fourth K

/-- The finite-parameter existence contract, retained as an unasserted proposition. -/
def CircleBoundStatement : Prop :=
  ∀ m : Nat, 9 ≤ m → ∀ a : Nat, 2 ≤ a → a ≤ m →
    ∃ w : Word (m + 2), IsSuperpermutation w ∧ (w.length : ℚ) ≤ CircleBound m a

/-- The epsilon target, retained as an unasserted proposition. -/
def Asymptotic2729Statement : Prop :=
  ∀ ε : ℚ, 0 < ε → ∃ N : Nat, 11 ≤ N ∧
    ∀ K : Nat, N ≤ K → ∃ w : Word K, IsSuperpermutation w ∧
      (w.length : ℚ) ≤ (F3 K : ℚ) + ((2729 : ℚ) / 5040 + ε) * (Fourth K : ℚ)

end SuperpermutationUpperBound
