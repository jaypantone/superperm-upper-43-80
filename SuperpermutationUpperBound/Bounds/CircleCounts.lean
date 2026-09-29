import SuperpermutationUpperBound.Bounds.Definitions
import SuperpermutationUpperBound.Partition.SprintFamily
import Mathlib.Tactic.Linarith

namespace SuperpermutationUpperBound.Bounds

/-- Selected circle occurrences multiply by their old length, beginning
with the checked 377-circle target at old ordinary size 9. -/
def selectedCircleCount : Nat → Nat
  | 0 => 377
  | k + 1 => (k + 8) * selectedCircleCount k

theorem selectedCircleCount_factorial (k : Nat) :
    5040 * selectedCircleCount k = 377 * (k + 7).factorial := by
  induction k with
  | zero => decide
  | succ k ih =>
    change 5040 * ((k + 8) * selectedCircleCount k) = _
    rw [show (k + 1 + 7).factorial = (k + 8) * (k + 7).factorial from
      Nat.factorial_succ (k + 7)]
    nlinarith

theorem selectedCircleCount_scaled (k : Nat) :
    5040 * ((k + 8) * selectedCircleCount k) = 377 * (k + 8).factorial := by
  have h := selectedCircleCount_factorial k
  rw [show (k + 8).factorial = (k + 8) * (k + 7).factorial from Nat.factorial_succ (k + 7)]
  nlinarith

/-- Exact principal numerator of the historical-family charge plus all
selected ordinary circle edges. This is an arithmetic ledger, not yet the
existence of a circle cover of that cardinality. -/
theorem current_principal_numerator (k : Nat) :
    5040 * (((Partition.SprintFamily.rows k).map Row.charge).sum +
      (k + 8) * selectedCircleCount k) = 2729 * (k + 8).factorial := by
  have hq := Partition.SprintFamily.rows_charge k
  have hc := selectedCircleCount_scaled k
  omega

/-- The final overlap charge decreases with every available join. -/
theorem circle_overlap_length_bound {base m a t J c V len : Nat}
    (ha : 2 ≤ a) (ham : a ≤ m) (ht : t ≤ c) (hj : J ≤ min t V)
    (hlen : len = base + (m - 2) * t - (m - a) * (t - J)) :
    len ≤ base + (a - 2) * c + (m - a) * min c V := by
  have hJt := (Nat.le_min.mp hj).1
  have hJV := (Nat.le_min.mp hj).2
  have hJc : J ≤ c := hJt.trans ht
  have hmin : J ≤ min c V := Nat.le_min.mpr ⟨hJc, hJV⟩
  have h1 := Nat.mul_le_mul_left (a - 2) ht
  have h2 := Nat.mul_le_mul_left (m - a) hmin
  have hsplit : m - 2 = (a - 2) + (m - a) := by omega
  have he : base + (m - 2) * t =
      base + (a - 2) * t + (m - a) * J + (m - a) * (t - J) := by
    rw [hsplit]
    have hsub : t = J + (t - J) := by omega
    nlinarith
  rw [he, Nat.add_sub_cancel] at hlen
  omega

end SuperpermutationUpperBound.Bounds
