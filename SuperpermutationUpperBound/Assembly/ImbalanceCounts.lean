import SuperpermutationUpperBound.Assembly.BalancedGraph
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Order.Lemmas
import Mathlib.Tactic.Linarith

namespace SuperpermutationUpperBound

variable {E V : Type} [Fintype E] [Fintype V] [DecidableEq V]

/-- Outdegree minus indegree, counting each edge label separately. -/
def degreeImbalance (src dst : E → V) (v : V) : Int :=
  (Fintype.card {e // src e = v} : Int) - (Fintype.card {e // dst e = v} : Int)

def positiveImbalance (src dst : E → V) : Nat :=
  ∑ v, (degreeImbalance src dst v).toNat

def nonzeroVertices (src dst : E → V) : Finset V :=
  Finset.univ.filter (fun v => degreeImbalance src dst v ≠ 0)

theorem sum_fiber_card (f : E → V) :
    (∑ v, Fintype.card {e // f e = v}) = Fintype.card E := by
  simpa only [Fintype.card_sigma] using Fintype.card_congr (Equiv.sigmaFiberEquiv f)

theorem degreeImbalance_sum_zero (src dst : E → V) :
    (∑ v, degreeImbalance src dst v) = 0 := by
  simp only [degreeImbalance, Finset.sum_sub_distrib, ← Nat.cast_sum,
    sum_fiber_card, sub_self]

omit [Fintype E] [DecidableEq V] in
theorem sum_toNat_eq_sum_neg_toNat (z : V → Int) (hz : ∑ v, z v = 0) :
    (∑ v, (z v).toNat) = ∑ v, (-z v).toNat := by
  have he : ((∑ v, (z v).toNat : Nat) : Int) -
      ((∑ v, (-z v).toNat : Nat) : Int) = 0 := by
    simp only [Nat.cast_sum, ← Finset.sum_sub_distrib, Int.toNat_sub_toNat_neg, hz]
  exact_mod_cast sub_eq_zero.mp he

omit [Fintype E] [DecidableEq V] in
/-- A zero-sum integer vector bounded by two needs no more positive unit
slots than its number of nonzero coordinates. -/
theorem sum_toNat_le_nonzero_card (z : V → Int) (hz : ∑ v, z v = 0)
    (hb : ∀ v, |z v| ≤ 2) :
    (∑ v, (z v).toNat) ≤ (Finset.univ.filter (fun v => z v ≠ 0)).card := by
  classical
  have he := sum_toNat_eq_sum_neg_toNat z hz
  have hterm : ∀ v, (z v).toNat + (-z v).toNat ≤ if z v = 0 then 0 else 2 := by
    intro v
    by_cases hv : z v = 0
    · simp [hv]
    · rw [if_neg hv, Int.toNat_add_toNat_neg_eq_natAbs]
      have h := hb v
      rw [← Int.natCast_natAbs] at h
      exact_mod_cast h
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hterm v)
  rw [Finset.sum_add_distrib, ← he] at hsum
  have hr : (∑ v, if z v = 0 then 0 else 2 : Nat) =
      2 * (Finset.univ.filter (fun v => z v ≠ 0)).card := by
    simp [Finset.sum_ite, Nat.mul_comm]
  rw [hr] at hsum
  omega

theorem positiveImbalance_eq_negative (src dst : E → V) :
    positiveImbalance src dst = ∑ v, (-degreeImbalance src dst v).toNat :=
  sum_toNat_eq_sum_neg_toNat _ (degreeImbalance_sum_zero src dst)

theorem positiveImbalance_le_nonzeroVertices (src dst : E → V)
    (hb : ∀ v, |degreeImbalance src dst v| ≤ 2) :
    positiveImbalance src dst ≤ (nonzeroVertices src dst).card :=
  sum_toNat_le_nonzero_card _ (degreeImbalance_sum_zero src dst) hb

end SuperpermutationUpperBound
