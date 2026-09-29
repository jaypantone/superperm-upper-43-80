import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace SuperpermutationUpperBound.BalancedCuts

/-- Every candidate belongs to one item and has directed endpoint states. -/
structure ChoiceSystem (I V C : Type) where
  item : C → I
  source : C → V
  target : C → V

namespace ChoiceSystem
variable {I V C : Type} [Fintype C] [DecidableEq I] [DecidableEq V]

def incidence (S : ChoiceSystem I V C) (v : V) (c : C) : Int :=
  (if S.source c = v then 1 else 0) - (if S.target c = v then 1 else 0)

def itemMass (S : ChoiceSystem I V C) (x : C → ℚ) (i : I) : ℚ :=
  ∑ c, if S.item c = i then x c else 0

def stateBalance (S : ChoiceSystem I V C) (x : C → ℚ) (v : V) : ℚ :=
  ∑ c, (S.incidence v c : ℚ) * x c

def Feasible (S : ChoiceSystem I V C) (x : C → ℚ) : Prop :=
  (∀ c, 0 ≤ x c) ∧ (∀ i, S.itemMass x i = 1) ∧ (∀ v, S.stateBalance x v = 0)

omit [Fintype C] [DecidableEq I] in
theorem incidence_values (S : ChoiceSystem I V C) (v : V) (c : C) :
    S.incidence v c = -1 ∨ S.incidence v c = 0 ∨ S.incidence v c = 1 := by
  unfold incidence
  split <;> split <;> omega

omit [Fintype C] [DecidableEq I] in
theorem incidence_loop (S : ChoiceSystem I V C) (c : C) (hc : S.source c = S.target c) :
    ∀ v, S.incidence v c = 0 := by
  intro v
  simp [incidence, hc]

theorem Feasible.le_one {S : ChoiceSystem I V C} {x : C → ℚ}
    (hx : S.Feasible x) (c : C) : x c ≤ 1 := by
  have hsum := Finset.single_le_sum
    (fun d (_ : d ∈ Finset.univ) => show 0 ≤ if S.item d = S.item c then x d else 0 from
      by split <;> first | exact hx.1 d | exact le_refl 0)
    (Finset.mem_univ c)
  simp only [if_pos rfl] at hsum
  change x c ≤ S.itemMass x (S.item c) at hsum
  rw [hx.2.1] at hsum
  exact hsum

theorem Feasible.exists_positive {S : ChoiceSystem I V C} {x : C → ℚ}
    (hx : S.Feasible x) (i : I) : ∃ c, S.item c = i ∧ 0 < x c := by
  classical
  by_contra hn
  have hz : S.itemMass x i = 0 := by
    apply Finset.sum_eq_zero
    intro c _
    by_cases hc : S.item c = i
    · rw [if_pos hc]
      have hnonpos : x c ≤ 0 := by
        by_contra hp
        exact hn ⟨c, hc, lt_of_not_ge hp⟩
      exact le_antisymm hnonpos (hx.1 c)
    · simp [hc]
  have hmass := hx.2.1 i
  rw [hz] at hmass
  norm_num at hmass

end ChoiceSystem

/-- Dropping a state with at most three strictly fractional incidences leaves
permanent discrepancy at most two after every surviving variable is rounded. -/
theorem dropped_state_discrepancy {p r : Nat} {theta final : Int}
    (hn : p + r ≤ 3) (hlo : -(r : Int) < theta) (hhi : theta < (p : Int))
    (hflo : -(r : Int) ≤ final) (hfhi : final ≤ (p : Int)) :
    |final - theta| ≤ 2 := by
  apply abs_le.mpr
  constructor <;> omega

/-- The zero-incidence case is already exact. -/
theorem dropped_state_no_incidence {theta final : Int}
    (ht : theta = 0) (hf : final = 0) : |final - theta| = 0 := by simp [ht, hf]

end SuperpermutationUpperBound.BalancedCuts
