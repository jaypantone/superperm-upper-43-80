import SuperpermutationUpperBound.BalancedCuts.Selection
import SuperpermutationUpperBound.Assembly.BalancingEdges

namespace SuperpermutationUpperBound.BalancedCuts
namespace ChoiceSystem

variable {I V C : Type} [Fintype C] [DecidableEq I]

/-- Selected labels, including parallel candidates, are retained as a subtype
of the original candidate type. -/
abbrev Selected (y : C → ℚ) := {c // y c = 1}

def selectedSource (S : ChoiceSystem I V C) (y : C → ℚ) (c : Selected y) : V :=
  S.source c

def selectedTarget (S : ChoiceSystem I V C) (y : C → ℚ) (c : Selected y) : V :=
  S.target c

theorem selected_card [Fintype I] (S : ChoiceSystem I V C) (y : C → ℚ)
    (hy : S.ItemFeasible y) (hint : IntegralVector y) :
    Fintype.card (Selected y) = Fintype.card I :=
  Fintype.card_congr (S.integralSupportEquiv y hy hint)

variable [DecidableEq V]

/-- The graph's signed degree is exactly the rounded rational state balance. -/
theorem selected_degreeImbalance_eq_stateBalance
    (S : ChoiceSystem I V C) (y : C → ℚ) (hint : IntegralVector y) (v : V) :
    (degreeImbalance (S.selectedSource y) (S.selectedTarget y) v : ℚ) =
      S.stateBalance y v := by
  classical
  rw [S.stateBalance_eq_selected y hint v]
  simp only [degreeImbalance, Int.cast_sub, Fintype.card_subtype,
    Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Nat.cast_zero, Nat.cast_ite,
    Int.cast_sum, Finset.sum_filter,
    incidence, Int.cast_ite, Int.cast_one, Int.cast_zero,
    Finset.sum_sub_distrib, selectedSource, selectedTarget]

theorem selected_degreeImbalance_bound
    (S : ChoiceSystem I V C) (y : C → ℚ) (hint : IntegralVector y)
    (hb : ∀ v, |S.stateBalance y v| ≤ 2) :
    ∀ v, |degreeImbalance (S.selectedSource y) (S.selectedTarget y) v| ≤ 2 := by
  intro v
  have h := hb v
  rw [← S.selected_degreeImbalance_eq_stateBalance y hint v] at h
  exact_mod_cast h

/-- Feasible fractional choices yield an actual labelled graph with one edge
per item, using only initially positive candidates, and imbalance at most two. -/
theorem Feasible.exists_selected_graph [Fintype I] [Fintype V]
    {S : ChoiceSystem I V C} {x : C → ℚ} (hx : S.Feasible x) :
    ∃ y : C → ℚ, IntegralVector y ∧ S.ItemFeasible y ∧
      (∀ c : Selected y, 0 < x c) ∧
      Fintype.card (Selected y) = Fintype.card I ∧
      (∀ i, ∃! c : Selected y, S.item c = i) ∧
      ∀ v, |degreeImbalance (S.selectedSource y) (S.selectedTarget y) v| ≤ 2 := by
  obtain ⟨y, hyint, hym, _href, hs, hb⟩ := hx.exists_integral_rounding
  refine ⟨y, hyint, hym, ?_, S.selected_card y hym hyint, ?_,
    S.selected_degreeImbalance_bound y hyint hb⟩
  · intro c
    apply mem_positiveSupport.mp (hs _)
    exact mem_positiveSupport.mpr (by rw [c.property]; norm_num)
  · intro i
    obtain ⟨c, hc, hu⟩ := hym.exists_unique_one hyint i
    refine ⟨⟨c, hc.2⟩, hc.1, fun d hd => ?_⟩
    exact Subtype.ext (hu d ⟨hd, d.property⟩)

end ChoiceSystem
end SuperpermutationUpperBound.BalancedCuts
