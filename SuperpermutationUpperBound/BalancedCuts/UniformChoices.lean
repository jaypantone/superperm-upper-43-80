import SuperpermutationUpperBound.BalancedCuts.Definitions
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.FinRange
import Mathlib.Algebra.BigOperators.Fin

namespace SuperpermutationUpperBound.BalancedCuts

variable {I V : Type} {h : Nat}

/-- Each item has exactly `h` labelled candidate occurrences. -/
def uniformSystem (source target : I × Fin h → V) : ChoiceSystem I V (I × Fin h) :=
  ⟨Prod.fst, source, target⟩

def uniformWeight (h : Nat) : I × Fin h → ℚ := fun _ => 1 / (h : ℚ)

variable [Fintype I] [DecidableEq I] [DecidableEq V]

omit [DecidableEq V] in
theorem uniform_itemMass (source target : I × Fin h → V) (hpos : 0 < h) (i : I) :
    (uniformSystem source target).itemMass (uniformWeight h) i = 1 := by
  have hn : (h : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hpos)
  simp only [ChoiceSystem.itemMass, uniformSystem, uniformWeight, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp [hn]

omit [DecidableEq I] in
/-- Permutation of endpoint lists balances every state with multiplicity;
the endpoints need not be distinct within an item's list. -/
theorem uniform_stateBalance (source target : I × Fin h → V)
    (hperm : ∀ i, ((List.finRange h).map (fun j => source (i, j))).Perm
      ((List.finRange h).map (fun j => target (i, j)))) (v : V) :
    (uniformSystem source target).stateBalance (uniformWeight h) v = 0 := by
  have hitem : ∀ i, (∑ j : Fin h, (if source (i, j) = v then (1 : ℚ) else 0)) =
      ∑ j : Fin h, (if target (i, j) = v then (1 : ℚ) else 0) := by
    intro i
    have hp := ((hperm i).map (fun a => if a = v then (1 : ℚ) else 0)).sum_eq
    simpa only [List.map_map, Function.comp_def, ← List.ofFn_eq_map, List.map_ofFn,
      Function.comp_def, List.sum_ofFn] using hp
  unfold ChoiceSystem.stateBalance
  rw [Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro i _
  simp only [ChoiceSystem.incidence, uniformSystem, uniformWeight, Int.cast_sub,
    Int.cast_ite, Int.cast_one, Int.cast_zero, ← Finset.sum_mul,
    Finset.sum_sub_distrib, hitem i, sub_self, zero_mul]

theorem uniform_feasible (source target : I × Fin h → V) (hpos : 0 < h)
    (hperm : ∀ i, ((List.finRange h).map (fun j => source (i, j))).Perm
      ((List.finRange h).map (fun j => target (i, j)))) :
    (uniformSystem source target).Feasible (uniformWeight h) := by
  refine ⟨fun _ => ?_, uniform_itemMass source target hpos,
    uniform_stateBalance source target hperm⟩
  exact div_nonneg (by norm_num) (Nat.cast_nonneg h)

end SuperpermutationUpperBound.BalancedCuts
