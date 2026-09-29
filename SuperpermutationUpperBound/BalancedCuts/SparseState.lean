import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-! The sparse active-state lemma for iterative rounding. Only incidence
counts and the cancellation of a column with two active state coordinates
are used; no concrete choice-system definition is required. -/
namespace SuperpermutationUpperBound.BalancedCuts

open scoped BigOperators

variable {C : Type u} {I : Type v} {V : Type w}
  [Fintype C] [Fintype V]

def stateDegree (col : C → (I ⊕ V → ℚ)) (v : V) : Nat :=
  (Finset.univ.filter (fun c => col c (Sum.inr v) ≠ 0)).card

def columnStateDegree (col : C → (I ⊕ V → ℚ)) (c : C) : Nat :=
  (Finset.univ.filter (fun v => col c (Sum.inr v) ≠ 0)).card

theorem stateDegree_sum_eq_columnStateDegree (col : C → (I ⊕ V → ℚ)) :
    (∑ v, stateDegree col v) = ∑ c, columnStateDegree col c := by
  simp only [stateDegree, columnStateDegree, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

variable [Fintype I] [DecidableEq I]

theorem item_fiber_card_sum (item : C → I) :
    (∑ i, (Finset.univ.filter (fun c => item c = i)).card) = Fintype.card C := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := Finset.univ) (t := Finset.univ) (f := item) (by intro c _; simp)
  simpa only [Finset.card_univ] using h.symm

/-- If every unresolved item has at least two fractional columns, and the
combined item/state columns are independent, some active state has at most
three fractional incidences. The item coordinate values may be arbitrary.
-/
theorem exists_state_degree_le_three (col : C → (I ⊕ V → ℚ)) (item : C → I)
    (hne : Nonempty C)
    (hitem : ∀ i, 2 ≤ (Finset.univ.filter (fun c => item c = i)).card)
    (hcolumn : ∀ c, columnStateDegree col c ≤ 2)
    (hcancel : ∀ c, columnStateDegree col c = 2 → ∑ v, col c (Sum.inr v) = 0)
    (hli : LinearIndependent ℚ col) : ∃ v, stateDegree col v ≤ 3 := by
  classical
  by_contra hnone
  have hfour_each : ∀ v, 4 ≤ stateDegree col v := by
    intro v
    have hnot : ¬ stateDegree col v ≤ 3 := fun hv => hnone ⟨v, hv⟩
    omega
  have hitem_bound : 2 * Fintype.card I ≤ Fintype.card C := by
    have hi := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hitem i)
    rw [item_fiber_card_sum item] at hi
    simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm] using hi
  have hrank : Fintype.card C ≤ Fintype.card I + Fintype.card V := by
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum] using
      hli.fintype_card_le_finrank
  have hfour : 4 * Fintype.card V ≤ ∑ v, stateDegree col v := by
    have hv := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hfour_each v)
    simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm] using hv
  have htwo : (∑ c, columnStateDegree col c) ≤ 2 * Fintype.card C := by
    have hc := Finset.sum_le_sum (s := Finset.univ) (fun c _ => hcolumn c)
    simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm] using hc
  have hdouble := stateDegree_sum_eq_columnStateDegree col
  have heq : Fintype.card C = Fintype.card I + Fintype.card V := by omega
  have htotal : (∑ c, columnStateDegree col c) = 2 * Fintype.card C := by omega
  have htwice : ∀ c, columnStateDegree col c = 2 := by
    have hs : (∑ c, columnStateDegree col c) = ∑ _c : C, 2 := by
      simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm] using htotal
    exact fun c => (Finset.sum_eq_sum_iff_of_le (fun c _ => hcolumn c)).mp hs c (Finset.mem_univ c)
  have hsumzero : ∀ c, ∑ v, col c (Sum.inr v) = 0 := fun c => hcancel c (htwice c)
  have hspan : Submodule.span ℚ (Set.range col) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by
      simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum] using heq)
  have hspan_zero : ∀ x ∈ Submodule.span ℚ (Set.range col), ∑ v, x (Sum.inr v) = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, rfl⟩ := hx
      exact hsumzero c
    | zero => simp
    | add x y hx hy ihx ihy =>
      simp only [Pi.add_apply, Finset.sum_add_distrib, ihx, ihy, add_zero]
    | smul a x hx ih =>
      simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, ih, mul_zero]
  have hC : 0 < Fintype.card C := Fintype.card_pos_iff.mpr hne
  have hV : 0 < Fintype.card V := by omega
  obtain ⟨v₀⟩ : Nonempty V := Fintype.card_pos_iff.mp hV
  let unit : I ⊕ V → ℚ := fun j => if j = Sum.inr v₀ then 1 else 0
  have hunit : unit ∈ Submodule.span ℚ (Set.range col) := by rw [hspan]; trivial
  have hbad := hspan_zero unit hunit
  simp only [unit, Sum.inr.injEq, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hbad
  exact one_ne_zero hbad

end SuperpermutationUpperBound.BalancedCuts
