import SuperpermutationUpperBound.BalancedCuts.Residual

/-! Finite sharp rounding for choices carrying a directed state incidence.
The iteration preserves item masses, fixes coordinates that reach zero or
one, and drops only states with at most three fractional incidences. -/
namespace SuperpermutationUpperBound.BalancedCuts
namespace ChoiceSystem

variable {I V C : Type} [Fintype C] [DecidableEq I] [DecidableEq V]

/-- The induction invariant permits previously dropped states. Their bound
holds for every later integral refinement, so removing one more active state
does not weaken any earlier bound. -/
theorem round_active (S : ChoiceSystem I V C) (A : Finset V) (x : C → ℚ)
    (hx : S.ActiveFeasible A x) (hs : S.SafeDropped A x) :
    ∃ y : C → ℚ, IntegralVector y ∧ S.ItemFeasible y ∧ Refines x y ∧
      positiveSupport y ⊆ positiveSupport x ∧ ∀ v, |S.stateBalance y v| ≤ 2 := by
  classical
  suffices H : ∀ n, ∀ (A : Finset V) (x : C → ℚ), A.card = n →
      S.ActiveFeasible A x → S.SafeDropped A x →
      ∃ y : C → ℚ, IntegralVector y ∧ S.ItemFeasible y ∧ Refines x y ∧
        positiveSupport y ⊆ positiveSupport x ∧ ∀ v, |S.stateBalance y v| ≤ 2 by
    exact H _ A x rfl hx hs
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A x hn hx hs
    obtain ⟨z, hz, hxz, hsz, hiz⟩ := hx.sparsify
    have hsafe : S.SafeDropped A z := hs.refine hxz
    by_cases hint : IntegralVector z
    · refine ⟨z, hint, hz.1, hxz, hsz, fun v => ?_⟩
      by_cases hv : v ∈ A
      · rw [hz.2 v hv, abs_zero]
        norm_num
      · exact hsafe v hv z hint (Refines.refl z)
    · obtain ⟨v, hv, hsmall⟩ := hz.exists_sparse_fractional_state hiz hint
      have hlt : (A.erase v).card < n := by
        rw [← hn]
        exact Finset.card_lt_card (Finset.erase_ssubset hv)
      have hz' : S.ActiveFeasible (A.erase v) z :=
        ⟨hz.1, fun w hw => hz.2 w (Finset.mem_of_mem_erase hw)⟩
      obtain ⟨y, hyint, hym, hzy, hsy, hyb⟩ :=
        ih _ hlt (A.erase v) z rfl hz' (hsafe.erase hz hv hsmall)
      exact ⟨y, hyint, hym, hxz.trans hzy, hsy.trans hsz, hyb⟩

variable [Fintype V]

/-- A nonnegative feasible rational choice vector has a zero-one refinement
with the same unit item masses, no new positive coordinate, and absolute
state discrepancy at most two. -/
theorem Feasible.exists_integral_rounding {S : ChoiceSystem I V C} {x : C → ℚ}
    (hx : S.Feasible x) :
    ∃ y : C → ℚ, IntegralVector y ∧ S.ItemFeasible y ∧ Refines x y ∧
      positiveSupport y ⊆ positiveSupport x ∧ ∀ v, |S.stateBalance y v| ≤ 2 := by
  apply S.round_active Finset.univ x
  · exact ⟨hx.itemFeasible, fun v _ => hx.2.2 v⟩
  · intro v hv
    exact (hv (Finset.mem_univ v)).elim

/-- An explicit form of sharp rounding, exposing the item equations and
preservation of every zero coordinate. -/
theorem exists_integral_rounding (S : ChoiceSystem I V C) (x : C → ℚ)
    (hx : S.Feasible x) :
    ∃ y : C → ℚ, (∀ c, y c = 0 ∨ y c = 1) ∧
      (∀ i, S.itemMass y i = 1) ∧ (∀ c, x c = 0 → y c = 0) ∧
      positiveSupport y ⊆ positiveSupport x ∧ ∀ v, |S.stateBalance y v| ≤ 2 := by
  obtain ⟨y, hy, hym, href, hs, hb⟩ := hx.exists_integral_rounding
  exact ⟨y, hy, hym.2, fun c hc => (href c (Or.inl hc)).trans hc, hs, hb⟩

end ChoiceSystem
end SuperpermutationUpperBound.BalancedCuts
