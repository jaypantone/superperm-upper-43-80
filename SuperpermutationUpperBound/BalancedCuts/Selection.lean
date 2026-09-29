import SuperpermutationUpperBound.BalancedCuts.Rounding

namespace SuperpermutationUpperBound.BalancedCuts
namespace ChoiceSystem
variable {I V C : Type} [Fintype C] [DecidableEq I]

/-- A unit integral item vector contains exactly one positive candidate for
each item. This turns rational rounding into an actual finite selection. -/
theorem ItemFeasible.exists_unique_one {S : ChoiceSystem I V C} {y : C → ℚ}
    (hy : S.ItemFeasible y) (hint : IntegralVector y) (i : I) :
    ∃! c, S.item c = i ∧ y c = 1 := by
  classical
  have hex : ∃ c, S.item c = i ∧ y c = 1 := by
    by_contra hn
    have hz : S.itemMass y i = 0 := by
      apply Finset.sum_eq_zero
      intro c _
      by_cases hci : S.item c = i
      · rcases hint c with h0 | h1
        · simp [hci, h0]
        · exact False.elim (hn ⟨c, hci, h1⟩)
      · simp [hci]
    have hmass := hy.2 i
    rw [hz] at hmass
    norm_num at hmass
  obtain ⟨c, hc, hc1⟩ := hex
  refine ⟨c, ⟨hc, hc1⟩, ?_⟩
  intro d hd
  by_contra hdc
  have hzero := hy.zero_other_of_one hc1 (hd.1.trans hc.symm) hdc
  rw [hd.2] at hzero
  norm_num at hzero

/-- The positive support of an integral unit-mass vector is in bijection
with the item type, without any assumption on candidate multiplicities. -/
noncomputable def integralSupportEquiv (S : ChoiceSystem I V C) (y : C → ℚ)
    (hy : S.ItemFeasible y) (hint : IntegralVector y) : {c // y c = 1} ≃ I := by
  classical
  apply Equiv.ofBijective (fun c => S.item c.val)
  constructor
  · intro c d hcd
    apply Subtype.ext
    exact (hy.exists_unique_one hint (S.item d.val)).unique
      ⟨hcd, c.property⟩ ⟨rfl, d.property⟩
  · intro i
    obtain ⟨c, hc, _⟩ := hy.exists_unique_one hint i
    exact ⟨⟨c, hc.2⟩, hc.1⟩

/-- For integral weights, the rational incidence sum is the unweighted sum
over the selected candidate occurrences. -/
theorem stateBalance_eq_selected [DecidableEq V]
    (S : ChoiceSystem I V C) (y : C → ℚ) (hint : IntegralVector y) (v : V) :
    S.stateBalance y v = ∑ c : {c // y c = 1}, (S.incidence v c : ℚ) := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (fun c => y c = 1))
    (by simp) (fun c => (S.incidence v c : ℚ)), Finset.sum_filter]
  unfold stateBalance
  apply Finset.sum_congr rfl
  intro c _
  rcases hint c with h0 | h1
  · simp [h0]
  · simp [h1]

end ChoiceSystem
end SuperpermutationUpperBound.BalancedCuts
