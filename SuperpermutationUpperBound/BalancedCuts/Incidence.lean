import SuperpermutationUpperBound.BalancedCuts.Definitions
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace SuperpermutationUpperBound.BalancedCuts
namespace ChoiceSystem
variable {I V C : Type} [DecidableEq V]

def activeIncidences (S : ChoiceSystem I V C) (A : Finset V) (c : C) : Finset A :=
  Finset.univ.filter (fun v => (S.incidence v c : ℚ) ≠ 0)

theorem incidence_ne_zero_endpoints (S : ChoiceSystem I V C) (v : V) (c : C)
    (hc : (S.incidence v c : ℚ) ≠ 0) : v = S.source c ∨ v = S.target c := by
  by_contra he
  have hs : S.source c ≠ v := fun h => he (Or.inl h.symm)
  have ht : S.target c ≠ v := fun h => he (Or.inr h.symm)
  simp [incidence, hs, ht] at hc

theorem activeIncidences_image_subset (S : ChoiceSystem I V C) (A : Finset V) (c : C) :
    (S.activeIncidences A c).image Subtype.val ⊆ {S.source c, S.target c} := by
  intro v hv
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
  have h := S.incidence_ne_zero_endpoints a c (Finset.mem_filter.mp ha).2
  simpa only [Finset.mem_insert, Finset.mem_singleton] using h

theorem activeIncidences_card_le_two (S : ChoiceSystem I V C) (A : Finset V) (c : C) :
    (S.activeIncidences A c).card ≤ 2 := by
  have h := Finset.card_le_card (S.activeIncidences_image_subset A c)
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at h
  have hp : ({S.source c, S.target c} : Finset V).card ≤ 2 := by
    calc
      _ ≤ ({S.target c} : Finset V).card + 1 := Finset.card_insert_le _ _
      _ = 2 := by simp
  exact h.trans hp

/-- If both nonzero active coordinates occur, they cancel. -/
theorem activeIncidences_card_two_sum_zero (S : ChoiceSystem I V C) (A : Finset V) (c : C)
    (hc : (S.activeIncidences A c).card = 2) :
    (∑ v : A, (S.incidence v c : ℚ)) = 0 := by
  have he : (S.activeIncidences A c).image Subtype.val = {S.source c, S.target c} := by
    apply Finset.eq_of_subset_of_card_le (S.activeIncidences_image_subset A c)
    rw [Finset.card_image_of_injective _ Subtype.val_injective, hc]
    calc
      _ ≤ ({S.target c} : Finset V).card + 1 := Finset.card_insert_le _ _
      _ = 2 := by simp
  obtain ⟨vs, _, hvs⟩ := Finset.mem_image.mp (he.symm ▸ (by simp : S.source c ∈ ({S.source c, S.target c} : Finset V)))
  obtain ⟨vt, _, hvt⟩ := Finset.mem_image.mp (he.symm ▸ (by simp : S.target c ∈ ({S.source c, S.target c} : Finset V)))
  simp only [incidence, ← hvs, ← hvt, Subtype.val_inj]
  push_cast
  simp [Finset.sum_sub_distrib, Finset.sum_ite_eq]

end ChoiceSystem
end SuperpermutationUpperBound.BalancedCuts
