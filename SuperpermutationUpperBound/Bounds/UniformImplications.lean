import SuperpermutationUpperBound.Bounds.Definitions
import Mathlib.Tactic

/-! Arithmetic implications between exact word-existence contracts.  Every
existence result in this file has an explicit input existence hypothesis. -/
namespace SuperpermutationUpperBound.Bounds

/-- Clearing denominators preserves the exact weakening from 3/5 to 101/120. -/
theorem weaken_threeFifths {K L : Nat}
    (h : 5 * L ≤ 5 * F3 K + 3 * Fourth K) :
    120 * L ≤ 120 * F3 K + 101 * Fourth K := by omega

theorem finite8_coefficient_inequality :
    120 * 46181 = 120 * F3 8 + 101 * Fourth 8 := by norm_num [F3, Fourth]

theorem finite9_coefficient_inequality :
    120 * 408743 ≤ 120 * F3 9 + 101 * Fourth 9 := by norm_num [F3, Fourth]

theorem eight_coefficient_of_word
    (h8 : HasSuperpermutationOfLengthAtMost 8 46181) :
    ∃ w : Word 8, IsSuperpermutation w ∧
      120 * w.length ≤ 120 * F3 8 + 101 * Fourth 8 := by
  obtain ⟨w, hw, hlen⟩ := h8
  refine ⟨w, hw, ?_⟩
  calc
    120 * w.length ≤ 120 * 46181 := Nat.mul_le_mul_left 120 hlen
    _ = 120 * F3 8 + 101 * Fourth 8 := finite8_coefficient_inequality

theorem nine_coefficient_of_word
    (h9 : HasSuperpermutationOfLengthAtMost 9 408743) :
    ∃ w : Word 9, IsSuperpermutation w ∧
      120 * w.length ≤ 120 * F3 9 + 101 * Fourth 9 := by
  obtain ⟨w, hw, hlen⟩ := h9
  refine ⟨w, hw, ?_⟩
  exact (Nat.mul_le_mul_left 120 hlen).trans finite9_coefficient_inequality

/-- Conditional uniform implication, with actual words and the exact cleared
natural inequality in the conclusion. The three premises remain to be proved
by the combinatorial construction and finite witness certificates. -/
theorem uniform101Over120_of_finite_and_threeFifths
    (h8 : HasSuperpermutationOfLengthAtMost 8 46181)
    (h9 : HasSuperpermutationOfLengthAtMost 9 408743)
    (h10 : UniformThreeFifthsStatement) :
    ∀ K : Nat, 8 ≤ K → ∃ w : Word K, IsSuperpermutation w ∧
      120 * w.length ≤ 120 * F3 K + 101 * Fourth K := by
  intro K hK
  by_cases hK8 : K = 8
  · subst K
    exact eight_coefficient_of_word h8
  by_cases hK9 : K = 9
  · subst K
    exact nine_coefficient_of_word h9
  obtain ⟨w, hw, hlen⟩ := h10 K (by omega)
  exact ⟨w, hw, weaken_threeFifths hlen⟩

/-- Proposition-form packaging of the same conditional implication. -/
theorem uniform101Over120Statement_of_inputs
    (h8 : HasSuperpermutationOfLengthAtMost 8 46181)
    (h9 : HasSuperpermutationOfLengthAtMost 9 408743)
    (h10 : UniformThreeFifthsStatement) : Uniform101Over120Statement :=
  uniform101Over120_of_finite_and_threeFifths h8 h9 h10

/-- The old m=8, 54-circle scalar ledger, stated independently of CircleBound. -/
theorem structural10_ledger :
    F3 10 + 2352 + 7 * 54 + 5 * 54 + min 54 9 = 4035009 := by norm_num [F3]

theorem structural10_surplus :
    F3 10 + 2352 + 7 * 54 + 5 * 54 + min 54 9 = F3 10 + 3009 := by omega

theorem structural10_threeFifths_inequality :
    5 * 4035009 ≤ 5 * F3 10 + 3 * Fourth 10 := by norm_num [F3, Fourth]

/-- A structural ten-symbol word of the stated length suffices for its 3/5 case. -/
theorem threeFifths_at_ten_of_structural_word
    (h10 : HasSuperpermutationOfLengthAtMost 10 4035009) :
    ∃ w : Word 10, IsSuperpermutation w ∧
      5 * w.length ≤ 5 * F3 10 + 3 * Fourth 10 := by
  obtain ⟨w, hw, hlen⟩ := h10
  exact ⟨w, hw, (Nat.mul_le_mul_left 5 hlen).trans structural10_threeFifths_inequality⟩

theorem principal_coefficient_le_older : (2729 : ℚ) / 5040 ≤ 229 / 420 := by norm_num

theorem circle_coefficient_le_older : (377 : ℚ) / 5040 ≤ 11 / 140 := by norm_num

theorem structural10_surplus_ratio : (3009 : ℚ) / 5040 = 1003 / 1680 := by norm_num

theorem structural10_surplus_ratio_lt_threeFifths : (1003 : ℚ) / 1680 < 3 / 5 := by
  norm_num

#print axioms weaken_threeFifths
#print axioms finite8_coefficient_inequality
#print axioms finite9_coefficient_inequality
#print axioms uniform101Over120_of_finite_and_threeFifths
#print axioms structural10_ledger
#print axioms structural10_threeFifths_inequality
#print axioms threeFifths_at_ten_of_structural_word
#print axioms principal_coefficient_le_older
#print axioms circle_coefficient_le_older

end SuperpermutationUpperBound.Bounds
