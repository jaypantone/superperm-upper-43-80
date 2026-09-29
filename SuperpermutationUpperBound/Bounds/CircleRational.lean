import SuperpermutationUpperBound.Bounds.CircleCounts
import Mathlib.Tactic.FieldSimp

/-! Exact conversion of the natural circle-construction length ledger to
the rational expression in the theorem contract. -/
namespace SuperpermutationUpperBound.Bounds

theorem selectedCircleCount_rat (k : Nat) :
    (selectedCircleCount k : ℚ) =
      (377 / 5040 : ℚ) * ((k + 8).factorial : ℚ) / (k + 8 : Nat) := by
  have hk : ((k + 8 : Nat) : ℚ) ≠ 0 := by positivity
  apply (eq_div_iff hk).mpr
  have hc : (5040 : ℚ) * (((k + 8 : Nat) : ℚ) * (selectedCircleCount k : ℚ)) =
      377 * ((k + 8).factorial : ℚ) := by
    exact_mod_cast selectedCircleCount_scaled k
  linarith

theorem current_principal_rat (k : Nat) :
    ((((Partition.SprintFamily.rows k).map Row.charge).sum +
      (k + 8) * selectedCircleCount k : Nat) : ℚ) =
      (2729 / 5040 : ℚ) * ((k + 8).factorial : ℚ) := by
  have hc : (5040 : ℚ) *
      ((((Partition.SprintFamily.rows k).map Row.charge).sum +
        (k + 8) * selectedCircleCount k : Nat) : ℚ) =
      2729 * ((k + 8).factorial : ℚ) := by
    exact_mod_cast current_principal_numerator k
  linarith

theorem overlap_state_count_rat (k a : Nat) (ha : a ≤ k + 9) :
    ((k + 10).descFactorial (k + 9 - a) : ℚ) =
      ((k + 10).factorial : ℚ) / ((a + 1).factorial : ℚ) := by
  have hfact : ((a + 1).factorial : ℚ) ≠ 0 := by positivity
  apply (eq_div_iff hfact).mpr
  have he := Nat.factorial_mul_descFactorial (show k + 9 - a ≤ k + 10 by omega)
  rw [show k + 10 - (k + 9 - a) = a + 1 by omega] at he
  exact_mod_cast (Nat.mul_comm _ _).trans he

/-- The construction ledger equals the displayed rational bound exactly. -/
theorem circle_ledger_eq_CircleBound (k a : Nat) (ha : a ≤ k + 9) :
    ((F3 (k + 11) + ((Partition.SprintFamily.rows k).map Row.charge).sum +
      (k + 8) * selectedCircleCount k + (a - 2) * selectedCircleCount k +
      (k + 9 - a) * min (selectedCircleCount k)
        ((k + 10).descFactorial (k + 9 - a)) : Nat) : ℚ) = CircleBound (k + 9) a := by
  have hp := current_principal_rat k
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hp
  unfold CircleBound
  rw [show k + 9 + 2 = k + 11 by omega, show k + 9 - 1 = k + 8 by omega,
    show k + 9 + 1 = k + 10 by omega]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_min, Nat.cast_ofNat]
  rw [show (F3 (k + 11) : ℚ) +
      (((Partition.SprintFamily.rows k).map Row.charge).sum : ℚ) +
      ((k : ℚ) + 8) * (selectedCircleCount k : ℚ) =
        (F3 (k + 11) : ℚ) + (2729 / 5040 : ℚ) * ((k + 8).factorial : ℚ) by
          linarith]
  rw [selectedCircleCount_rat, overlap_state_count_rat k a ha]
  simp only [Nat.cast_add, Nat.cast_ofNat]
  ring

theorem circleBound_of_nat_ledger (k a len : Nat) (ha : a ≤ k + 9)
    (hlen : len ≤ F3 (k + 11) + ((Partition.SprintFamily.rows k).map Row.charge).sum +
      (k + 8) * selectedCircleCount k + (a - 2) * selectedCircleCount k +
      (k + 9 - a) * min (selectedCircleCount k)
        ((k + 10).descFactorial (k + 9 - a))) :
    (len : ℚ) ≤ CircleBound (k + 9) a := by
  rw [← circle_ledger_eq_CircleBound k a ha]
  exact_mod_cast hlen

theorem circleBound_of_nat_word_ledger (k a : Nat) (ha : a ≤ k + 9)
    (hw : ∃ w : Word (k + 11), IsSuperpermutation w ∧
      w.length ≤ F3 (k + 11) + ((Partition.SprintFamily.rows k).map Row.charge).sum +
        (k + 8) * selectedCircleCount k + (a - 2) * selectedCircleCount k +
        (k + 9 - a) * min (selectedCircleCount k)
          ((k + 10).descFactorial (k + 9 - a))) :
    ∃ w : Word (k + 11), IsSuperpermutation w ∧ (w.length : ℚ) ≤ CircleBound (k + 9) a := by
  obtain ⟨w, hs, hl⟩ := hw
  exact ⟨w, hs, circleBound_of_nat_ledger k a w.length ha hl⟩

/-- All remaining hypotheses are the natural word-existence ledger; its
conversion to the exact all-size rational contract is arithmetic. -/
theorem circleBoundStatement_of_nat_ledger
    (hw : ∀ k a : Nat, 2 ≤ a → a ≤ k + 9 →
      ∃ w : Word (k + 11), IsSuperpermutation w ∧
        w.length ≤ F3 (k + 11) + ((Partition.SprintFamily.rows k).map Row.charge).sum +
          (k + 8) * selectedCircleCount k + (a - 2) * selectedCircleCount k +
          (k + 9 - a) * min (selectedCircleCount k)
            ((k + 10).descFactorial (k + 9 - a))) : CircleBoundStatement := by
  intro m hm a ha ham
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hak : a ≤ k + 9 := by omega
  have he := circleBound_of_nat_word_ledger k a hak (hw k a ha hak)
  rw [Nat.add_comm 9 k]
  exact he

end SuperpermutationUpperBound.Bounds
