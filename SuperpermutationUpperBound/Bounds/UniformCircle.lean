import SuperpermutationUpperBound.Bounds.UniformImplications

/-! The uniform three-fifths consequence of the current finite circle bound.
The circle construction and the structural ten-symbol word remain premises. -/
namespace SuperpermutationUpperBound.Bounds

set_option maxHeartbeats 2000000

/-- Parameters for the seven exceptional finite substitutions, m=9,...,15. -/
def finiteUniformParameter (m : Nat) : Nat := if m ≤ 10 then 7 else 8

theorem finite_uniform_parameter (m : Nat) (hm9 : 9 ≤ m) (hm15 : m ≤ 15) :
    2 ≤ finiteUniformParameter m ∧ finiteUniformParameter m ≤ m ∧
      CircleBound m (finiteUniformParameter m) ≤
        (F3 (m + 2) : ℚ) + ((3 : ℚ) / 5) * (Fourth (m + 2) : ℚ) := by
  interval_cases m <;> norm_num [finiteUniformParameter, CircleBound, F3, Fourth]

/-- The odd-case numerator also bounds the even case at a=floor(m/2). -/
def oddTailRatio (a : Nat) : ℚ :=
  2 * (2 * (a : ℚ) + 1) * ((a : ℚ) + 1) ^ 2 / (Nat.factorial (a + 1) : ℚ)

theorem oddTailRatio_step (a : Nat) (ha : 8 ≤ a) :
    oddTailRatio (a + 1) ≤ oddTailRatio a := by
  have haQ : (8 : ℚ) ≤ a := by exact_mod_cast ha
  have hp : (2 * (a : ℚ) + 3) * ((a : ℚ) + 2) ≤
      (2 * (a : ℚ) + 1) * ((a : ℚ) + 1) ^ 2 := by
    have hh := mul_nonneg (show (0 : ℚ) ≤ (a : ℚ) - 2 by linarith)
      (show (0 : ℚ) ≤ 2 * (a : ℚ) ^ 2 + 7 * a + 11 by positivity)
    nlinarith
  have hh := mul_le_mul_of_nonneg_right hp
    (show (0 : ℚ) ≤ 2 * ((a : ℚ) + 2) * (Nat.factorial (a + 1) : ℚ) by positivity)
  unfold oddTailRatio
  rw [Nat.factorial_succ (a + 1)]
  push_cast
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith only [hh]

theorem oddTailRatio_le_initial (a : Nat) (ha : 8 ≤ a) :
    oddTailRatio a ≤ (2754 : ℚ) / 362880 := by
  have h : oddTailRatio a ≤ oddTailRatio 8 := by
    induction a, ha using Nat.le_induction with
    | base => exact le_rfl
    | succ a ha ih => exact (oddTailRatio_step a ha).trans ih
  exact h.trans (by norm_num [oddTailRatio])

theorem half_parameter_bounds (m : Nat) (hm : 16 ≤ m) :
    8 ≤ m / 2 ∧ m / 2 ≤ m ∧ m ≤ 2 * (m / 2) + 1 ∧ m - m / 2 ≤ m / 2 + 1 := by omega

/-- The residual factorial error is bounded by its first odd case m=17. -/
theorem half_factorial_error_le (m : Nat) (hm : 16 ≤ m) :
    (m : ℚ) * ((m : ℚ) + 1) * ((m - m / 2 : Nat) : ℚ) /
      (Nat.factorial (m / 2 + 1) : ℚ) ≤ (2754 : ℚ) / 362880 := by
  have hb := half_parameter_bounds m hm
  have hmQ : (m : ℚ) ≤ 2 * ((m / 2 : Nat) : ℚ) + 1 := by exact_mod_cast hb.2.2.1
  have hdQ : ((m - m / 2 : Nat) : ℚ) ≤ ((m / 2 : Nat) : ℚ) + 1 := by
    exact_mod_cast hb.2.2.2
  have hnum : (m : ℚ) * ((m : ℚ) + 1) * ((m - m / 2 : Nat) : ℚ) ≤
      2 * (2 * ((m / 2 : Nat) : ℚ) + 1) * (((m / 2 : Nat) : ℚ) + 1) ^ 2 := by
    calc
      _ ≤ (2 * ((m / 2 : Nat) : ℚ) + 1) *
          (2 * (((m / 2 : Nat) : ℚ) + 1)) * (((m / 2 : Nat) : ℚ) + 1) := by
        gcongr
        linarith
      _ = _ := by ring
  have hratio :
      (m : ℚ) * ((m : ℚ) + 1) * ((m - m / 2 : Nat) : ℚ) /
        (Nat.factorial (m / 2 + 1) : ℚ) ≤ oddTailRatio (m / 2) := by
    exact div_le_div_of_nonneg_right hnum (by positivity)
  exact hratio.trans (oddTailRatio_le_initial (m / 2) hb.1)

theorem half_linear_error_le (m : Nat) (hm : 16 ≤ m) :
    ((m / 2 - 2 : Nat) : ℚ) * ((377 : ℚ) / 5040) / ((m - 1 : Nat) : ℚ) ≤
      ((377 : ℚ) / 5040) / 2 := by
  have hden : (0 : ℚ) < ((m - 1 : Nat) : ℚ) := by
    exact_mod_cast (show 0 < m - 1 by omega)
  have hrel : 2 * ((m / 2 - 2 : Nat) : ℚ) ≤ ((m - 1 : Nat) : ℚ) := by
    exact_mod_cast (show 2 * (m / 2 - 2) ≤ m - 1 by omega)
  apply (div_le_div_iff₀ hden (by norm_num : (0 : ℚ) < 2)).mpr
  nlinarith

theorem uniform_tail_coefficient_lt :
    (2729 : ℚ) / 5040 + ((377 : ℚ) / 5040) / 2 + 2754 / 362880 < 3 / 5 := by norm_num

/-- For m>=16 the half-size overlap already gives coefficient at most 3/5. -/
theorem circleBound_half_le_threeFifths (m : Nat) (hm : 16 ≤ m) :
    CircleBound m (m / 2) ≤
      (F3 (m + 2) : ℚ) + ((3 : ℚ) / 5) * (Fourth (m + 2) : ℚ) := by
  have hlinear := half_linear_error_le m hm
  have hfactorial := half_factorial_error_le m hm
  have hfac : (Nat.factorial (m + 1) : ℚ) =
      ((m : ℚ) + 1) * m * (Nat.factorial (m - 1) : ℚ) := by
    rw [Nat.factorial_succ, ← Nat.mul_factorial_pred (n := m) (by omega)]
    push_cast
    ring
  have htail :
      ((m - m / 2 : Nat) : ℚ) *
          min (((377 : ℚ) / 5040) * (Nat.factorial (m - 1) : ℚ) / ((m - 1 : Nat) : ℚ))
            ((Nat.factorial (m + 1) : ℚ) / (Nat.factorial (m / 2 + 1) : ℚ)) ≤
        ((m - m / 2 : Nat) : ℚ) *
          ((Nat.factorial (m + 1) : ℚ) / (Nat.factorial (m / 2 + 1) : ℚ)) :=
    mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
  have hFourth : (m + 2) - 3 = m - 1 := by omega
  unfold CircleBound
  rw [Fourth, hFourth]
  calc
    _ ≤ (F3 (m + 2) : ℚ) + ((2729 : ℚ) / 5040) * (Nat.factorial (m - 1) : ℚ) +
          ((m / 2 - 2 : Nat) : ℚ) * ((377 : ℚ) / 5040) * (Nat.factorial (m - 1) : ℚ)
            / ((m - 1 : Nat) : ℚ) +
          ((m - m / 2 : Nat) : ℚ) *
            ((Nat.factorial (m + 1) : ℚ) / (Nat.factorial (m / 2 + 1) : ℚ)) :=
      add_le_add (le_refl _) htail
    _ = (F3 (m + 2) : ℚ) +
          ((2729 : ℚ) / 5040 +
            ((m / 2 - 2 : Nat) : ℚ) * ((377 : ℚ) / 5040) / ((m - 1 : Nat) : ℚ) +
            (m : ℚ) * ((m : ℚ) + 1) * ((m - m / 2 : Nat) : ℚ) /
              (Nat.factorial (m / 2 + 1) : ℚ)) * (Nat.factorial (m - 1) : ℚ) := by
      rw [hfac]
      ring
    _ ≤ _ := by
      apply add_le_add (le_refl _)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith [uniform_tail_coefficient_lt]

/-- Every parameter m>=9 admits a certified arithmetic choice of overlap. -/
theorem exists_uniform_circle_parameter (m : Nat) (hm : 9 ≤ m) :
    ∃ a : Nat, 2 ≤ a ∧ a ≤ m ∧
      CircleBound m a ≤ (F3 (m + 2) : ℚ) + ((3 : ℚ) / 5) * (Fourth (m + 2) : ℚ) := by
  by_cases hm15 : m ≤ 15
  · exact ⟨finiteUniformParameter m, finite_uniform_parameter m hm hm15⟩
  · have h16 : 16 ≤ m := by omega
    have hb := half_parameter_bounds m h16
    exact ⟨m / 2, by omega, hb.2.1, circleBound_half_le_threeFifths m h16⟩

/-- Convert the rational inequality to the exact natural contract. -/
theorem threeFifths_nat_of_rat (K L : Nat)
    (h : (L : ℚ) ≤ (F3 K : ℚ) + ((3 : ℚ) / 5) * (Fourth K : ℚ)) :
    5 * L ≤ 5 * F3 K + 3 * Fourth K := by
  have hQ : (5 : ℚ) * L ≤ 5 * (F3 K : ℚ) + 3 * (Fourth K : ℚ) := by linarith
  exact_mod_cast hQ

/-- Conditional uniform word theorem.  The finite circle construction supplies
K>=11 and the independently supplied structural word supplies K=10. -/
theorem uniformThreeFifths_of_circleBound_and_structural10
    (hcircle : CircleBoundStatement)
    (h10 : HasSuperpermutationOfLengthAtMost 10 4035009) : UniformThreeFifthsStatement := by
  intro K hK
  by_cases hK10 : K = 10
  · subst K
    exact threeFifths_at_ten_of_structural_word h10
  have hm9 : 9 ≤ K - 2 := by omega
  obtain ⟨a, ha2, ham, hbound⟩ := exists_uniform_circle_parameter (K - 2) hm9
  obtain ⟨w, hw, hlen⟩ := hcircle (K - 2) hm9 a ha2 ham
  have hnat := threeFifths_nat_of_rat ((K - 2) + 2) w.length (hlen.trans hbound)
  have hout : ∃ w : Word (K - 2 + 2), IsSuperpermutation w ∧
      5 * w.length ≤ 5 * F3 (K - 2 + 2) + 3 * Fourth (K - 2 + 2) := ⟨w, hw, hnat⟩
  have hKeq : K - 2 + 2 = K := by omega
  exact Eq.mp (congrArg (fun n => ∃ w : Word n, IsSuperpermutation w ∧
      5 * w.length ≤ 5 * F3 n + 3 * Fourth n) hKeq) hout

#print axioms finite_uniform_parameter
#print axioms oddTailRatio_step
#print axioms oddTailRatio_le_initial
#print axioms half_factorial_error_le
#print axioms half_linear_error_le
#print axioms circleBound_half_le_threeFifths
#print axioms exists_uniform_circle_parameter
#print axioms uniformThreeFifths_of_circleBound_and_structural10

end SuperpermutationUpperBound.Bounds
