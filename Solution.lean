import Challenge
import SuperpermutationUpperBound43.Main
import SuperpermutationUpperBound.Bounds.SharpUniform

/-! Proofs of the independent statements in `Challenge.lean`. -/

namespace SuperpermutationBounds


private theorem covers_of_construction {K : ℕ} {w : List (Fin K)}
    (h : SuperpermutationUpperBound.IsSuperpermutation w) : SuperpermutationBounds.Covers w := by
  intro p hlength hnodup
  obtain ⟨u, v, heq⟩ := h p ⟨hlength, hnodup⟩
  exact ⟨u, v, heq.symm⟩

theorem finite_bound : SuperpermutationBounds.Finite := by
  intro m a hm ha ham
  obtain ⟨w, hw, hl⟩ := SuperpermutationUpperBound43.finite_bound m hm a ha ham
  refine ⟨w, covers_of_construction hw, ?_⟩
  have hm1 : 1 ≤ m := by omega
  have hfac1 : m + 2 - 1 = m + 1 := by omega
  have hfac2 : m + 2 - 2 = m := by omega
  have hfacA : ((a : ℤ) + 1).toNat = a + 1 := by omega
  simpa only [SuperpermutationBounds.Cost, SuperpermutationBounds.F3, hfac1, hfac2, hfacA,
    Nat.cast_add, Nat.cast_sub ha, Nat.cast_sub ham, Nat.cast_sub hm1,
    Nat.cast_ofNat, Nat.cast_one, Int.cast_natCast, mul_div_assoc, mul_assoc] using hl

theorem finite_bound_integer : SuperpermutationBounds.FiniteInteger := by
  intro m a hm ha ham
  obtain ⟨w, hw, hl⟩ :=
    SuperpermutationUpperBound43.finite_bound_integer m hm a ha ham
  refine ⟨w, covers_of_construction hw, ?_⟩
  have hm1 : 1 ≤ m := by omega
  have hfac1 : m + 2 - 1 = m + 1 := by omega
  have hfac2 : m + 2 - 2 = m := by omega
  have ha0 : 0 ≤ a := by omega
  have haCast : (a.toNat : ℤ) = a := Int.toNat_of_nonneg ha0
  have hfacA : (a + 1).toNat = a.toNat + 1 := by omega
  simpa only [SuperpermutationBounds.Cost, SuperpermutationBounds.F3, hfac1, hfac2, hfacA,
    Nat.cast_add, Nat.cast_sub hm1, Nat.cast_ofNat, Nat.cast_one, mul_div_assoc, mul_assoc] using hl

theorem eventual_bound : SuperpermutationBounds.Eventual := by
  intro ε hε
  obtain ⟨N, hN, hall⟩ := SuperpermutationUpperBound43.asymptotic4380 ε hε
  refine ⟨N, hN, ?_⟩
  intro K hK
  obtain ⟨w, hw, hl⟩ := hall K hK
  refine ⟨w, covers_of_construction hw, ?_⟩
  simpa only [SuperpermutationBounds.F3, Nat.cast_add] using hl

/-- The eight-symbol construction, with its full certificate checked in Lean. -/
theorem word_eight : HasWord 8 46181 := by
  obtain ⟨w, hw, hl⟩ :=
    SuperpermutationUpperBound.Certificates.Word8.word8_46181
  exact ⟨w, covers_of_construction hw, hl⟩

/-- The certified nine-symbol construction precedes the shorter literal file. -/
theorem word_nine : HasWord 9 408743 := by
  obtain ⟨w, hw, hl⟩ :=
    SuperpermutationUpperBound.Certificates.Word9.word9_408743
  exact ⟨w, covers_of_construction hw, hl⟩

/-- A structural ten-symbol bound used in the uniform three-fifths theorem. -/
theorem word_ten_structural : HasWord 10 4035009 := by
  obtain ⟨w, hw, hl⟩ :=
    SuperpermutationUpperBound.Bounds.StructuralTen.exists_superpermutation
  exact ⟨w, covers_of_construction hw, hl⟩

/-- The uniform coefficient 3/5 is valid for every K >= 10. -/
theorem uniform_three_fifths : UniformThreeFifths := by
  intro K hK
  obtain ⟨w, hw, hl⟩ := SuperpermutationUpperBound.Bounds.uniform_three_fifths K hK
  refine ⟨w, covers_of_construction hw, ?_⟩
  simpa only [SuperpermutationUpperBound.F3,
    SuperpermutationUpperBound.Fourth] using hl

/-- The uniform coefficient 101/120 is valid for every K >= 8. -/
theorem uniform_101_over_120 : Uniform101Over120 := by
  intro K hK
  obtain ⟨w, hw, hl⟩ := SuperpermutationUpperBound.Bounds.uniform_101_over_120 K hK
  refine ⟨w, covers_of_construction hw, ?_⟩
  simpa only [SuperpermutationUpperBound.F3,
    SuperpermutationUpperBound.Fourth] using hl

end SuperpermutationBounds
