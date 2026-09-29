import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Data.Finset.Max
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Linarith

/-! Rational conic support reduction. A nullspace direction supported on the
positive variables can be followed until one positive variable becomes zero.
The move is rational, preserves nonnegativity and never restores a zero. -/
namespace SuperpermutationUpperBound.BalancedCuts

open scoped BigOperators

variable {ι : Type u} {E : Type v} [Fintype ι]
  [AddCommGroup E] [Module ℚ E]

def positiveSupport (w : ι → ℚ) : Finset ι := Finset.univ.filter (fun i => 0 < w i)

@[simp] theorem mem_positiveSupport {w : ι → ℚ} {i : ι} :
    i ∈ positiveSupport w ↔ 0 < w i := by simp [positiveSupport]

/-- One exact rational support-reducing move. The direction need only contain
a positive coordinate; other coordinates may have either sign. -/
theorem reduce_support_of_null_direction (v : ι → E) (w d : ι → ℚ)
    (hw : ∀ i, 0 ≤ w i) (hzero : ∀ i, w i = 0 → d i = 0)
    (hd : ∃ i, 0 < d i) (hnull : ∑ i, d i • v i = 0) :
    ∃ u : ι → ℚ, (∀ i, 0 ≤ u i) ∧
      (∑ i, u i • v i) = ∑ i, w i • v i ∧
      positiveSupport u ⊂ positiveSupport w := by
  let S := Finset.univ.filter (fun i => 0 < d i)
  have hS : S.Nonempty := by
    obtain ⟨i, hi⟩ := hd
    exact ⟨i, by simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]; exact hi⟩
  obtain ⟨j, hj, hmin⟩ := S.exists_min_image (fun i => w i / d i) hS
  have hdj : 0 < d j := (Finset.mem_filter.mp hj).2
  have hwj : 0 < w j := by
    have hn : w j ≠ 0 := fun he => (ne_of_gt hdj) (hzero j he)
    exact lt_of_le_of_ne (hw j) hn.symm
  let t : ℚ := w j / d j
  have ht : 0 ≤ t := div_nonneg (hw j) (le_of_lt hdj)
  let u : ι → ℚ := fun i => w i - t * d i
  have huj : u j = 0 := by simp [u, t, ne_of_gt hdj]
  have hun : ∀ i, 0 ≤ u i := by
    intro i
    change 0 ≤ w i - t * d i
    apply sub_nonneg.mpr
    by_cases hdi : 0 < d i
    · apply (le_div_iff₀ hdi).mp
      exact hmin i (by simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]; exact hdi)
    · exact le_trans (mul_nonpos_of_nonneg_of_nonpos ht (le_of_not_gt hdi)) (hw i)
  have huzero : ∀ i, w i = 0 → u i = 0 := by
    intro i hi
    simp only [u, hi, hzero i hi, mul_zero, sub_self]
  have hsubset : positiveSupport u ⊆ positiveSupport w := by
    intro i hi
    have hui : 0 < u i := mem_positiveSupport.mp hi
    apply mem_positiveSupport.mpr
    have hwi := hw i
    by_contra hnot
    have hwi0 : w i = 0 := by linarith
    rw [huzero i hwi0] at hui
    exact (lt_irrefl 0) hui
  refine ⟨u, hun, ?_, ?_⟩
  · simp only [u, sub_smul, mul_smul, Finset.sum_sub_distrib,
      ← Finset.smul_sum, hnull, smul_zero, sub_zero]
  · apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hsubset, ?_⟩
    intro heq
    have hjw : j ∈ positiveSupport w := mem_positiveSupport.mpr hwj
    have hju : j ∈ positiveSupport u := heq.symm ▸ hjw
    have hjpos := mem_positiveSupport.mp hju
    rw [huj] at hjpos
    exact (lt_irrefl 0) hjpos

variable [DecidableEq ι]

/-- Linear dependence on positive support gives a supported null direction.
Negating the relation if necessary supplies a positive coordinate. -/
theorem null_direction_of_dependent_support (v : ι → E) (w : ι → ℚ)
    (hli : ¬ LinearIndependent ℚ (fun i : positiveSupport w => v i)) :
    ∃ d : ι → ℚ, (∀ i, w i = 0 → d i = 0) ∧
      (∃ i, 0 < d i) ∧ (∑ i, d i • v i) = 0 := by
  have hdep : ¬ LinearIndepOn ℚ v (positiveSupport w : Set ι) := hli
  obtain ⟨c, hc, i, hi, hci⟩ := not_linearIndepOn_finset_iff.mp hdep
  let d : ι → ℚ := fun j => if j ∈ positiveSupport w then c j else 0
  have hdzero : ∀ j, w j = 0 → d j = 0 := by
    intro j hj
    simp [d, hj]
  have hdnull : (∑ j, d j • v j) = 0 := by
    calc
      (∑ j, d j • v j) = ∑ j ∈ positiveSupport w, d j • v j := by
        apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
        intro j _ hj
        simp only [d, if_neg hj, zero_smul]
      _ = ∑ j ∈ positiveSupport w, c j • v j := by
        apply Finset.sum_congr rfl
        intro j hj
        simp only [d, if_pos hj]
      _ = 0 := hc
  have hdi : d i = c i := by simp only [d, if_pos hi]
  by_cases hpos : 0 < c i
  · exact ⟨d, hdzero, ⟨i, by rw [hdi]; exact hpos⟩, hdnull⟩
  · refine ⟨fun j => -d j, ?_, ⟨i, ?_⟩, ?_⟩
    · intro j hj
      simp only [hdzero j hj, neg_zero]
    · change 0 < -d i
      rw [hdi]
      exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hpos) hci)
    · simp only [neg_smul, Finset.sum_neg_distrib, hdnull, neg_zero]

theorem reduce_support_of_dependent (v : ι → E) (w : ι → ℚ)
    (hw : ∀ i, 0 ≤ w i)
    (hli : ¬ LinearIndependent ℚ (fun i : positiveSupport w => v i)) :
    ∃ u : ι → ℚ, (∀ i, 0 ≤ u i) ∧
      (∑ i, u i • v i) = ∑ i, w i • v i ∧
      positiveSupport u ⊂ positiveSupport w := by
  obtain ⟨d, hz, hp, hn⟩ := null_direction_of_dependent_support v w hli
  exact reduce_support_of_null_direction v w d hw hz hp hn

/-- A rational nonnegative representation has another such representation
with linearly independent positive-support columns. No zero is restored. -/
theorem exists_nonneg_independent_support (v : ι → E) (w : ι → ℚ)
    (hw : ∀ i, 0 ≤ w i) :
    ∃ u : ι → ℚ, (∀ i, 0 ≤ u i) ∧
      (∑ i, u i • v i) = ∑ i, w i • v i ∧
      positiveSupport u ⊆ positiveSupport w ∧
      LinearIndependent ℚ (fun i : positiveSupport u => v i) := by
  classical
  suffices H : ∀ n, ∀ w : ι → ℚ, (∀ i, 0 ≤ w i) → (positiveSupport w).card = n →
      ∃ u : ι → ℚ, (∀ i, 0 ≤ u i) ∧
        (∑ i, u i • v i) = ∑ i, w i • v i ∧
        positiveSupport u ⊆ positiveSupport w ∧
        LinearIndependent ℚ (fun i : positiveSupport u => v i) by
    exact H _ w hw rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro w hw hn
    by_cases hli : LinearIndependent ℚ (fun i : positiveSupport w => v i)
    · exact ⟨w, hw, rfl, Finset.Subset.refl _, hli⟩
    · obtain ⟨u, hun, hue, hus⟩ := reduce_support_of_dependent v w hw hli
      have hcard : (positiveSupport u).card < n := by
        rw [← hn]
        exact Finset.card_lt_card hus
      obtain ⟨z, hzn, hze, hzs, hzi⟩ := ih _ hcard u hun rfl
      exact ⟨z, hzn, hze.trans hue,
        hzs.trans (Finset.ssubset_iff_subset_ne.mp hus).1, hzi⟩

omit [DecidableEq ι] in
theorem zero_of_positiveSupport_subset {u w : ι → ℚ} (hu : ∀ i, 0 ≤ u i)
    (hs : positiveSupport u ⊆ positiveSupport w) {i : ι} (hi : w i = 0) : u i = 0 := by
  have hnot : ¬ 0 < u i := by
    intro hpos
    have hp := mem_positiveSupport.mp (hs (mem_positiveSupport.mpr hpos))
    rw [hi] at hp
    exact (lt_irrefl 0) hp
  exact le_antisymm (le_of_not_gt hnot) (hu i)

/-- The finite-matrix feasibility interface for iterative rounding. The
columns indexed by positive coordinates are independent over the rationals. -/
theorem matrix_exists_nonneg_independent_support {ρ : Type w}
    (A : Matrix ρ ι ℚ) (b : ρ → ℚ) (x : ι → ℚ)
    (hx : ∀ i, 0 ≤ x i) (hfeas : A.mulVec x = b) :
    ∃ y : ι → ℚ, (∀ i, 0 ≤ y i) ∧ A.mulVec y = b ∧
      positiveSupport y ⊆ positiveSupport x ∧
      (∀ i, x i = 0 → y i = 0) ∧
      LinearIndependent ℚ (fun j : positiveSupport y => fun i => A i j) := by
  obtain ⟨y, hyn, hysum, hysub, hyind⟩ :=
    exists_nonneg_independent_support (fun j => fun i => A i j) x hx
  refine ⟨y, hyn, ?_, hysub, fun _ hi => zero_of_positiveSupport_subset hyn hysub hi, hyind⟩
  rw [← hfeas]
  funext i
  have he := congrFun hysum i
  simpa only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    mul_comm] using he

end SuperpermutationUpperBound.BalancedCuts
