import SuperpermutationUpperBound.BalancedCuts.Fractional
import SuperpermutationUpperBound.BalancedCuts.SparseState
import SuperpermutationUpperBound.BalancedCuts.Incidence

namespace SuperpermutationUpperBound.BalancedCuts

variable {I V C : Type} [Fintype C] [DecidableEq V]

namespace ChoiceSystem

def fractionalIncidences (S : ChoiceSystem I V C) (x : C → ℚ) (v : V) : Finset C :=
  (fractionalSupport x).filter (fun c => S.incidence v c ≠ 0)

theorem stateBalance_eq_int (S : ChoiceSystem I V C) (y : C → ℚ)
    (hy : IntegralVector y) (v : V) : ∃ z : Int, S.stateBalance y v = (z : ℚ) := by
  refine ⟨∑ c, if y c = 1 then S.incidence v c else 0, ?_⟩
  simp only [stateBalance, Int.cast_sum, Int.cast_ite, Int.cast_zero]
  apply Finset.sum_congr rfl
  intro c _
  rcases hy c with hc | hc <;> simp [hc]

variable [DecidableEq I]

theorem integral_refinement_state_difference {S : ChoiceSystem I V C} {x y : C → ℚ}
    (hx : S.ItemFeasible x) (href : Refines x y) (v : V) :
    S.stateBalance y v - S.stateBalance x v =
      ∑ c ∈ S.fractionalIncidences x v, (S.incidence v c : ℚ) * (y c - x c) := by
  classical
  have he : S.stateBalance y v - S.stateBalance x v =
      ∑ c, (S.incidence v c : ℚ) * (y c - x c) := by
    simp only [stateBalance, mul_sub, Finset.sum_sub_distrib]
  rw [he]
  apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro c _ hc
  by_cases hf : c ∈ fractionalSupport x
  · have hz : S.incidence v c = 0 := by
      simpa only [fractionalIncidences, Finset.mem_filter, hf, true_and, not_not] using hc
    simp [hz]
  · rw [href c (hx.fixed_of_not_fractional hf), sub_self, mul_zero]

omit [DecidableEq I] in
theorem fractional_term_abs_lt_one (S : ChoiceSystem I V C) {x y : C → ℚ}
    (hy : IntegralVector y) {c : C} (hc : c ∈ fractionalSupport x) (v : V) :
    |(S.incidence v c : ℚ) * (y c - x c)| < 1 := by
  have hx := mem_fractionalSupport.mp hc
  have hylo : 0 ≤ y c := by rcases hy c with he | he <;> simp [he]
  have hyhi : y c ≤ 1 := by rcases hy c with he | he <;> simp [he]
  have hd : |y c - x c| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
  rcases S.incidence_values v c with hi | hi | hi
  · simpa only [hi, Int.cast_neg, Int.cast_one, neg_one_mul, abs_neg] using hd
  · simp [hi]
  · simpa [hi] using hd

/-- An active state with at most three fractional incidences is safe to drop:
every later integral refinement has absolute imbalance at most two. -/
theorem small_fractional_state_safe {S : ChoiceSystem I V C} {x : C → ℚ}
    (hx : S.ItemFeasible x) (v : V) (hv : S.stateBalance x v = 0)
    (hsmall : (S.fractionalIncidences x v).card ≤ 3) :
    ∀ y : C → ℚ, IntegralVector y → Refines x y → |S.stateBalance y v| ≤ 2 := by
  classical
  intro y hy href
  have hdiff := integral_refinement_state_difference hx href v
  rw [hv, sub_zero] at hdiff
  by_cases hne : (S.fractionalIncidences x v).Nonempty
  · have hsumlt :
        (∑ c ∈ S.fractionalIncidences x v, |(S.incidence v c : ℚ) * (y c - x c)|) <
          ((S.fractionalIncidences x v).card : ℚ) := by
      calc
        _ < ∑ _c ∈ S.fractionalIncidences x v, (1 : ℚ) :=
          Finset.sum_lt_sum_of_nonempty hne (fun c hc =>
            fractional_term_abs_lt_one S hy (Finset.mem_filter.mp hc).1 v)
        _ = _ := by simp
    have hbound : |S.stateBalance y v| < 3 := by
      rw [hdiff]
      apply lt_of_le_of_lt (Finset.abs_sum_le_sum_abs _ _)
      apply lt_of_lt_of_le hsumlt
      exact_mod_cast hsmall
    obtain ⟨z, hz⟩ := stateBalance_eq_int S y hy v
    rw [hz] at hbound ⊢
    have hzi : |z| < (3 : Int) := by exact_mod_cast hbound
    have hzle : |z| ≤ (2 : Int) := by omega
    exact_mod_cast hzle
  · have he := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [he, Finset.sum_empty] at hdiff
    simp [hdiff]

def ActiveFeasible (S : ChoiceSystem I V C) (A : Finset V) (x : C → ℚ) : Prop :=
  S.ItemFeasible x ∧ ∀ v ∈ A, S.stateBalance x v = 0

/-- Dropped states are safe for every integral refinement of the current
weights. This quantification makes the invariant persistent without storing
historical rounding steps. -/
def SafeDropped (S : ChoiceSystem I V C) (A : Finset V) (x : C → ℚ) : Prop :=
  ∀ v, v ∉ A → ∀ y : C → ℚ, IntegralVector y → Refines x y → |S.stateBalance y v| ≤ 2

omit [DecidableEq I] in
theorem SafeDropped.refine {S : ChoiceSystem I V C} {A : Finset V} {x y : C → ℚ}
    (hs : S.SafeDropped A x) (href : Refines x y) : S.SafeDropped A y := by
  intro v hv z hz hyz
  exact hs v hv z hz (href.trans hyz)

theorem SafeDropped.erase {S : ChoiceSystem I V C} {A : Finset V} {x : C → ℚ}
    (hs : S.SafeDropped A x) (hx : S.ActiveFeasible A x) {v : V} (hv : v ∈ A)
    (hsmall : (S.fractionalIncidences x v).card ≤ 3) : S.SafeDropped (A.erase v) x := by
  intro w hw y hy href
  by_cases he : w = v
  · subst w
    exact small_fractional_state_safe hx.1 v (hx.2 v hv) hsmall y hy href
  · have hnot : w ∉ A := fun hm => hw (Finset.mem_erase.mpr ⟨he, hm⟩)
    exact hs w hnot y hy href

/-- The equality-constraint column while precisely the states in `A` remain
active. Item coordinates are kept even after an item has become integral. -/
def activeColumn (S : ChoiceSystem I V C) (A : Finset V) (c : C) : I ⊕ A → ℚ :=
  Sum.elim (fun i => if S.item c = i then 1 else 0)
    (fun v => (S.incidence v c : ℚ))

theorem activeColumn_item_sum (S : ChoiceSystem I V C) (A : Finset V)
    (x : C → ℚ) (i : I) :
    (∑ c, x c • S.activeColumn A c) (Sum.inl i) = S.itemMass x i := by
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, activeColumn,
    Sum.elim_inl, mul_ite, mul_one, mul_zero, itemMass]

theorem activeColumn_state_sum (S : ChoiceSystem I V C) (A : Finset V)
    (x : C → ℚ) (v : A) :
    (∑ c, x c • S.activeColumn A c) (Sum.inr v) = S.stateBalance x v := by
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, activeColumn,
    Sum.elim_inr, stateBalance, mul_comm]

theorem ActiveFeasible.sparsify {S : ChoiceSystem I V C} {A : Finset V} {x : C → ℚ}
    (hx : S.ActiveFeasible A x) :
    ∃ y : C → ℚ, S.ActiveFeasible A y ∧ Refines x y ∧
      positiveSupport y ⊆ positiveSupport x ∧
      LinearIndependent ℚ (fun c : positiveSupport y => S.activeColumn A c) := by
  classical
  obtain ⟨y, hyn, he, hs, hi⟩ :=
    exists_nonneg_independent_support (S.activeColumn A) x hx.1.1
  have hym : S.ItemFeasible y := by
    refine ⟨hyn, fun i => ?_⟩
    have h := congrFun he (Sum.inl i)
    rw [activeColumn_item_sum, activeColumn_item_sum, hx.1.2 i] at h
    exact h
  have hya : S.ActiveFeasible A y := by
    refine ⟨hym, fun v hv => ?_⟩
    have h := congrFun he (Sum.inr (⟨v, hv⟩ : A))
    rw [activeColumn_state_sum, activeColumn_state_sum] at h
    exact h.trans (hx.2 v hv)
  exact ⟨y, hya, hx.1.refines_of_support_subset hym hs, hs, hi⟩

/-- Only unresolved item rows are needed for fractional columns. -/
def fractionalColumn (S : ChoiceSystem I V C) (A : Finset V) (x : C → ℚ)
    (c : fractionalSupport x) : S.unresolvedItems x ⊕ A → ℚ :=
  Sum.elim (fun i => if S.item c = i.val then 1 else 0)
    (fun v => (S.incidence v c : ℚ))

theorem fractionalColumn_independent {S : ChoiceSystem I V C} {A : Finset V}
    {x : C → ℚ}
    (hi : LinearIndependent ℚ (fun c : positiveSupport x => S.activeColumn A c)) :
    LinearIndependent ℚ (S.fractionalColumn A x) := by
  classical
  let f : fractionalSupport x → positiveSupport x := fun c =>
    ⟨c.val, mem_positiveSupport.mpr (mem_fractionalSupport.mp c.property).1⟩
  have hf : Function.Injective f := by
    intro c d h
    exact Subtype.ext (congrArg (fun q : positiveSupport x => q.val) h)
  have hi' : LinearIndependent ℚ (fun c : fractionalSupport x => S.activeColumn A c) :=
    hi.comp f hf
  apply Fintype.linearIndependent_iff.mpr
  intro g hg c
  apply Fintype.linearIndependent_iff.mp hi' g _ c
  funext a
  cases a with
  | inl i =>
    by_cases hm : i ∈ S.unresolvedItems x
    · have h := congrFun hg (Sum.inl (⟨i, hm⟩ : S.unresolvedItems x))
      simpa only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply,
        fractionalColumn, activeColumn, Sum.elim_inl] using h
    · simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply,
        activeColumn, Sum.elim_inl]
      apply Finset.sum_eq_zero
      intro d _
      have hne : S.item d ≠ i := by
        intro he
        exact hm (he ▸ (S.fractionalItem x d).property)
      simp [hne]
  | inr v =>
    have h := congrFun hg (Sum.inr v)
    simpa only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply,
      fractionalColumn, activeColumn, Sum.elim_inr] using h

theorem fractionalColumn_stateDegree (S : ChoiceSystem I V C) (A : Finset V)
    (x : C → ℚ) (v : A) :
    stateDegree (S.fractionalColumn A x) v = (S.fractionalIncidences x v).card := by
  classical
  let T : Finset (fractionalSupport x) :=
    Finset.univ.filter (fun c => S.incidence v c ≠ 0)
  have he : T.image Subtype.val = S.fractionalIncidences x v := by
    ext c
    simp only [T, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      fractionalIncidences]
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact ⟨d.property, hd⟩
    · rintro ⟨hc, hi⟩
      exact ⟨⟨c, hc⟩, hi, rfl⟩
  calc
    _ = T.card := by simp only [stateDegree, fractionalColumn, Sum.elim_inr,
      ne_eq, Int.cast_eq_zero, T]
    _ = (T.image Subtype.val).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ = _ := congrArg Finset.card he

theorem ActiveFeasible.exists_sparse_fractional_state
    {S : ChoiceSystem I V C} {A : Finset V} {x : C → ℚ}
    (hx : S.ActiveFeasible A x)
    (hi : LinearIndependent ℚ (fun c : positiveSupport x => S.activeColumn A c))
    (hnot : ¬ IntegralVector x) :
    ∃ v ∈ A, (S.fractionalIncidences x v).card ≤ 3 := by
  classical
  have hne : (fractionalSupport x).Nonempty := by
    by_contra h
    exact hnot (hx.1.integral_of_fractionalSupport_empty
      (Finset.not_nonempty_iff_eq_empty.mp h))
  have hn : Nonempty (fractionalSupport x) := by
    obtain ⟨c, hc⟩ := hne
    exact ⟨⟨c, hc⟩⟩
  have hcol : ∀ c : fractionalSupport x,
      columnStateDegree (S.fractionalColumn A x) c ≤ 2 := by
    intro c
    exact S.activeIncidences_card_le_two A c
  have hcancel : ∀ c : fractionalSupport x,
      columnStateDegree (S.fractionalColumn A x) c = 2 →
        ∑ v : A, S.fractionalColumn A x c (Sum.inr v) = 0 := by
    intro c hc
    exact S.activeIncidences_card_two_sum_zero A c hc
  obtain ⟨v, hv⟩ := exists_state_degree_le_three (S.fractionalColumn A x)
    (S.fractionalItem x) hn hx.1.fractional_item_degree hcol hcancel
      (fractionalColumn_independent hi)
  exact ⟨v, v.property, (S.fractionalColumn_stateDegree A x v) ▸ hv⟩

end ChoiceSystem
end SuperpermutationUpperBound.BalancedCuts
