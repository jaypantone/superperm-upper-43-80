import SuperpermutationUpperBound.BalancedCuts.Definitions
import SuperpermutationUpperBound.BalancedCuts.SparseSupport

namespace SuperpermutationUpperBound.BalancedCuts

variable {I V C : Type}

def IntegralVector (x : C → ℚ) : Prop := ∀ c, x c = 0 ∨ x c = 1

/-- A refinement permanently fixes coordinates that have reached zero or one. -/
def Refines (x y : C → ℚ) : Prop := ∀ c, x c = 0 ∨ x c = 1 → y c = x c

theorem Refines.refl (x : C → ℚ) : Refines x x := fun _ _ => rfl

theorem Refines.trans {x y z : C → ℚ} (hxy : Refines x y) (hyz : Refines y z) :
    Refines x z := by
  intro c hc
  have he := hxy c hc
  have hy : y c = 0 ∨ y c = 1 := by simpa only [he] using hc
  exact (hyz c hy).trans he

variable [Fintype C] [DecidableEq I]

def fractionalSupport (x : C → ℚ) : Finset C :=
  Finset.univ.filter (fun c => 0 < x c ∧ x c < 1)

@[simp] theorem mem_fractionalSupport {x : C → ℚ} {c : C} :
    c ∈ fractionalSupport x ↔ 0 < x c ∧ x c < 1 := by simp [fractionalSupport]

namespace ChoiceSystem

def ItemFeasible (S : ChoiceSystem I V C) (x : C → ℚ) : Prop :=
  (∀ c, 0 ≤ x c) ∧ ∀ i, S.itemMass x i = 1

theorem Feasible.itemFeasible [DecidableEq V] {S : ChoiceSystem I V C} {x : C → ℚ}
    (hx : S.Feasible x) : S.ItemFeasible x := ⟨hx.1, hx.2.1⟩

theorem ItemFeasible.le_one {S : ChoiceSystem I V C} {x : C → ℚ}
    (hx : S.ItemFeasible x) (c : C) : x c ≤ 1 := by
  have hsum := Finset.single_le_sum
    (fun d (_ : d ∈ Finset.univ) => show 0 ≤ if S.item d = S.item c then x d else 0 from
      by split <;> first | exact hx.1 d | exact le_refl 0)
    (Finset.mem_univ c)
  rw [if_pos rfl] at hsum
  change x c ≤ S.itemMass x (S.item c) at hsum
  rw [hx.2] at hsum
  exact hsum

theorem ItemFeasible.zero_other_of_one {S : ChoiceSystem I V C} {x : C → ℚ}
    (hx : S.ItemFeasible x) {c d : C} (hc : x c = 1)
    (hd : S.item d = S.item c) (hne : d ≠ c) : x d = 0 := by
  classical
  let f : C → ℚ := fun e => if S.item e = S.item c then x e else 0
  have hf : ∀ e, 0 ≤ f e := by intro e; dsimp [f]; split <;> first | exact hx.1 e | rfl
  have hmass : ∑ e, f e = 1 := hx.2 (S.item c)
  have hsum := Finset.sum_erase_add (s := Finset.univ) (f := f) (Finset.mem_univ c)
  have hfc : f c = 1 := by simp only [f, if_pos rfl, hc]
  rw [hfc, hmass] at hsum
  have herase : ∑ e ∈ Finset.univ.erase c, f e = 0 := by linarith
  have hterm := Finset.single_le_sum (fun e (_ : e ∈ Finset.univ.erase c) => hf e)
    (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ d⟩)
  rw [herase] at hterm
  have hfd : f d = x d := by simp only [f, if_pos hd]
  rw [hfd] at hterm
  exact le_antisymm hterm (hx.1 d)

theorem ItemFeasible.refines_of_support_subset {S : ChoiceSystem I V C} {x y : C → ℚ}
    (hx : S.ItemFeasible x) (hy : S.ItemFeasible y)
    (hs : positiveSupport y ⊆ positiveSupport x) : Refines x y := by
  classical
  intro c hc
  rcases hc with hc | hc
  · rw [hc]
    exact zero_of_positiveSupport_subset hy.1 hs hc
  · have hyc : S.itemMass y (S.item c) = y c := by
      unfold itemMass
      rw [Finset.sum_eq_single c]
      · simp
      · intro d _ hdc
        by_cases hd : S.item d = S.item c
        · have hxd := hx.zero_other_of_one hc hd hdc
          simp only [if_pos hd, zero_of_positiveSupport_subset hy.1 hs hxd]
        · simp only [if_neg hd]
      · simp
    rw [hy.2] at hyc
    exact hyc.symm.trans hc.symm

theorem ItemFeasible.fixed_of_not_fractional {S : ChoiceSystem I V C} {x : C → ℚ}
    (hx : S.ItemFeasible x) {c : C} (hc : c ∉ fractionalSupport x) : x c = 0 ∨ x c = 1 := by
  have hlo := hx.1 c
  have hhi := hx.le_one c
  by_cases hz : x c = 0
  · exact Or.inl hz
  · right
    have hp : 0 < x c := lt_of_le_of_ne hlo (Ne.symm hz)
    have hn : ¬ x c < 1 := fun hlt => hc (mem_fractionalSupport.mpr ⟨hp, hlt⟩)
    exact le_antisymm hhi (le_of_not_gt hn)

theorem ItemFeasible.integral_of_fractionalSupport_empty {S : ChoiceSystem I V C} {x : C → ℚ}
    (hx : S.ItemFeasible x) (he : fractionalSupport x = ∅) : IntegralVector x := by
  intro c
  exact hx.fixed_of_not_fractional (by rw [he]; simp)

/-- A fractional candidate forces a second fractional candidate of its item. -/
theorem ItemFeasible.exists_other_fractional {S : ChoiceSystem I V C} {x : C → ℚ}
    (hx : S.ItemFeasible x) {c : C} (hc : c ∈ fractionalSupport x) :
    ∃ d, d ≠ c ∧ S.item d = S.item c ∧ d ∈ fractionalSupport x := by
  classical
  have hcx := mem_fractionalSupport.mp hc
  have hother : ∃ d, d ≠ c ∧ S.item d = S.item c ∧ 0 < x d := by
    by_contra hn
    have hsum : S.itemMass x (S.item c) = x c := by
      unfold itemMass
      rw [Finset.sum_eq_single c]
      · simp
      · intro d _ hdc
        by_cases hd : S.item d = S.item c
        · have hnp : ¬ 0 < x d := fun hp => hn ⟨d, hdc, hd, hp⟩
          have hz : x d = 0 := le_antisymm (le_of_not_gt hnp) (hx.1 d)
          simp [hd, hz]
        · simp [hd]
      · simp
    rw [hx.2] at hsum
    linarith
  obtain ⟨d, hdc, hdi, hdp⟩ := hother
  refine ⟨d, hdc, hdi, mem_fractionalSupport.mpr ⟨hdp, ?_⟩⟩
  have hdle := hx.le_one d
  have hdne : x d ≠ 1 := by
    intro hd1
    have hzero := hx.zero_other_of_one hd1 hdi.symm hdc.symm
    rw [hzero] at hcx
    exact (lt_irrefl 0) hcx.1
  exact lt_of_le_of_ne hdle hdne

def unresolvedItems (S : ChoiceSystem I V C) (x : C → ℚ) : Finset I :=
  (fractionalSupport x).image S.item

def fractionalItem (S : ChoiceSystem I V C) (x : C → ℚ)
    (c : fractionalSupport x) : unresolvedItems S x :=
  ⟨S.item c, Finset.mem_image.mpr ⟨c, c.property, rfl⟩⟩

theorem ItemFeasible.fractional_item_degree {S : ChoiceSystem I V C} {x : C → ℚ}
    (hx : S.ItemFeasible x) (i : unresolvedItems S x) :
    2 ≤ (Finset.univ.filter (fun c : fractionalSupport x => fractionalItem S x c = i)).card := by
  classical
  obtain ⟨c, hc, hci⟩ := Finset.mem_image.mp i.property
  obtain ⟨d, hdc, hdi, hd⟩ := hx.exists_other_fractional hc
  have hcitem : fractionalItem S x ⟨c, hc⟩ = i := Subtype.ext hci
  have hditem : fractionalItem S x ⟨d, hd⟩ = i := Subtype.ext (hdi.trans hci)
  have hmemc : (⟨c, hc⟩ : fractionalSupport x) ∈
      Finset.univ.filter (fun c => fractionalItem S x c = i) := by simp [hcitem]
  have hmemd : (⟨d, hd⟩ : fractionalSupport x) ∈
      Finset.univ.filter (fun c => fractionalItem S x c = i) := by simp [hditem]
  have hne : (⟨c, hc⟩ : fractionalSupport x) ≠ ⟨d, hd⟩ := by
    intro he
    exact hdc (congrArg Subtype.val he).symm
  exact Finset.one_lt_card.mpr ⟨_, hmemc, _, hmemd, hne⟩

end ChoiceSystem
end SuperpermutationUpperBound.BalancedCuts
