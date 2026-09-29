import SuperpermutationUpperBound.Partition.SeedBase
import SuperpermutationUpperBound.Partition.FullCharts

/-! The actual row selection at old ordinary size seven: transport the 96
seed rows, then fill each of the 24 missing old blocks by its closed full
chart. The mixed-component orbit assembly is a separate theorem. -/
namespace SuperpermutationUpperBound.Partition.OriginalSeven

open SeedBase Transport

def mixedRows7 : List (Row Nat) := packingRows seedRowsNat 7
def fullCharts7 : List (List (Row Nat)) := unusedBases6.map (fun x => fullChart x 7 6)
def chartRows7 : List (Row Nat) := fullCharts7.flatten
def rows7 : List (Row Nat) := mixedRows7 ++ chartRows7
def alphabet7 : List Nat := 7 :: alphabet6

private theorem fresh_seven : 7 ∉ alphabet6 := by decide

private theorem unused_properties {x : List Nat} (hx : x ∈ unusedBases6) :
    x.Perm alphabet6 ∧ x.Nodup ∧ x.length = 6 ∧ 7 ∉ x ∧ 6 ∉ x := by
  have hp := canonicalBases6_perm (mem_unusedBases6.mp hx).1
  refine ⟨hp, hp.nodup_iff.mpr (by decide), hp.length_eq, ?_, ?_⟩
  · exact fun h => fresh_seven (hp.mem_iff.mp h)
  · intro h
    have hh := hp.mem_iff.mp h
    simp [alphabet6] at hh

private theorem chart_member_block {x : List Nat} {r : Row Nat}
    (hx : x ∈ unusedBases6) (hr : r ∈ fullChart x 7 6) : InInsertionBlock 7 x r.base := by
  have hl := fullChart_base_length x 7 6 r hr
  exact (fullChart_cyclicEq_iff_inInsertionBlock x r.base 7 6).mp
    ⟨r, hr, CyclicEq.refl (by intro he; rw [he] at hl; simp at hl)⟩

theorem mixedRows7_basedOn : BasedOn alphabet7 6 mixedRows7 :=
  seedRowsNat_basedOn.transport fresh_seven (by decide)

theorem rows7_basedOn : BasedOn alphabet7 6 rows7 := by
  intro r hr
  rcases List.mem_append.mp hr with hm | hc
  · exact mixedRows7_basedOn r hm
  · obtain ⟨x, hx, hr⟩ := List.mem_flatMap.mp hc
    have hp := unused_properties hx
    have hv := fullChart_valid hp.2.1 hp.2.2.2.1 hp.2.2.2.2 (by decide) r hr
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
    refine ⟨hv, ?_, rfl, Or.inl ?_⟩
    · exact ((rot_perm x j).trans hp.1 |>.append_right [7]).trans
        (by simpa [alphabet7] using (List.perm_append_comm (l₁ := alphabet6) (l₂ := [7])))
    · simp [fullChartAt]

theorem rows7_complete : BlockComplete alphabet7 rows7 := by
  have hc := accountingRows6_complete.transport accountingRows6_basedOn
    (by decide : alphabet6.Nodup) (by decide : alphabet6 ≠ []) fresh_seven
  intro y hy
  obtain ⟨t, ht, hty⟩ := hc y hy
  obtain ⟨r, hr, ht⟩ := List.mem_flatMap.mp ht
  rcases List.mem_append.mp hr with hs | hf
  · exact ⟨t, List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr ⟨r, hs, ht⟩)), hty⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hf
    have hblock : InInsertionBlock 7 x y :=
      (rows_cyclicEq_iff_inInsertionBlock
        (accountingRows6_basedOn _ (List.mem_append.mpr
          (Or.inr (List.mem_map.mpr ⟨x, hx, rfl⟩)))).1 7 y).mp ⟨t, ht, hty⟩
    obtain ⟨u, hu, huy⟩ := (fullChart_cyclicEq_iff_inInsertionBlock x y 7 6).mpr hblock
    exact ⟨u, List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨x, hx, hu⟩)), huy⟩

theorem chartRows7_distinct : DistinctBlocks chartRows7 := by
  apply List.pairwise_flatMap.mpr
  refine ⟨?_, ?_⟩
  · intro x hx
    have hp := unused_properties hx
    exact fullChart_pairwise_not_cyclicEq 6 hp.2.1 hp.2.2.2.1
  · have hd : unusedBases6.Pairwise (fun x y => ¬ CyclicEq x y) :=
      canonicalBases6_distinct.filter _
    apply hd.imp_of_mem
    intro x y hx hy hxy r hr t ht hrt
    have hxb : InInsertionBlock 7 x t.base :=
      (fullChart_cyclicEq_iff_inInsertionBlock x t.base 7 6).mp ⟨r, hr, hrt⟩
    exact hxy (hxb.unique_base (chart_member_block hy ht)
      (unused_properties hx).2.2.2.1 (unused_properties hy).2.2.2.1)

theorem rows7_distinct : DistinctBlocks rows7 := by
  apply List.pairwise_append.mpr
  refine ⟨seedRowsNat_distinct.transport seedRowsNat_basedOn fresh_seven,
    chartRows7_distinct, ?_⟩
  intro t ht u hu htu
  obtain ⟨r, hr, ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨x, hx, hu⟩ := List.mem_flatMap.mp hu
  have hb := seedRowsNat_basedOn r hr
  have hnew : InInsertionBlock 7 r.base u.base :=
    (rows_cyclicEq_iff_inInsertionBlock hb.1 7 u.base).mp ⟨t, ht, htu⟩
  have hzr : 7 ∉ r.base := fun h => fresh_seven (hb.2.1.mem_iff.mp h)
  exact (mem_unusedBases6.mp hx).2 r hr
    (hnew.unique_base (chart_member_block hx hu) hzr (unused_properties hx).2.2.2.1)

theorem mixedRows7_length : mixedRows7.length = 576 := by
  have h := packingRows_length seedRowsNat 7 6
    (seedRowsNat_basedOn.ready fresh_seven (by decide))
  simpa [mixedRows7, seedRowsNat_length] using h

theorem mixedRows7_charge : (mixedRows7.map Row.charge).sum = 288 := by
  have h := packingRows_charge_sum seedRowsNat 7 6
    (seedRowsNat_basedOn.ready fresh_seven (by decide))
  simpa [mixedRows7, seedRowsNat_charge] using h

theorem chartRows7_length : chartRows7.length = 144 := by
  have haux : ∀ xs : List (List Nat), (∀ x ∈ xs, x.length = 6) →
      (xs.flatMap (fun x => fullChart x 7 6)).length = 6 * xs.length := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih =>
      intro h
      simp only [List.flatMap_cons, List.length_append, fullChart_length, List.length_cons]
      rw [h x (by simp), ih (fun y hy => h y (List.mem_cons_of_mem _ hy)), Nat.mul_succ]
      omega
  have h := haux unusedBases6 (fun x hx => (unused_properties hx).2.2.1)
  simpa [chartRows7, fullCharts7, List.flatMap, unusedBases6_length] using h

theorem chartRows7_charge : (chartRows7.map Row.charge).sum = 0 := by
  apply List.sum_eq_zero_iff_forall_eq_nat.mpr
  intro c hc
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hc
  obtain ⟨x, _, hr⟩ := List.mem_flatMap.mp hr
  exact fullChart_charge x 7 6 r hr

theorem rows7_length : rows7.length = 720 := by
  simp [rows7, mixedRows7_length, chartRows7_length]

theorem rows7_charge : (rows7.map Row.charge).sum = 288 := by
  simp [rows7, List.map_append, mixedRows7_charge, chartRows7_charge]

theorem fullCharts7_closed : ∀ rs ∈ fullCharts7, ClosedTrail rs := by
  intro rs hrs
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hrs
  exact fullChart_closedTrail x 7 6 (by have := (unused_properties hx).2.2.1; omega)

/-- The paper's correct row selection at size seven, with closed missing-block
charts. Closed mixed components are deliberately a separate theorem. -/
theorem rows7_certificate :
    BasedOn alphabet7 6 rows7 ∧ BlockComplete alphabet7 rows7 ∧ DistinctBlocks rows7 ∧
    rows7.length = 720 ∧ (rows7.map Row.charge).sum = 288 ∧
    fullCharts7.length = 24 ∧ (∀ rs ∈ fullCharts7, ClosedTrail rs) := by
  exact ⟨rows7_basedOn, rows7_complete, rows7_distinct, rows7_length, rows7_charge,
    by simp [fullCharts7, unusedBases6_length], fullCharts7_closed⟩

end SuperpermutationUpperBound.Partition.OriginalSeven
