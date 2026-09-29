import SuperpermutationUpperBound.Certificates.Word9
import SuperpermutationUpperBound.Partition.Iterated
import SuperpermutationUpperBound.Transport.Counts

namespace SuperpermutationUpperBound.Partition.SprintBase
open Certificates

/-- Keep the ordinary rows of the nine-symbol recipe and reserve 9 as satellite. -/
def setSatellite9 (r : Row Nat) : Row Nat := ⟨r.base, 9, r.visible⟩
def seeds9 : List (Row Nat) := NineRecipe.selectedRows.map setSatellite9

def alphabet8 : List Nat := 7 :: NineRecipe.alphabet7
def alphabet9 : List Nat := 8 :: alphabet8

/-- Exact full-chart representatives are retained, since their literal
endpoint circles are part of the finite certificate. -/
def rows8 : List (Row Nat) := Transport.packingRows seeds9 7 ++
  NineRecipe.unusedBases.flatMap (fun x => fullChart x 7 9)

def rows9 : List (Row Nat) := Transport.packingRows rows8 8

theorem seeds9_basedOn : BasedOn NineRecipe.alphabet7 9 seeds9 := by
  intro r hr
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hr
  have h := NineRecipe.seeds_basedOn t ht
  refine ⟨⟨h.1.1, ?_, h.1.2.2⟩, h.2.1, rfl, h.2.2.2⟩
  intro hm
  exact (by decide : 9 ∉ NineRecipe.alphabet7) (h.2.1.mem_iff.mp hm)

theorem unused_perm {x : List Nat} (hx : x ∈ NineRecipe.unusedBases) :
    x.Perm NineRecipe.alphabet7 :=
  (NineRecipe.accountingRows_basedOn ⟨x,7,7⟩
    (List.mem_append.mpr (Or.inr (List.mem_map_of_mem hx)))).2.1

theorem rows8_basedOn : BasedOn alphabet8 9 rows8 := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact seeds9_basedOn.transport (by decide) (by decide) r hr
  · obtain ⟨x, hx, hr⟩ := List.mem_flatMap.mp hr
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
    have hp := unused_perm hx
    have h7 : 7 ∉ x := fun hm => (by decide : 7 ∉ NineRecipe.alphabet7) (hp.mem_iff.mp hm)
    have h9 : 9 ∉ x := fun hm => (by decide : 9 ∉ NineRecipe.alphabet7) (hp.mem_iff.mp hm)
    refine ⟨fullChartAt_valid (hp.nodup_iff.mpr (by decide)) h7 h9 (by decide) j, ?_, rfl, Or.inl ?_⟩
    · exact ((rot_perm x j).append_right [7]).trans
        ((hp.append_right [7]).trans List.perm_append_comm)
    · simp

theorem rows8_complete : BlockComplete alphabet8 rows8 := by
  intro y hy
  have hp : y.Perm (NineRecipe.alphabet7 ++ [7]) :=
    hy.trans (by simpa only [alphabet8, List.cons_append, List.nil_append] using
      (List.perm_append_comm (l₁ := [7]) (l₂ := NineRecipe.alphabet7)))
  obtain ⟨x, hx, hb⟩ := exists_inInsertionBlock_of_perm_append_satellite
    (by decide : NineRecipe.alphabet7.Nodup) (by decide : NineRecipe.alphabet7 ≠ [])
    (by decide : 7 ∉ NineRecipe.alphabet7) hp
  obtain ⟨r, hr, hc⟩ := Word9.accountingRows_complete x hx
  have hb' : InInsertionBlock 7 r.base y := (InInsertionBlock.congr_base hc).mpr hb
  rcases List.mem_append.mp hr with hs | hu
  · have hm : setSatellite9 r ∈ seeds9 := List.mem_map_of_mem hs
    obtain ⟨t, ht, hc⟩ := (Transport.rows_cyclicEq_iff_inInsertionBlock
      (seeds9_basedOn _ hm).1 7 y).mpr hb'
    exact ⟨t, List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr ⟨_,hm,ht⟩)), hc⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hu
    obtain ⟨t, ht, hc⟩ := (fullChart_cyclicEq_iff_inInsertionBlock x y 7 9).mpr hb'
    exact ⟨t, List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨x,hx,ht⟩)), hc⟩

theorem rows9_basedOn : BasedOn alphabet9 9 rows9 :=
  rows8_basedOn.transport (by decide) (by decide)

theorem rows9_complete : BlockComplete alphabet9 rows9 :=
  rows8_complete.transport rows8_basedOn (by decide) (by decide) (by decide)

theorem seeds9_length : seeds9.length = 672 := by
  simp [seeds9, NineRecipe.selectedRows, NineRecipe.seedA_length, NineRecipe.seedB_length]

theorem seeds9_charge : (seeds9.map Row.charge).sum = 336 := by
  have hm : seeds9.map Row.charge = NineRecipe.selectedRows.map Row.charge := by
    simp [seeds9, List.map_map, setSatellite9, Row.charge]
  rw [hm]
  simp [NineRecipe.selectedRows, NineRecipe.seedA_charge, NineRecipe.seedB_charge]

theorem rows8_counts : rows8.length = 5040 ∧ (rows8.map Row.charge).sum = 2352 := by
  have hc := Transport.packingRows_counts seeds9 7 7 (seeds9_basedOn.ready (by decide) (by decide))
  have hf : (NineRecipe.unusedBases.flatMap (fun x => fullChart x 7 9)).length = 336 := by
    rw [List.length_flatMap]
    have he : NineRecipe.unusedBases.map (fun x => (fullChart x 7 9).length) =
        NineRecipe.unusedBases.map (fun _ => 7) := by
      apply List.map_congr_left
      intro x hx
      rw [fullChart_length, (unused_perm hx).length_eq]
      rfl
    rw [he]
    simp [NineRecipe.unusedBases_length]
  have hq : ((NineRecipe.unusedBases.flatMap (fun x => fullChart x 7 9)).map Row.charge).sum = 0 := by
    simp [List.flatMap_def, List.map_flatten, List.sum_flatten, List.map_map, Function.comp_def]
  constructor
  · simp only [rows8, List.length_append, hc.1, seeds9_length, hf]
  · simp only [rows8, List.map_append, List.sum_append, hc.2.1, seeds9_charge, hq]

theorem rows9_counts : rows9.length = 40320 ∧ (rows9.map Row.charge).sum = 18816 := by
  have hc := Transport.packingRows_counts rows8 8 8 (rows8_basedOn.ready (by decide) (by decide))
  change (Transport.packingRows rows8 8).length = 40320 ∧
    ((Transport.packingRows rows8 8).map Row.charge).sum = 18816
  constructor
  · rw [hc.1, rows8_counts.1]
  · rw [hc.2.1, rows8_counts.2]

end SuperpermutationUpperBound.Partition.SprintBase
