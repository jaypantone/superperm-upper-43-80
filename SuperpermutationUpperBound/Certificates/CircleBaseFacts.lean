import SuperpermutationUpperBound.Certificates.CircleBase

/-! Structural consequences of the finite source certificate. The second
transport is justified by the generic labelled track theorem. -/
namespace SuperpermutationUpperBound.Certificates.CircleBase
open CircleTransport Transport

theorem retag_rotate (rs : List (Row Nat)) (satellite j : Nat) :
    rot (rs.map (retag satellite)) j = (rot rs j).map (retag satellite) := by
  simp only [rot_eq_drop_append_take, List.length_map, List.map_append,
    List.map_drop, List.map_take]

theorem retag_closed {rs : List (Row Nat)} (hc : ClosedTrail rs) (satellite : Nat) :
    ClosedTrail (rs.map (retag satellite)) := by
  refine ⟨by simpa using hc.1, ?_⟩
  intro pair hp
  change pair ∈ (rs.map (retag satellite)).zip (rot (rs.map (retag satellite)) 1) at hp
  rw [retag_rotate, List.zip_map] at hp
  obtain ⟨ab, hab, rfl⟩ := List.mem_map.mp hp
  exact hc.2 ab hab

theorem retag_signedExcess (rs : List (Row Nat)) (satellite : Nat) :
    signedExcess (rs.map (retag satellite)) = signedExcess rs := by
  simp [signedExcess, List.map_map, Function.comp_def, retag, Row.charge]

theorem components8_shape (satellite : Nat) : ∀ rs ∈ components8 satellite, ∀ r ∈ rs,
    r.base.length = 8 ∧ r.satellite = satellite ∧
      (r.visible = r.base.length ∨ r.visible = r.base.length - 2) := by
  intro rs hrs r hr
  obtain ⟨ts, hts, rfl⟩ := List.mem_map.mp hrs
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hr
  have hh := rawComponents8_shape ts hts t ht
  exact ⟨hh.1, rfl, hh.2.2⟩

theorem components8_closed (satellite : Nat) : ∀ rs ∈ components8 satellite, ClosedTrail rs := by
  intro rs hrs
  obtain ⟨ts, hts, rfl⟩ := List.mem_map.mp hrs
  exact retag_closed (rawComponents8_closed ts hts) satellite

theorem components8_winding (satellite : Nat) :
    ∀ rs ∈ components8 satellite, (7 : Int) ∣ signedExcess rs := by
  intro rs hrs
  obtain ⟨ts, hts, rfl⟩ := List.mem_map.mp hrs
  rw [retag_signedExcess]
  exact rawComponents8_winding ts hts

theorem components8_nine : components8 9 = rawComponents8 := by
  unfold components8
  conv_rhs => rw [← List.map_id rawComponents8]
  apply List.map_congr_left
  intro rs hrs
  conv_rhs => rw [← List.map_id rs]
  apply List.map_congr_left
  intro r hr
  have he := (rawComponents8_shape rs hrs r hr).2.1
  cases r
  simp_all [retag]

theorem components8_inventory : (components8 9).flatten.Perm Partition.SprintBase.rows8 := by
  rw [components8_nine]
  exact rawComponents8_inventory

theorem components9_inventory : components9.flatten.Perm Partition.SprintBase.rows9 := by
  have hlocal : ∀ rs ∈ components8 9,
      ((List.range 7).flatMap (transportWalk rs 8)).Perm (packingRows rs 8) := by
    intro rs hrs
    have hi := transportWalk_inventory rs 8 7 (by decide)
      (fun r hr => (components8_shape 9 rs hrs r hr).1)
    simpa only [← map_val_finRange, List.flatMap_map] using hi
  have he : components9.flatten.Perm ((components8 9).flatMap (fun rs => packingRows rs 8)) := by
    simpa only [components9, List.flatten_eq_flatMap, List.flatMap_assoc, List.flatMap_map, id_eq] using
      (List.Perm.flatMap (List.Perm.refl (components8 9)) hlocal)
  exact he.trans (by
    simpa only [Partition.SprintBase.rows9, packingRows, List.flatten_eq_flatMap, List.flatMap_assoc, id_eq] using
      components8_inventory.flatMap_right (fun r => rows r 8))

theorem components9_basedOn : ∀ rs ∈ components9,
    BasedOn Partition.SprintBase.alphabet9 9 rs := by
  intro rs hrs r hr
  exact Partition.SprintBase.rows9_basedOn r
    (components9_inventory.mem_iff.mp (List.mem_flatten.mpr ⟨rs, hrs, hr⟩))

theorem components9_shape : ∀ rs ∈ components9, ∀ r ∈ rs,
    r.base.length = 9 ∧ r.satellite = 9 ∧
      (r.visible = r.base.length ∨ r.visible = r.base.length - 2) := by
  intro rs hrs r hr
  have hh := components9_basedOn rs hrs r hr
  exact ⟨hh.2.1.length_eq, hh.2.2⟩

theorem components9_closed_winding : ∀ rs ∈ components9,
    ClosedTrail rs ∧ (8 : Int) ∣ signedExcess rs := by
  intro ts hts
  obtain ⟨rs, hrs, hts⟩ := List.mem_flatMap.mp hts
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hts
  have hp' := List.mem_range.mp hp
  have hl := fun r hr => (components8_shape 9 rs hrs r hr).1
  have hk := fun r hr => (components8_shape 9 rs hrs r hr).2.2
  exact ⟨transportWalk_closedTrail (components8_closed 9 rs hrs) 8 7 (by decide)
      hl hk (components8_winding 9 rs hrs) p hp',
    transportWalk_winding_divisible rs 8 7 (by decide) hl hk
      (components8_winding 9 rs hrs) p hp'⟩

theorem family9_inventory : ((List.finRange 364).flatMap family9).Perm Partition.SprintBase.rows9 := by
  have he : (List.finRange 364).map family9 = components9 := by
    apply List.ext_getElem
    · simp [components9_count]
    · intro i hi hj
      simp [family9, componentAt, List.getElem?_eq_getElem hj]
  simpa only [List.flatMap_def, he] using components9_inventory

theorem family9_closed_winding (i : Fin 364) :
    ClosedTrail (family9 i) ∧ (8 : Int) ∣ signedExcess (family9 i) :=
  components9_closed_winding _ (componentAt_mem _ i.val (by rw [components9_count]; exact i.isLt))

end SuperpermutationUpperBound.Certificates.CircleBase
