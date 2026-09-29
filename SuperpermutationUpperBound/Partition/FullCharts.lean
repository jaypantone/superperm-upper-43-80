import SuperpermutationUpperBound.Transport.Ports
import SuperpermutationUpperBound.Transport.Blocks

/-! A missing old cyclic block is filled by its full chart in rotation order. -/
namespace SuperpermutationUpperBound.Partition

open Transport

variable {α : Type}

def fullChartAt (x : List α) (z s : α) (j : Nat) : Row α :=
  ⟨rot x j ++ [z], s, x.length + 1⟩

def fullChart (x : List α) (z s : α) : List (Row α) :=
  (List.range x.length).map (fullChartAt x z s)

@[simp] theorem fullChart_length (x : List α) (z s : α) :
    (fullChart x z s).length = x.length := by simp [fullChart]

@[simp] theorem fullChartAt_length (x : List α) (z s : α) (j : Nat) :
    (fullChartAt x z s j).base.length = x.length + 1 := by simp [fullChartAt]

@[simp] theorem fullChartAt_visible (x : List α) (z s : α) (j : Nat) :
    (fullChartAt x z s j).visible = x.length + 1 := rfl

@[simp] theorem fullChartAt_charge (x : List α) (z s : α) (j : Nat) :
    (fullChartAt x z s j).charge = 0 := by simp [Row.charge]

theorem fullChartAt_valid {x : List α} {z s : α} (hx : x.Nodup)
    (hz : z ∉ x) (hs : s ∉ x) (hsz : s ≠ z) (j : Nat) :
    (fullChartAt x z s j).Valid := by
  have hzrot : z ∉ rot x j := fun hm => hz ((rot_perm x j).mem_iff.mp hm)
  have hsrot : s ∉ rot x j := fun hm => hs ((rot_perm x j).mem_iff.mp hm)
  refine ⟨?_, ?_, by simp, by simp⟩
  · exact ((List.perm_append_comm (l₁ := rot x j) (l₂ := [z])).nodup_iff).mpr
      (by simpa using List.nodup_cons.mpr ⟨hzrot, rot_nodup hx j⟩)
  · simpa only [fullChartAt, List.mem_append, List.mem_singleton, not_or] using And.intro hsrot hsz

theorem fullChartAt_head (x : List α) (z s : α) (j : Nat) (hn : 1 ≤ x.length) :
    (fullChartAt x z s j).head = (rot x j).take (x.length - 1) := by
  simp only [fullChartAt, Row.head, List.length_append, List.length_singleton, rot_length]
  have hlen : x.length + 1 - 2 = x.length - 1 := by omega
  rw [hlen, List.take_append_of_le_length (by simp)]

theorem fullChartAt_tail (x : List α) (z s : α) (j : Nat) (hn : 1 ≤ x.length) :
    (fullChartAt x z s j).tail = (rot x j).drop 1 := by
  have h := row_full_tail (rot x j ++ [z]) s (by simp; omega)
  simp only [List.length_append, List.length_singleton, rot_length] at h
  change (Row.mk (rot x j ++ [z]) s (x.length + 1)).tail = _
  rw [h, List.drop_append_of_le_length (by simp; omega)]
  have hlen : x.length + 1 - 2 = ((rot x j).drop 1).length := by simp
  rw [hlen, List.take_append_length]

theorem fullChartAt_compatible (x : List α) (z s : α) (j : Nat) (hn : 1 ≤ x.length) :
    (fullChartAt x z s j).Compatible (fullChartAt x z s (j + 1)) := by
  unfold Row.Compatible
  rw [fullChartAt_tail x z s j hn, fullChartAt_head x z s (j + 1) hn, rot_add_one]
  have ht := take_rot_eq_drop (rot x j) 1 (by simp; omega)
  simpa only [rot_length] using ht.symm

@[simp] theorem fullChartAt_mod (x : List α) (z s : α) (j : Nat) :
    fullChartAt x z s (j % x.length) = fullChartAt x z s j := by
  simp only [fullChartAt, rot_mod]

theorem fullChart_cyclicallyCompatible (x : List α) (z s : α) (hn : 1 ≤ x.length) :
    CyclicallyCompatible (fullChart x z s) := by
  intro pair hp
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hp
  simp only [List.getElem_zip]
  rw [getElem_rot]
  simp only [fullChart, List.getElem_map, List.getElem_range,
    List.length_map, List.length_range, fullChartAt_mod]
  rw [Nat.add_comm 1 j]
  exact fullChartAt_compatible x z s j hn

/-- The literal chart closes in its specified rotation order. -/
theorem fullChart_closedTrail (x : List α) (z s : α) (hn : 1 ≤ x.length) :
    ClosedTrail (fullChart x z s) := by
  refine ⟨?_, fullChart_cyclicallyCompatible x z s hn⟩
  intro heq
  have hlen := fullChart_length x z s
  rw [heq, List.length_nil] at hlen
  omega

theorem fullChart_valid {x : List α} {z s : α} (hx : x.Nodup)
    (hz : z ∉ x) (hs : s ∉ x) (hsz : s ≠ z) :
    ∀ r ∈ fullChart x z s, r.Valid := by
  intro r hr
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
  exact fullChartAt_valid hx hz hs hsz j

theorem fullChart_visible (x : List α) (z s : α) :
    ∀ r ∈ fullChart x z s, r.visible = x.length + 1 := by
  intro r hr
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
  rfl

theorem fullChart_base_length (x : List α) (z s : α) :
    ∀ r ∈ fullChart x z s, r.base.length = x.length + 1 := by
  intro r hr
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
  exact fullChartAt_length x z s j

theorem fullChart_charge (x : List α) (z s : α) :
    ∀ r ∈ fullChart x z s, r.charge = 0 := by
  intro r hr
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
  exact fullChartAt_charge x z s j

@[simp] theorem fullChart_charge_sum (x : List α) (z s : α) :
    ((fullChart x z s).map Row.charge).sum = 0 := by
  have hzero : ∀ xs : List Nat, (xs.map (fun _ => 0)).sum = 0 := by
    intro xs
    induction xs with
    | nil => rfl
    | cons a xs ih => simp [ih]
  simpa [fullChart, List.map_map, Function.comp_def] using hzero (List.range x.length)

/-- The chart has exactly the extension classes belonging to its old base. -/
theorem fullChart_cyclicEq_iff_inInsertionBlock (x y : List α) (z s : α) :
    (∃ r ∈ fullChart x z s, CyclicEq r.base y) ↔ InInsertionBlock z x y := by
  constructor
  · intro ⟨r, hr, hry⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
    exact ⟨⟨j, List.mem_range.mp hj⟩, hry⟩
  · intro ⟨j, hj⟩
    exact ⟨fullChartAt x z s j,
      List.mem_map.mpr ⟨j.val, List.mem_range.mpr j.isLt, rfl⟩, hj⟩

theorem fullChart_same_extensions_as_fullBases (x y : List α) (z s : α) :
    (∃ r ∈ fullChart x z s, CyclicEq r.base y) ↔
      ∃ b ∈ fullBases x z, CyclicEq b y := by
  rw [fullChart_cyclicEq_iff_inInsertionBlock,
    fullBases_cyclicEq_iff_inInsertionBlock]

/-- Distinct chart occurrences belong to distinct cyclic base blocks. -/
theorem fullChart_pairwise_not_cyclicEq {x : List α} {z : α} (s : α)
    (hx : x.Nodup) (hz : z ∉ x) :
    (fullChart x z s).Pairwise (fun r t => ¬ CyclicEq r.base t.base) := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij hc
  have hi' : i < x.length := by simpa using hi
  have hj' : j < x.length := by simpa using hj
  simp only [fullChart, List.getElem_map, List.getElem_range, fullChartAt] at hc
  have he := (entry_cyclicEq_iff_index_eq hx hz hi' hj').mp hc
  omega

/-- A full chart supplies a closed, charge-zero packing of every extension
of one missing old cyclic base block. -/
theorem fullChart_certificate {x : List α} {z s : α} (hn : 1 ≤ x.length)
    (hx : x.Nodup) (hz : z ∉ x) (hs : s ∉ x) (hsz : s ≠ z) :
    (fullChart x z s).length = x.length ∧
      ClosedTrail (fullChart x z s) ∧
      (∀ r ∈ fullChart x z s,
        r.Valid ∧ r.base.length = x.length + 1 ∧ r.visible = x.length + 1 ∧ r.charge = 0) ∧
      (fullChart x z s).Pairwise (fun r t => ¬ CyclicEq r.base t.base) ∧
      ((fullChart x z s).map Row.charge).sum = 0 ∧
      ∀ y, (∃ r ∈ fullChart x z s, CyclicEq r.base y) ↔ InInsertionBlock z x y := by
  refine ⟨fullChart_length x z s, fullChart_closedTrail x z s hn, ?_,
    fullChart_pairwise_not_cyclicEq s hx hz, fullChart_charge_sum x z s, ?_⟩
  · intro r hr
    exact ⟨fullChart_valid hx hz hs hsz r hr, fullChart_base_length x z s r hr,
      fullChart_visible x z s r hr, fullChart_charge x z s r hr⟩
  · intro y
    exact fullChart_cyclicEq_iff_inInsertionBlock x y z s

end SuperpermutationUpperBound.Partition
