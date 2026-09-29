import SuperpermutationUpperBound.Transport.Local
import SuperpermutationUpperBound.Packing

/-!
Local transport covers exactly the satellite-insertion blocks over the old
base. The final short descendant uses a different literal orientation, and
the proof retains its established rotation witness.
-/

namespace SuperpermutationUpperBound.Transport

variable {α : Type} {x y : List α} {z : α}

theorem insertLetter_cyclicEq_entry (x : List α) (z : α) (j : Nat)
    (hj : j ≤ x.length) :
    CyclicEq (insertLetter x z j) (rot x j ++ [z]) := by
  have hn : insertLetter x z j ≠ [] := by
    apply List.length_pos_iff.mp
    simp
  have he := rot_insertLetter_at_cut x z j
  rw [← rot_eq_drop_append_take_of_le x j hj] at he
  have hc := CyclicEq.of_rot hn ((x.take j).length + 1)
  exact Eq.mp (congrArg (fun w => CyclicEq (insertLetter x z j) w) he) hc

theorem fullBases_cyclicEq_iff_inInsertionBlock (x y : List α) (z : α) :
    (∃ b ∈ fullBases x z, CyclicEq b y) ↔ InInsertionBlock z x y := by
  constructor
  · intro ⟨b, hb, hby⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
    have hj' : j < x.length := List.mem_range.mp hj
    exact ⟨⟨j, hj'⟩,
      (insertLetter_cyclicEq_entry x z j (Nat.le_of_lt hj')).symm.trans hby⟩
  · intro ⟨j, hj⟩
    refine ⟨insertLetter x z j.val,
      List.mem_map.mpr ⟨j.val, List.mem_range.mpr j.isLt, rfl⟩, ?_⟩
    exact (insertLetter_cyclicEq_entry x z j.val (Nat.le_of_lt j.isLt)).trans hj

theorem shortBases_cyclicEq_iff_inInsertionBlock (x y : List α) (z : α)
    (hn : 1 ≤ x.length) :
    (∃ b ∈ shortBases x z, CyclicEq b y) ↔ InInsertionBlock z x y := by
  constructor
  · intro ⟨b, hb, hby⟩
    rcases List.mem_append.mp hb with hi | he
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      have hj' : j < x.length - 1 := List.mem_range.mp hj
      have hjn : j < x.length := by omega
      exact ⟨⟨j, hjn⟩,
        (insertLetter_cyclicEq_entry x z j (Nat.le_of_lt hjn)).symm.trans hby⟩
    · have heq : b = rot x (x.length - 1) ++ [z] := List.mem_singleton.mp he
      exact ⟨⟨x.length - 1, by omega⟩, heq ▸ hby⟩
  · intro ⟨j, hj⟩
    by_cases hjlast : j.val = x.length - 1
    · refine ⟨rot x (x.length - 1) ++ [z],
        List.mem_append.mpr (Or.inr (List.mem_singleton_self _)), ?_⟩
      simpa only [hjlast] using hj
    · have hjlt : j.val < x.length - 1 := by omega
      refine ⟨insertLetter x z j.val,
        List.mem_append.mpr (Or.inl (List.mem_map.mpr
          ⟨j.val, List.mem_range.mpr hjlt, rfl⟩)), ?_⟩
      exact (insertLetter_cyclicEq_entry x z j.val (Nat.le_of_lt j.isLt)).trans hj

theorem fullRows_cyclicEq_iff_inInsertionBlock (r : Row α) (z : α) (y : List α) :
    (∃ t ∈ fullRows r z, CyclicEq t.base y) ↔ InInsertionBlock z r.base y := by
  rw [← fullBases_cyclicEq_iff_inInsertionBlock r.base y z]
  constructor
  · intro ⟨t, ht, hty⟩
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
    exact ⟨b, hb, hty⟩
  · intro ⟨b, hb, hby⟩
    exact ⟨⟨b, r.satellite, r.base.length + 1⟩, List.mem_map.mpr ⟨b, hb, rfl⟩, hby⟩

theorem shortRows_cyclicEq_iff_inInsertionBlock (r : Row α) (z : α) (y : List α)
    (hn : 1 ≤ r.base.length) :
    (∃ t ∈ shortRows r z, CyclicEq t.base y) ↔ InInsertionBlock z r.base y := by
  rw [← shortBases_cyclicEq_iff_inInsertionBlock r.base y z hn]
  constructor
  · intro ⟨t, ht, hty⟩
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
    exact ⟨b, hb, hty⟩
  · intro ⟨b, hb, hby⟩
    exact ⟨⟨b, r.satellite, r.base.length - 1⟩, List.mem_map.mpr ⟨b, hb, rfl⟩, hby⟩

/-- The actual descendant list meets precisely all insertion blocks over its
old cyclic base. Validity supplies the only necessary size hypothesis; the
block statement itself does not require freshness or a full/short deficit.
-/
theorem rows_cyclicEq_iff_inInsertionBlock {r : Row α} (hr : r.Valid)
    (z : α) (y : List α) :
    (∃ t ∈ rows r z, CyclicEq t.base y) ↔ InInsertionBlock z r.base y := by
  have hn : 1 ≤ r.base.length := Nat.le_trans hr.2.2.1 hr.2.2.2
  unfold rows
  split
  · exact fullRows_cyclicEq_iff_inInsertionBlock r z y
  · exact shortRows_cyclicEq_iff_inInsertionBlock r z y hn

theorem rows_base_nonempty {r t : Row α} (ht : t ∈ rows r z) : t.base ≠ [] := by
  have hn : t.base.length = r.base.length + 1 := by
    unfold rows at ht
    split at ht
    · exact fullRows_base_length ht
    · exact shortRows_base_length ht
  exact List.length_pos_iff.mp (by omega)

theorem rows_base_inInsertionBlock {r t : Row α} (hr : r.Valid)
    (ht : t ∈ rows r z) : InInsertionBlock z r.base t.base :=
  (rows_cyclicEq_iff_inInsertionBlock hr z t.base).mp
    ⟨t, ht, CyclicEq.refl (rows_base_nonempty ht)⟩

/-- Deleting the new ordinary letter from a descendant recovers its old cyclic
base block. This supplies the inverse needed by all-size coverage induction.
-/
theorem rows_base_eraseSatellite [DecidableEq α] {r t : Row α} (hr : r.Valid)
    (hz : z ∉ r.base) (ht : t ∈ rows r z) :
    CyclicEq r.base (eraseSatellite z t.base) :=
  (rows_base_inInsertionBlock hr ht).cyclicEq_eraseSatellite hz

/-- Descendants from distinct old cyclic blocks cannot share a new block. -/
theorem rows_cyclicEq_implies_old_cyclicEq [DecidableEq α] {r q t u : Row α}
    (hr : r.Valid) (hq : q.Valid) (hzr : z ∉ r.base) (hzq : z ∉ q.base)
    (ht : t ∈ rows r z) (hu : u ∈ rows q z) (hnew : CyclicEq t.base u.base) :
    CyclicEq r.base q.base := by
  have hrt : InInsertionBlock z r.base u.base :=
    (rows_cyclicEq_iff_inInsertionBlock hr z u.base).mp ⟨t, ht, hnew⟩
  exact hrt.unique_base (rows_base_inInsertionBlock hq hu) hzr hzq

/-- A fresh final letter fixes the literal orientation of a cyclic class. -/
theorem append_satellite_eq_of_cyclicEq {a b : List α} {z : α}
    (hz : z ∉ a) (h : CyclicEq (a ++ [z]) (b ++ [z])) : a = b := by
  have hlen : a.length = b.length := by
    have hl := h.length_eq
    simpa using hl
  obtain ⟨j, hj⟩ := h
  have hjn : j.val ≤ a.length := by have := j.isLt; simp only [List.length_append,
    List.length_singleton] at this; omega
  have hlast : (rot (a ++ [z]) j.val)[a.length]'(by simp) = z := by
    have he := congrArg (fun w : List α => w[a.length]?) hj
    have hl : (b ++ [z])[a.length]? = some z := by simp [hlen]
    have hh : (rot (a ++ [z]) j.val)[a.length]? = some z := he.trans hl
    obtain ⟨_, helem⟩ := List.getElem_of_getElem? hh
    exact helem
  have hjzero : j.val = 0 := by
    by_cases hn : j.val = 0
    · exact hn
    exfalso
    have hjpos : 0 < j.val := by omega
    rw [getElem_rot] at hlast
    have hm : (j.val + a.length) % (a ++ [z]).length = j.val - 1 := by
      simp only [List.length_append, List.length_singleton]
      have he : j.val + a.length = (j.val - 1) + (a.length + 1) := by omega
      rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    have hv : a[j.val - 1]'(by omega) = z := by
      simpa only [hm, List.getElem_append_left (as := a) (bs := [z])
        (i := j.val - 1) (by omega)] using hlast
    exact hz (hv ▸ List.getElem_mem (by omega : j.val - 1 < a.length))
  have he : a ++ [z] = b ++ [z] := by simpa only [hjzero, rot_zero] using hj
  exact List.append_cancel_right he

/-- Distinct positions of a duplicate-free word give distinct rotations. -/
theorem rot_index_eq_of_nodup {x : List α} (hx : x.Nodup) {i j : Nat}
    (hi : i < x.length) (hj : j < x.length) (he : rot x i = rot x j) : i = j := by
  have hip : 0 < (rot x i).length := by simp; omega
  have hjp : 0 < (rot x j).length := by simp; omega
  have hh := congrArg (fun w : List α => w[0]?) he
  simp only [List.getElem?_eq_getElem hip, List.getElem?_eq_getElem hjp,
    Option.some.injEq] at hh
  have hh' : x[i] = x[j] := by
    simpa only [getElem_rot, Nat.add_zero, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using hh
  exact (List.getElem_inj hx).mp hh'

theorem entry_cyclicEq_iff_index_eq {x : List α} {z : α} (hx : x.Nodup)
    (hz : z ∉ x) {i j : Nat} (hi : i < x.length) (hj : j < x.length) :
    CyclicEq (rot x i ++ [z]) (rot x j ++ [z]) ↔ i = j := by
  constructor
  · intro he
    have hzi : z ∉ rot x i := fun hm => hz ((rot_perm x i).mem_iff.mp hm)
    exact rot_index_eq_of_nodup hx hi hj (append_satellite_eq_of_cyclicEq hzi he)
  · intro he
    subst j
    exact CyclicEq.refl (by simp)

theorem insertLetter_cyclicEq_iff_index_eq {x : List α} {z : α} (hx : x.Nodup)
    (hz : z ∉ x) {i j : Nat} (hi : i < x.length) (hj : j < x.length) :
    CyclicEq (insertLetter x z i) (insertLetter x z j) ↔ i = j := by
  constructor
  · intro he
    have hc := (insertLetter_cyclicEq_entry x z i (Nat.le_of_lt hi)).symm.trans
      (he.trans (insertLetter_cyclicEq_entry x z j (Nat.le_of_lt hj)))
    exact (entry_cyclicEq_iff_index_eq hx hz hi hj).mp hc
  · intro he
    subst j
    exact CyclicEq.refl (List.length_pos_iff.mp (by simp))

theorem insertLetter_range_pairwise_not_cyclicEq {x : List α} {z : α}
    (hx : x.Nodup) (hz : z ∉ x) {n : Nat} (hn : n ≤ x.length) :
    ((List.range n).map (insertLetter x z)).Pairwise (fun a b => ¬ CyclicEq a b) := by
  have hp : (List.range n).Pairwise (fun i j => i < j) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    simpa using hij
  apply List.pairwise_map.mpr
  apply List.Pairwise.imp_of_mem (p := hp)
  intro i j hi hj hij hc
  have hi' : i < x.length := Nat.lt_of_lt_of_le (List.mem_range.mp hi) hn
  have hj' : j < x.length := Nat.lt_of_lt_of_le (List.mem_range.mp hj) hn
  have he := (insertLetter_cyclicEq_iff_index_eq hx hz hi' hj').mp hc
  omega

theorem fullBases_pairwise_not_cyclicEq {x : List α} {z : α}
    (hx : x.Nodup) (hz : z ∉ x) :
    (fullBases x z).Pairwise (fun a b => ¬ CyclicEq a b) :=
  insertLetter_range_pairwise_not_cyclicEq hx hz (Nat.le_refl _)

theorem shortBases_pairwise_not_cyclicEq {x : List α} {z : α}
    (hx : x.Nodup) (hz : z ∉ x) (hn : 1 ≤ x.length) :
    (shortBases x z).Pairwise (fun a b => ¬ CyclicEq a b) := by
  apply List.pairwise_append.mpr
  refine ⟨insertLetter_range_pairwise_not_cyclicEq hx hz (Nat.sub_le _ _),
    by simp, ?_⟩
  intro a ha b hb hc
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
  have hblast : b = rot x (x.length - 1) ++ [z] := List.mem_singleton.mp hb
  subst b
  have hjlt : j < x.length - 1 := List.mem_range.mp hj
  have hjn : j < x.length := by omega
  have he := (insertLetter_cyclicEq_entry x z j (Nat.le_of_lt hjn)).symm.trans hc
  have hi := (entry_cyclicEq_iff_index_eq hx hz hjn (by omega)).mp he
  omega

theorem fullRows_pairwise_not_cyclicEq {r : Row α} {z : α}
    (hr : r.Valid) (hz : z ∉ r.base) :
    (fullRows r z).Pairwise (fun t u => ¬ CyclicEq t.base u.base) := by
  exact List.pairwise_map.mpr (fullBases_pairwise_not_cyclicEq hr.1 hz)

theorem shortRows_pairwise_not_cyclicEq {r : Row α} {z : α}
    (hr : r.Valid) (hz : z ∉ r.base) :
    (shortRows r z).Pairwise (fun t u => ¬ CyclicEq t.base u.base) := by
  exact List.pairwise_map.mpr (shortBases_pairwise_not_cyclicEq hr.1 hz
    (Nat.le_trans hr.2.2.1 hr.2.2.2))

/-- The local replacement has no duplicate cyclic base blocks, including the
exceptional literal orientation of the final short descendant.
-/
theorem rows_pairwise_not_cyclicEq {r : Row α} {z : α}
    (hr : r.Valid) (hz : z ∉ r.base) :
    (rows r z).Pairwise (fun t u => ¬ CyclicEq t.base u.base) := by
  unfold rows
  split
  · exact fullRows_pairwise_not_cyclicEq hr hz
  · exact shortRows_pairwise_not_cyclicEq hr hz

end SuperpermutationUpperBound.Transport
