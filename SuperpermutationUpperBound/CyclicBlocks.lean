import SuperpermutationUpperBound.Rows
import SuperpermutationUpperBound.Foundation.Rotation

/-!
Semantic cyclic equivalence and the satellite-deletion interface. All
equivalence claims concern nonempty literal words. A direct insertion at a
fixed final position does not preserve cyclic equivalence of the base; the
full insertion block must allow every rotated base.
-/

namespace SuperpermutationUpperBound

variable {α : Type u}

namespace CyclicEq

theorem refl {x : List α} (hx : x ≠ []) : CyclicEq x x := by
  have hp : 0 < x.length := List.length_pos_iff.mpr hx
  exact ⟨⟨0, hp⟩, rot_zero x⟩

theorem length_eq {x y : List α} (h : CyclicEq x y) : x.length = y.length := by
  obtain ⟨j, rfl⟩ := h
  exact (rot_length x j).symm

theorem nonempty_left {x y : List α} (h : CyclicEq x y) : x ≠ [] := by
  obtain ⟨j, _⟩ := h
  exact List.length_pos_iff.mp (Nat.zero_lt_of_lt j.isLt)

theorem nonempty_right {x y : List α} (h : CyclicEq x y) : y ≠ [] := by
  apply List.length_pos_iff.mp
  rw [← h.length_eq]
  exact List.length_pos_iff.mpr h.nonempty_left

theorem perm {x y : List α} (h : CyclicEq x y) : x.Perm y := by
  obtain ⟨j, rfl⟩ := h
  exact (rot_perm x j).symm

theorem nodup_iff {x y : List α} (h : CyclicEq x y) : x.Nodup ↔ y.Nodup :=
  h.perm.nodup_iff

theorem of_rot {x : List α} (hx : x ≠ []) (j : Nat) : CyclicEq x (rot x j) := by
  refine ⟨⟨j % x.length, Nat.mod_lt _ (List.length_pos_iff.mpr hx)⟩, ?_⟩
  exact rot_mod x j

theorem symm {x y : List α} (h : CyclicEq x y) : CyclicEq y x := by
  obtain ⟨j, rfl⟩ := h
  have hx : x ≠ [] := List.length_pos_iff.mp (Nat.zero_lt_of_lt j.isLt)
  have hy : rot x j ≠ [] := by
    apply List.length_pos_iff.mp
    simpa using List.length_pos_iff.mpr hx
  have hi := of_rot hy (x.length - j.val % x.length)
  simpa only [rot_inverse] using hi

theorem trans {x y z : List α} (hxy : CyclicEq x y) (hyz : CyclicEq y z) :
    CyclicEq x z := by
  have hx := hxy.nonempty_left
  obtain ⟨i, rfl⟩ := hxy
  obtain ⟨j, rfl⟩ := hyz
  refine ⟨⟨(i.val + j.val) % x.length,
    Nat.mod_lt _ (List.length_pos_iff.mpr hx)⟩, ?_⟩
  exact (rot_mod x (i.val + j.val)).trans (rot_add x i.val j.val).symm

/-- Changing the base representative only reindexes its literal rotations. -/
theorem rot_reindex {x y : List α} (h : CyclicEq x y) (j : Nat) :
    ∃ i : Fin x.length, rot y j = rot x i.val := by
  have hx := h.nonempty_left
  obtain ⟨k, rfl⟩ := h
  refine ⟨⟨(k.val + j) % x.length,
    Nat.mod_lt _ (List.length_pos_iff.mpr hx)⟩, ?_⟩
  exact (rot_add x k.val j).trans (rot_mod x (k.val + j)).symm

theorem insertion_reindex {x y : List α} (h : CyclicEq x y) (s : α) (j : Nat) :
    ∃ i : Fin x.length, rot y j ++ [s] = rot x i.val ++ [s] := by
  obtain ⟨i, hi⟩ := h.rot_reindex j
  exact ⟨i, congrArg (fun z => z ++ [s]) hi⟩

theorem isPermutation_iff {n : Nat} {x y : Word n} (h : CyclicEq x y) :
    IsPermutation x ↔ IsPermutation y := by
  unfold IsPermutation
  rw [h.length_eq, h.nodup_iff]

end CyclicEq

/-- Rotation at a literal concatenation boundary interchanges the two pieces. -/
theorem rot_append_length (a b : List α) :
    rot (a ++ b) a.length = b ++ a := by
  rw [rot_eq_drop_append_take_of_le _ _ (by simp)]
  rw [List.drop_append_length, List.take_append_length]

/-- Filtering a rotation is exactly a rotation of the filtered word. The new
distance counts the retained letters before the original cut.
-/
theorem filter_rot (p : α → Bool) (x : List α) (j : Nat) :
    (rot x j).filter p =
      rot (x.filter p) ((x.take (j % x.length)).filter p).length := by
  have hsplit := congrArg (List.filter p) (List.take_append_drop (j % x.length) x)
  rw [List.filter_append] at hsplit
  calc
    (rot x j).filter p =
        (x.drop (j % x.length)).filter p ++ (x.take (j % x.length)).filter p := by
      rw [rot_eq_drop_append_take, List.filter_append]
    _ = rot ((x.take (j % x.length)).filter p ++
        (x.drop (j % x.length)).filter p)
        ((x.take (j % x.length)).filter p).length := (rot_append_length _ _).symm
    _ = rot (x.filter p) ((x.take (j % x.length)).filter p).length := by rw [hsplit]

theorem CyclicEq.filter {x y : List α} (h : CyclicEq x y) (p : α → Bool)
    (hx : x.filter p ≠ []) : CyclicEq (x.filter p) (y.filter p) := by
  obtain ⟨j, rfl⟩ := h
  rw [filter_rot]
  exact CyclicEq.of_rot hx _

/-- Delete every occurrence of a specified satellite from a literal word. -/
def eraseSatellite [DecidableEq α] (s : α) (x : List α) : List α :=
  x.filter (fun a => decide (a ≠ s))

theorem eraseSatellite_rot [DecidableEq α] (s : α) (x : List α) (j : Nat) :
    eraseSatellite s (rot x j) =
      rot (eraseSatellite s x) (eraseSatellite s (x.take (j % x.length))).length :=
  filter_rot _ x j

theorem cyclicEq_eraseSatellite_rot [DecidableEq α] (s : α) (x : List α)
    (j : Nat) (hx : eraseSatellite s x ≠ []) :
    CyclicEq (eraseSatellite s x) (eraseSatellite s (rot x j)) := by
  rw [eraseSatellite_rot]
  exact CyclicEq.of_rot hx _

theorem CyclicEq.eraseSatellite [DecidableEq α] {x y : List α}
    (h : CyclicEq x y) (s : α) (hx : eraseSatellite s x ≠ []) :
    CyclicEq (eraseSatellite s x) (eraseSatellite s y) :=
  h.filter _ hx

@[simp] theorem eraseSatellite_eq_self [DecidableEq α] {s : α} {x : List α}
    (hs : s ∉ x) : eraseSatellite s x = x := by
  apply List.filter_eq_self.mpr
  intro a ha
  have hn : a ≠ s := by
    intro he
    subst a
    exact hs ha
  simp [hn]

@[simp] theorem eraseSatellite_append_satellite [DecidableEq α] (s : α) (x : List α) :
    eraseSatellite s (x ++ [s]) = eraseSatellite s x := by
  simp [eraseSatellite]

/-- Equal satellite-containing cyclic classes determine equal cyclic base
blocks after deleting the satellite. No uniqueness-of-occurrence assumption
is hidden: satellite absence from both base lists is explicit.
-/
theorem cyclicEq_base_of_append_satellite [DecidableEq α] {s : α} {x y : List α}
    (h : CyclicEq (x ++ [s]) (y ++ [s])) (hsx : s ∉ x) (hsy : s ∉ y)
    (hx : x ≠ []) : CyclicEq x y := by
  have he : eraseSatellite s (x ++ [s]) ≠ [] := by simpa [hsx] using hx
  have hd := h.eraseSatellite s he
  simpa [hsx, hsy] using hd

/-- The family of inserted cyclic classes depends only on the cyclic base
block. Quantifying all insertion positions is essential in both directions.
-/
theorem cyclicEq_insertion_exists_iff {x y p : List α} (h : CyclicEq x y) (s : α) :
    (∃ i : Fin x.length, CyclicEq (rot x i.val ++ [s]) p) ↔
      (∃ j : Fin y.length, CyclicEq (rot y j.val ++ [s]) p) := by
  constructor
  · intro ⟨i, hi⟩
    obtain ⟨j, hj⟩ := h.symm.insertion_reindex s i.val
    exact ⟨j, Eq.mp (congrArg (fun z => CyclicEq z p) hj) hi⟩
  · intro ⟨j, hj⟩
    obtain ⟨i, hi⟩ := h.insertion_reindex s j.val
    exact ⟨i, Eq.mp (congrArg (fun z => CyclicEq z p) hi) hj⟩

end SuperpermutationUpperBound
