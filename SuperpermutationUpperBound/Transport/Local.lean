import SuperpermutationUpperBound.Rows
import SuperpermutationUpperBound.Foundation.Rotation

/-! The literal local replacement used by transport.
All new ordinary letters are inserted into the old cyclic base; the final
short base is oriented to become the second row of the exceptional path. -/
namespace SuperpermutationUpperBound.Transport

variable {α : Type} {x : List α} {z s : α}

def insertLetter (x : List α) (z : α) (j : Nat) : List α :=
  x.take j ++ [z] ++ x.drop j

def fullBases (x : List α) (z : α) : List (List α) :=
  (List.range x.length).map (insertLetter x z)

def shortBases (x : List α) (z : α) : List (List α) :=
  (List.range (x.length - 1)).map (insertLetter x z) ++
    [rot x (x.length - 1) ++ [z]]

def fullRows (r : Row α) (z : α) : List (Row α) :=
  (fullBases r.base z).map (fun b => ⟨b, r.satellite, r.base.length + 1⟩)

def shortRows (r : Row α) (z : α) : List (Row α) :=
  (shortBases r.base z).map (fun b => ⟨b, r.satellite, r.base.length - 1⟩)

/-- The full/deficit-two transport chooses the indicated local replacement. -/
def rows (r : Row α) (z : α) : List (Row α) :=
  if r.visible = r.base.length then fullRows r z else shortRows r z

/-- Insertion preserves exactly the multiset of old letters plus the new one. -/
theorem insertLetter_perm (x : List α) (z : α) (j : Nat) :
    (insertLetter x z j).Perm (z :: x) := by
  unfold insertLetter
  have h := (List.perm_append_comm (l₁ := x.take j) (l₂ := [z])).append_right (x.drop j)
  simpa only [List.singleton_append, List.cons_append, List.nil_append,
    List.take_append_drop] using h

@[simp] theorem insertLetter_length (x : List α) (z : α) (j : Nat) :
    (insertLetter x z j).length = x.length + 1 := by
  simpa using (insertLetter_perm x z j).length_eq

@[simp] theorem mem_insertLetter {a : α} (x : List α) (z : α) (j : Nat) :
    a ∈ insertLetter x z j ↔ a = z ∨ a ∈ x := by
  simpa using (insertLetter_perm x z j).mem_iff (a := a)

theorem insertLetter_nodup (hx : x.Nodup) (hz : z ∉ x) (j : Nat) :
    (insertLetter x z j).Nodup :=
  (insertLetter_perm x z j).nodup_iff.mpr (List.nodup_cons.mpr ⟨hz, hx⟩)

theorem insertLetter_fresh (hs : s ∉ x) (hsz : s ≠ z) (j : Nat) :
    s ∉ insertLetter x z j := by
  simpa only [mem_insertLetter, not_or] using And.intro hsz hs

/-- Rotate an insertion just past the new letter to recover the literal cut. -/
theorem rot_insertLetter_at_cut (x : List α) (z : α) (j : Nat) :
    rot (insertLetter x z j) ((x.take j).length + 1) =
      x.drop j ++ x.take j ++ [z] := by
  have hlen : (x.take j ++ [z]).length = (x.take j).length + 1 := by simp
  rw [← hlen]
  change rot ((x.take j ++ [z]) ++ x.drop j) (x.take j ++ [z]).length = _
  rw [rot_eq_drop_append_take_of_le _ _ (by simp)]
  rw [List.drop_append_length, List.take_append_length, List.append_assoc]

/-- The exceptional final short base is the final-gap insertion, rotated by n. -/
theorem short_final_base_rotation (x : List α) (z : α) (hx : 1 ≤ x.length) :
    rot (insertLetter x z (x.length - 1)) x.length =
      rot x (x.length - 1) ++ [z] := by
  have hlen : (x.take (x.length - 1)).length + 1 = x.length := by
    simp only [List.length_take, Nat.min_eq_left (Nat.sub_le _ _)]
    omega
  have hcut := rot_insertLetter_at_cut x z (x.length - 1)
  rw [hlen] at hcut
  rw [hcut, rot_eq_drop_append_take_of_le x (x.length - 1) (Nat.sub_le _ _)]

theorem short_final_base_cyclicEq (x : List α) (z : α) (hx : 1 ≤ x.length) :
    CyclicEq (insertLetter x z (x.length - 1)) (rot x (x.length - 1) ++ [z]) := by
  refine ⟨⟨x.length, by simp⟩, ?_⟩
  exact short_final_base_rotation x z hx

@[simp] theorem fullBases_length (x : List α) (z : α) :
    (fullBases x z).length = x.length := by simp [fullBases]

@[simp] theorem shortBases_length (x : List α) (z : α) (hx : 1 ≤ x.length) :
    (shortBases x z).length = x.length := by
  simp only [shortBases, List.length_append, List.length_map, List.length_range,
    List.length_singleton]
  omega

theorem fullBases_perm {b : List α} (hb : b ∈ fullBases x z) : b.Perm (z :: x) := by
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hb
  exact insertLetter_perm x z j

theorem shortBases_perm {b : List α} (hb : b ∈ shortBases x z) : b.Perm (z :: x) := by
  rcases List.mem_append.mp hb with hi | he
  · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
    exact insertLetter_perm x z j
  · have heq : b = rot x (x.length - 1) ++ [z] := List.mem_singleton.mp he
    rw [heq]
    exact ((rot_perm x (x.length - 1)).append_right [z]).trans List.perm_append_comm

theorem fullBases_base_length {b : List α} (hb : b ∈ fullBases x z) :
    b.length = x.length + 1 := by simpa using (fullBases_perm hb).length_eq

theorem shortBases_base_length {b : List α} (hb : b ∈ shortBases x z) :
    b.length = x.length + 1 := by simpa using (shortBases_perm hb).length_eq

theorem fullBases_nodup (hx : x.Nodup) (hz : z ∉ x)
    {b : List α} (hb : b ∈ fullBases x z) : b.Nodup :=
  (fullBases_perm hb).nodup_iff.mpr (List.nodup_cons.mpr ⟨hz, hx⟩)

theorem shortBases_nodup (hx : x.Nodup) (hz : z ∉ x)
    {b : List α} (hb : b ∈ shortBases x z) : b.Nodup :=
  (shortBases_perm hb).nodup_iff.mpr (List.nodup_cons.mpr ⟨hz, hx⟩)

theorem fullBases_fresh (hs : s ∉ x) (hsz : s ≠ z)
    {b : List α} (hb : b ∈ fullBases x z) : s ∉ b := by
  rw [(fullBases_perm hb).mem_iff]
  simp only [List.mem_cons, not_or]
  exact ⟨hsz, hs⟩

theorem shortBases_fresh (hs : s ∉ x) (hsz : s ≠ z)
    {b : List α} (hb : b ∈ shortBases x z) : s ∉ b := by
  rw [(shortBases_perm hb).mem_iff]
  simp only [List.mem_cons, not_or]
  exact ⟨hsz, hs⟩

@[simp] theorem fullRows_length (r : Row α) (z : α) :
    (fullRows r z).length = r.base.length := by simp [fullRows]

@[simp] theorem shortRows_length (r : Row α) (z : α) (hn : 1 ≤ r.base.length) :
    (shortRows r z).length = r.base.length := by simp [shortRows, shortBases_length _ _ hn]

theorem fullRows_base_length {r t : Row α} (ht : t ∈ fullRows r z) :
    t.base.length = r.base.length + 1 := by
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
  exact fullBases_base_length hb

theorem shortRows_base_length {r t : Row α} (ht : t ∈ shortRows r z) :
    t.base.length = r.base.length + 1 := by
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
  exact shortBases_base_length hb

theorem fullRows_valid {r t : Row α} (hr : r.Valid)
    (hz : z ∉ r.base) (hzs : z ≠ r.satellite) (ht : t ∈ fullRows r z) : t.Valid := by
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
  refine ⟨fullBases_nodup hr.1 hz hb, fullBases_fresh hr.2.1 (Ne.symm hzs) hb, ?_, ?_⟩
  · simp
  · exact Nat.le_of_eq (fullBases_base_length hb).symm

theorem shortRows_valid {r t : Row α} (hr : r.Valid) (hn : 3 ≤ r.base.length)
    (hz : z ∉ r.base) (hzs : z ≠ r.satellite) (ht : t ∈ shortRows r z) : t.Valid := by
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
  refine ⟨shortBases_nodup hr.1 hz hb, shortBases_fresh hr.2.1 (Ne.symm hzs) hb, ?_, ?_⟩
  · dsimp
    omega
  · dsimp
    rw [shortBases_base_length hb]
    omega

theorem fullRows_charge {r t : Row α} (ht : t ∈ fullRows r z) : t.charge = 0 := by
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
  simp only [Row.charge, fullBases_base_length hb, Nat.sub_self]

theorem shortRows_charge {r t : Row α} (hn : 1 ≤ r.base.length)
    (ht : t ∈ shortRows r z) : t.charge = 2 := by
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
  dsimp [Row.charge]
  rw [shortBases_base_length hb]
  omega

private theorem sum_map_constant (xs : List α) (f : α → Nat) (c : Nat)
    (h : ∀ x ∈ xs, f x = c) : (xs.map f).sum = xs.length * c := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [h x (by simp), ih (by intro a ha; exact h a (by simp [ha]))]
    rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

theorem fullRows_charge_sum (r : Row α) (z : α) :
    ((fullRows r z).map Row.charge).sum = 0 := by
  have h := sum_map_constant (fullRows r z) Row.charge 0
    (fun _ ht => fullRows_charge ht)
  simpa using h

theorem shortRows_charge_sum (r : Row α) (z : α) (hn : 1 ≤ r.base.length) :
    ((shortRows r z).map Row.charge).sum = r.base.length * 2 := by
  have h := sum_map_constant (shortRows r z) Row.charge 2
    (fun _ ht => shortRows_charge hn ht)
  simpa [shortRows_length r z hn] using h

theorem fullRows_preserves_charge (r : Row α) (z : α) (hr : r.visible = r.base.length) :
    ((fullRows r z).map Row.charge).sum = r.base.length * r.charge := by
  simp [fullRows_charge_sum, Row.charge, hr]

theorem shortRows_preserves_charge (r : Row α) (z : α) (hn : 2 ≤ r.base.length)
    (hr : r.visible = r.base.length - 2) :
    ((shortRows r z).map Row.charge).sum = r.base.length * r.charge := by
  rw [shortRows_charge_sum r z (by omega)]
  have hc : r.charge = 2 := by dsimp [Row.charge]; omega
  rw [hc]

/-- Every valid full/short row has exactly n descendants of the same charge. -/
theorem rows_local_certificate {r : Row α} (hr : r.Valid)
    (hz : z ∉ r.base) (hzs : z ≠ r.satellite)
    (hkind : r.visible = r.base.length ∨ r.visible = r.base.length - 2) :
    (rows r z).length = r.base.length ∧
    (∀ t ∈ rows r z, t.Valid ∧ t.base.length = r.base.length + 1 ∧ t.charge = r.charge) ∧
    ((rows r z).map Row.charge).sum = r.base.length * r.charge := by
  by_cases hf : r.visible = r.base.length
  · simp only [rows, if_pos hf]
    refine ⟨fullRows_length r z, ?_, fullRows_preserves_charge r z hf⟩
    intro t ht
    refine ⟨fullRows_valid hr hz hzs ht, fullRows_base_length ht, ?_⟩
    simpa [Row.charge, hf] using fullRows_charge ht
  · have hs : r.visible = r.base.length - 2 := hkind.resolve_left hf
    have hn : 3 ≤ r.base.length := by have := hr.2.2.1; omega
    have hc : r.charge = 2 := by dsimp [Row.charge]; omega
    simp only [rows, if_neg hf]
    refine ⟨shortRows_length r z (by omega), ?_, shortRows_preserves_charge r z (by omega) hs⟩
    intro t ht
    exact ⟨shortRows_valid hr hn hz hzs ht, shortRows_base_length ht,
      (shortRows_charge (by omega) ht).trans hc.symm⟩

#print axioms insertLetter_perm
#print axioms short_final_base_rotation
#print axioms short_final_base_cyclicEq
#print axioms fullRows_valid
#print axioms shortRows_valid
#print axioms fullRows_preserves_charge
#print axioms shortRows_preserves_charge
#print axioms rows_local_certificate

end SuperpermutationUpperBound.Transport
