import SuperpermutationUpperBound.Foundation.Words

/-! Literal cyclic rotation, including the modular index law. -/

namespace SuperpermutationUpperBound

variable {α : Type u}

/-- The left rotation moves the first `j % x.length` letters to the end. -/
abbrev rot (x : List α) (j : Nat) : List α := x.rotateLeft j

theorem rot_eq_drop_append_take (x : List α) (j : Nat) :
    rot x j = x.drop (j % x.length) ++ x.take (j % x.length) := by
  unfold rot List.rotateLeft
  dsimp only
  split
  · rename_i h
    cases x with
    | nil => simp
    | cons a xs =>
      have hx : xs = [] := List.length_eq_zero_iff.mp (by simpa using h)
      subst xs
      simp [Nat.mod_one]
  · rfl

@[simp] theorem rot_length (x : List α) (j : Nat) : (rot x j).length = x.length := by
  rw [rot_eq_drop_append_take]
  simp
  omega

@[simp] theorem rot_zero (x : List α) : rot x 0 = x := List.rotateLeft_zero

@[simp] theorem rot_mod (x : List α) (j : Nat) : rot x (j % x.length) = rot x j := by
  simp only [rot_eq_drop_append_take, Nat.mod_mod]

@[simp] theorem rot_length_self (x : List α) : rot x x.length = x := by
  simp [rot_eq_drop_append_take]

theorem rot_perm (x : List α) (j : Nat) : (rot x j).Perm x := by
  rw [rot_eq_drop_append_take]
  exact List.perm_append_comm.trans (by rw [List.take_append_drop])

@[simp] theorem rot_nodup_iff (x : List α) (j : Nat) : (rot x j).Nodup ↔ x.Nodup :=
  (rot_perm x j).nodup_iff

theorem rot_nodup {x : List α} (hx : x.Nodup) (j : Nat) : (rot x j).Nodup :=
  (rot_nodup_iff x j).mpr hx

@[simp] theorem isPermutation_rot_iff {n : Nat} (x : Word n) (j : Nat) :
    IsPermutation (rot x j) ↔ IsPermutation x := by
  simp [IsPermutation]

theorem isPermutation_rot {n : Nat} {x : Word n} (hx : IsPermutation x) (j : Nat) :
    IsPermutation (rot x j) := (isPermutation_rot_iff x j).mpr hx

/-- Rotation is addition modulo the list length on positions. -/
theorem getElem_rot (x : List α) (j k : Nat) (hk : k < (rot x j).length) :
    (rot x j)[k] = x[(j + k) % x.length]'(Nat.mod_lt _ (by
      have := rot_length x j
      omega)) := by
  have hk' : k < x.length := by simpa using hk
  have hpos : 0 < x.length := by omega
  have hj : j % x.length < x.length := Nat.mod_lt _ hpos
  simp only [rot_eq_drop_append_take] at hk ⊢
  rw [List.getElem_append]
  split
  · rename_i h
    simp only [List.length_drop] at h
    rw [List.getElem_drop]
    have hsum : j % x.length + k < x.length := by omega
    have heq : (j + k) % x.length = j % x.length + k := by
      rw [← Nat.mod_add_mod, Nat.mod_eq_of_lt hsum]
    simp only [heq]
  · rename_i h
    simp only [List.length_drop] at h
    rw [List.getElem_take]
    have heq : (j + k) % x.length = k - (x.length - j % x.length) := by
      rw [← Nat.mod_add_mod]
      have hadd : j % x.length + k =
          (k - (x.length - j % x.length)) + x.length := by omega
      rw [hadd, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    simp only [List.length_drop, heq]

/-- Iterated literal rotations compose by addition of their distances. -/
theorem rot_add (x : List α) (i j : Nat) : rot (rot x i) j = rot x (i + j) := by
  apply List.ext_getElem (by simp)
  intro k hk₁ hk₂
  rw [getElem_rot, getElem_rot, getElem_rot]
  simp only [rot_length, Nat.add_mod_mod, Nat.add_assoc]

theorem rot_add_one (x : List α) (j : Nat) : rot x (j + 1) = rot (rot x j) 1 :=
  (rot_add x j 1).symm

theorem rot_add_two (x : List α) (j : Nat) : rot x (j + 2) = rot (rot x j) 2 :=
  (rot_add x j 2).symm

@[simp] theorem rot_add_length (x : List α) (j : Nat) :
    rot x (j + x.length) = rot x j := by
  simp only [rot_eq_drop_append_take, Nat.add_mod_right]

/-- Undo any rotation by its complementary distance in a full period. -/
@[simp] theorem rot_inverse (x : List α) (j : Nat) :
    rot (rot x j) (x.length - j % x.length) = x := by
  rw [rot_add]
  cases x with
  | nil => rfl
  | cons a xs =>
    have hj : j % (a :: xs).length ≤ (a :: xs).length :=
      Nat.le_of_lt (Nat.mod_lt _ (by simp))
    calc
      rot (a :: xs) (j + ((a :: xs).length - j % (a :: xs).length)) =
          rot (a :: xs) (j % (a :: xs).length +
            ((a :: xs).length - j % (a :: xs).length)) := by
        simp only [rot_eq_drop_append_take, Nat.mod_add_mod]
      _ = a :: xs := by rw [Nat.add_sub_of_le hj, rot_length_self]

/-- On distances up to one period, rotation is the literal cut-and-append. -/
theorem rot_eq_drop_append_take_of_le (x : List α) (j : Nat) (hj : j ≤ x.length) :
    rot x j = x.drop j ++ x.take j := by
  rcases Nat.lt_or_eq_of_le hj with hlt | rfl
  · simp [rot_eq_drop_append_take, Nat.mod_eq_of_lt hlt]
  · simp

theorem take_rot_eq_drop (x : List α) (j : Nat) (hj : j ≤ x.length) :
    (rot x j).take (x.length - j) = x.drop j := by
  rw [rot_eq_drop_append_take_of_le x j hj]
  have hlen : x.length - j = (x.drop j).length := (List.length_drop ..).symm
  rw [hlen, List.take_append_length]

theorem take_rot_two (x : List α) (hx : 2 ≤ x.length) :
    (rot x 2).take (x.length - 2) = x.drop 2 := take_rot_eq_drop x 2 hx

theorem append_take_eq_take_append_rot (x : List α) (j : Nat) (hj : j ≤ x.length) :
    x ++ x.take j = x.take j ++ rot x j := by
  rw [rot_eq_drop_append_take_of_le x j hj, ← List.append_assoc, List.take_append_drop]

theorem append_take_one_eq_take_one_append_rot (x : List α) :
    x ++ x.take 1 = x.take 1 ++ rot x 1 := by
  cases x with
  | nil => rfl
  | cons a xs => exact append_take_eq_take_append_rot _ 1 (by simp)

/-- A list followed by all but its last letter contains every cyclic rotation. -/
theorem rot_isInfix_cycleWord (x : List α) (j : Nat) (hj : j < x.length) :
    (rot x j).IsInfix (x ++ x.take (x.length - 1)) := by
  have hj' : j ≤ x.length - 1 := by omega
  have hsplit : x.take j ++ (x.take (x.length - 1)).drop j =
      x.take (x.length - 1) := by
    have ht : (x.take (x.length - 1)).take j = x.take j := by
      rw [List.take_take, Nat.min_eq_left hj']
    rw [← ht, List.take_append_drop]
  refine ⟨x.take j, (x.take (x.length - 1)).drop j, ?_⟩
  rw [rot_eq_drop_append_take_of_le x j (Nat.le_of_lt hj)]
  simp only [← List.append_assoc, List.take_append_drop]
  rw [List.append_assoc, hsplit]

end SuperpermutationUpperBound
