import SuperpermutationUpperBound.Foundation.Rotation
import SuperpermutationUpperBound.Foundation.WordSupport

namespace SuperpermutationUpperBound
variable {α : Type}

/-- Delete one edge of the rotation circle. The remaining ordinary path starts
at rotation j+1 and ends at rotation j, visiting every rotation vertex. -/
def rotationCutWord (x : List α) (j : Nat) : List α :=
  rot x (j + 1) ++ (rot x (j + 1)).take (x.length - 1)

theorem rotationCutWord_length (x : List α) (j : Nat) :
    (rotationCutWord x j).length = 2 * x.length - 1 := by
  simp [rotationCutWord, Nat.min_eq_left (Nat.sub_le _ _)]
  omega

theorem rotationCutWord_prefix (x : List α) (j : Nat) :
    (rotationCutWord x j).take x.length = rot x (j + 1) := by
  have h := List.take_append_length (l₁ := rot x (j + 1))
    (l₂ := (rot x (j + 1)).take (x.length - 1))
  simpa only [rot_length, rotationCutWord] using h

theorem rotationCutWord_suffix (x : List α) (j : Nat) (hx : 0 < x.length) :
    (rotationCutWord x j).drop ((rotationCutWord x j).length - x.length) = rot x j := by
  rw [rotationCutWord_length, show 2 * x.length - 1 - x.length = x.length - 1 by omega]
  unfold rotationCutWord
  rw [List.drop_append]
  simp only [rot_length]
  have hz : x.length - 1 - x.length = 0 := by omega
  simp only [hz, List.drop_zero]
  rw [← rot_eq_drop_append_take_of_le (rot x (j + 1)) (x.length - 1) (by simp)]
  rw [rot_add]
  rw [show j + 1 + (x.length - 1) = j + x.length by omega, rot_add_length]

theorem rotationCutWord_support (x : List α) (j : Nat) :
    ∀ a ∈ rotationCutWord x j, a ∈ x := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact (rot_perm x (j + 1)).mem_iff.mp ha
  · exact (rot_perm x (j + 1)).mem_iff.mp (List.mem_of_mem_take ha)

/-- Sampling all cyclic windows is invariant, with multiplicity, under a
uniform shift of the sampled rotation indices. -/
theorem rotation_windows_shift (x : List α) (d ell : Nat) :
    ((List.range x.length).map (fun j => (rot x (j + d)).take ell)).Perm
      ((List.range x.length).map (fun j => (rot x j).take ell)) := by
  have he : (List.range x.length).map (fun j => (rot x (j + d)).take ell) =
      rot ((List.range x.length).map (fun j => (rot x j).take ell)) d := by
    apply List.ext_getElem (by simp)
    intro i hi hi'
    rw [getElem_rot]
    simp only [List.getElem_map, List.getElem_range, List.length_map, List.length_range]
    rw [rot_mod]
    simp only [Nat.add_comm i d]
  rw [he]
  exact rot_perm _ d

/-- All rotations occur as literal endpoint-sized windows of every cut word. -/
theorem rotationCutWord_covers_rotations (x : List α) (j i : Nat) (hi : i < x.length) :
    (rot x i).IsInfix (rotationCutWord x j) := by
  have hh : 0 < x.length := by omega
  let d := ((x.length - (j + 1) % x.length) + i) % x.length
  have hd : d < (rot x (j + 1)).length := by dsimp [d]; simpa using Nat.mod_lt _ hh
  have hc := rot_isInfix_cycleWord (rot x (j + 1)) d hd
  have he : rot (rot x (j + 1)) d = rot x i := by
    dsimp [d]
    rw [show x.length = (rot x (j + 1)).length from (rot_length _ _).symm,
      rot_mod]
    simp only [rot_length]
    rw [← rot_add, rot_inverse]
  rw [he] at hc
  simpa only [rot_length, rotationCutWord] using hc

theorem rotationCutWord_prefix_short (x : List α) (j ell : Nat) (hell : ell ≤ x.length) :
    (rotationCutWord x j).take ell = (rot x (j + 1)).take ell := by
  have he : ((rotationCutWord x j).take x.length).take ell =
      (rotationCutWord x j).take ell := by simp [List.take_take, Nat.min_eq_left hell]
  rw [← he, rotationCutWord_prefix]

theorem rotationCutWord_suffix_short (x : List α) (j ell : Nat)
    (hx : 0 < x.length) (hell : ell ≤ x.length) :
    (rotationCutWord x j).drop ((rotationCutWord x j).length - ell) =
      (rot x (j + (x.length - ell))).take ell := by
  have hl := rotationCutWord_length x j
  have he : (rotationCutWord x j).drop ((rotationCutWord x j).length - ell) =
      ((rotationCutWord x j).drop ((rotationCutWord x j).length - x.length)).drop
        (x.length - ell) := by
    rw [List.drop_drop]
    congr 1
    omega
  rw [he, rotationCutWord_suffix x j hx]
  have ht := take_rot_eq_drop (rot x j) (x.length - ell) (by simp)
  simp only [rot_length, Nat.sub_sub_self hell, rot_add] at ht
  exact ht.symm

/-- Uniform cuts have identical prefix and suffix distributions at every
permitted overlap length, as a permutation of lists with multiplicity. -/
theorem rotationCutWord_balanced (x : List α) (ell : Nat)
    (hx : 0 < x.length) (hell : ell ≤ x.length) :
    ((List.range x.length).map (fun j => (rotationCutWord x j).take ell)).Perm
      ((List.range x.length).map (fun j =>
        (rotationCutWord x j).drop ((rotationCutWord x j).length - ell))) := by
  simp only [rotationCutWord_prefix_short x _ ell hell,
    rotationCutWord_suffix_short x _ ell hx hell]
  exact (rotation_windows_shift x 1 ell).trans (rotation_windows_shift x (x.length - ell) ell).symm

end SuperpermutationUpperBound
