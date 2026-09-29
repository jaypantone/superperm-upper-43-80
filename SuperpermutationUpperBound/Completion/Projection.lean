import SuperpermutationUpperBound.Packing
import SuperpermutationUpperBound.Transport.Blocks
import SuperpermutationUpperBound.Transport.Ports

/-! Literal insertion identities for completion coverage. The rotation index
increases by one exactly when the insertion passes the original cyclic cut. -/

namespace SuperpermutationUpperBound.Completion

open Transport

variable {α : Type}

theorem insertLetter_after_prefix (a b : List α) (z : α) (j : Nat) :
    insertLetter (a ++ b) z (a.length + j) = a ++ insertLetter b z j := by
  simp only [insertLetter, List.take_length_add_append,
    List.drop_length_add_append, List.append_assoc]

theorem insertLetter_rot_cut_left (a b : List α) (z : α) (j : Nat)
    (hj : j ≤ b.length) :
    insertLetter (b ++ a) z j = rot (insertLetter (a ++ b) z (a.length + j)) a.length := by
  rw [insertLetter_append_of_le b a z j hj, insertLetter_after_prefix, rot_append_length]

theorem insertLetter_rot_cut_right (a b : List α) (z : α) (j : Nat)
    (hj : j ≤ a.length) :
    insertLetter (b ++ a) z (b.length + j) =
      rot (insertLetter (a ++ b) z j) (a.length + 1) := by
  rw [insertLetter_after_prefix, insertLetter_append_of_le a b z j hj]
  have he : a.length + 1 = (insertLetter a z j).length := (insertLetter_length a z j).symm
  rw [he, rot_append_length]

/-- Every insertion into a visible old rotation occurs as a visible rotation
of the prescribed lifted base. This is a literal identity, not a count.
-/
theorem visible_lift_rotation (x : List α) (z : α) {L j b : Nat}
    (hL : L ≤ x.length) (hj : j < L) (hb : b ≤ x.length) :
    ∃ i, i < x.length ∧ ∃ k, k < L + (if i < L then 1 else 0) ∧
      rot (insertLetter x z i) k = insertLetter (rot x j) z b := by
  have hjn : j ≤ x.length := Nat.le_trans (Nat.le_of_lt hj) hL
  have ha : (x.take j).length = j := List.length_take_of_le hjn
  have hd : (x.drop j).length = x.length - j := List.length_drop ..
  have hr := rot_eq_drop_append_take_of_le x j hjn
  by_cases hwrap : j + b < x.length
  · have hbb : b ≤ (x.drop j).length := by omega
    have he := insertLetter_rot_cut_left (x.take j) (x.drop j) z b hbb
    have he' : insertLetter (rot x j) z b = rot (insertLetter x z (j + b)) j := by
      simpa only [List.take_append_drop, ha, ← hr] using he
    exact ⟨j + b, hwrap, j, by split <;> omega, he'.symm⟩
  · let c := b - (x.drop j).length
    have hc : c ≤ (x.take j).length := by dsimp [c]; omega
    have hcj : c ≤ j := by omega
    have hsum : (x.drop j).length + c = b := by dsimp [c]; omega
    have he := insertLetter_rot_cut_right (x.take j) (x.drop j) z c hc
    have he' : insertLetter (rot x j) z b = rot (insertLetter x z c) (j + 1) := by
      simpa only [List.take_append_drop, ha, hsum, ← hr] using he
    have hci : c < L := by omega
    exact ⟨c, by omega, j + 1, by simp only [if_pos hci]; omega, he'.symm⟩

@[simp] theorem eraseSatellite_append_of_ne [DecidableEq α]
    (x : List α) {s z : α} (hsz : s ≠ z) :
    eraseSatellite z (x ++ [s]) = eraseSatellite z x ++ [s] := by
  simp [eraseSatellite, hsz]

theorem not_mem_eraseSatellite [DecidableEq α] {x : List α} {s z : α}
    (hs : s ∉ x) : s ∉ eraseSatellite z x := by
  intro hm
  exact hs (List.mem_filter.mp hm).1

/-- A duplicate-free word containing z is literally obtained by inserting z
at one of the linear gaps of its deletion.
-/
theorem eq_insertLetter_eraseSatellite [DecidableEq α] {x : List α} {z : α}
    (hx : x.Nodup) (hz : z ∈ x) :
    ∃ b, b ≤ (eraseSatellite z x).length ∧
      x = insertLetter (eraseSatellite z x) z b := by
  obtain ⟨a, b, rfl, hza⟩ := List.eq_append_cons_of_mem hz
  have hzb : z ∉ b := (List.nodup_cons.mp (List.nodup_append.mp hx).2.1).1
  have he : eraseSatellite z (a ++ z :: b) = a ++ b := by
    simp only [eraseSatellite, List.filter_append, List.filter_cons,
      ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
    change eraseSatellite z a ++ eraseSatellite z b = a ++ b
    rw [eraseSatellite_eq_self hza, eraseSatellite_eq_self hzb]
  refine ⟨a.length, by rw [he, List.length_append]; omega, ?_⟩
  rw [he]
  simp only [insertLetter, List.take_append_length, List.drop_append_length,
    List.append_assoc, List.singleton_append]

/-- Rotate a word to place its unique satellite last. -/
theorem exists_satellite_last [DecidableEq α] {p : List α} {s : α}
    (hp : p.Nodup) (hs : s ∈ p) :
    ∃ y : List α, s ∉ y ∧ CyclicEq (y ++ [s]) p := by
  obtain ⟨a, b, rfl, hsa⟩ := List.eq_append_cons_of_mem hs
  have hsb : s ∉ b := (List.nodup_cons.mp (List.nodup_append.mp hp).2.1).1
  refine ⟨b ++ a, by simp [List.mem_append, hsa, hsb], ?_⟩
  have hn : (a ++ [s]) ++ b ≠ [] := by simp
  have hc := CyclicEq.of_rot hn (a ++ [s]).length
  rw [rot_append_length] at hc
  simpa only [List.append_assoc, List.singleton_append] using hc.symm

/-- A deleted old class ending in s determines a literal insertion into its
ordinary part, after rotating the new word to end in the same satellite.
-/
theorem extension_normal_form [DecidableEq α] {x p : List α} {s z : α}
    (hp : p.Nodup) (hs : s ∈ p) (hz : z ∈ p) (hsx : s ∉ x) (hzs : z ≠ s)
    (hold : CyclicEq (x ++ [s]) (eraseSatellite z p)) :
    ∃ b, b ≤ x.length ∧ CyclicEq (insertLetter x z b ++ [s]) p := by
  obtain ⟨y, hsy, hy⟩ := exists_satellite_last hp hs
  have hyp : (y ++ [s]).Nodup := hy.perm.nodup_iff.mpr hp
  have hyn : y.Nodup := (List.nodup_append.mp hyp).1
  have hzy : z ∈ y := by
    have hm : z ∈ y ++ [s] := hy.perm.mem_iff.mpr hz
    simpa only [List.mem_append, List.mem_singleton, hzs, or_false] using hm
  have he_nonempty : eraseSatellite z (y ++ [s]) ≠ [] := by
    rw [eraseSatellite_append_of_ne y (Ne.symm hzs)]
    simp
  have hdel : CyclicEq (eraseSatellite z y ++ [s]) (eraseSatellite z p) := by
    simpa only [eraseSatellite_append_of_ne y (Ne.symm hzs)] using
      hy.eraseSatellite z he_nonempty
  have hxy : x = eraseSatellite z y :=
    append_satellite_eq_of_cyclicEq hsx (hold.trans hdel.symm)
  obtain ⟨b, hb, hby⟩ := eq_insertLetter_eraseSatellite hyn hzy
  rw [← hxy] at hb hby
  refine ⟨b, hb, ?_⟩
  exact Eq.mp (congrArg (fun w => CyclicEq (w ++ [s]) p) hby) hy

end SuperpermutationUpperBound.Completion
