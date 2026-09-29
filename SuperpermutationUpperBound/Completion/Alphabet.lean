import SuperpermutationUpperBound.Completion.PartitionCoverage
import SuperpermutationUpperBound.Foundation.WordSupport

/-! The completed rows use exactly the enlarged alphabet, even though repair
rows have a different satellite. For the original family this alphabet is a
permutation of range (k+9), providing the finite-word support bridge. -/
namespace SuperpermutationUpperBound.Completion

variable {α : Type}

theorem completeRows_alphabet_perm {r t : Row α} {z : α}
    (ht : t ∈ completeRows r z) :
    (t.base ++ [t.satellite]).Perm (z :: (r.base ++ [r.satellite])) := by
  rcases List.mem_append.mp ht with ht | ht
  · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht
    exact (Transport.insertLetter_perm r.base z j).append_right [r.satellite]
  · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht
    change ((rot r.base j ++ [r.satellite]) ++ [z]).Perm _
    exact (List.perm_append_comm (l₁ := rot r.base j ++ [r.satellite]) (l₂ := [z])).trans
      (((rot_perm r.base j).append_right [r.satellite]).cons z)

theorem packingRows_alphabet_perm {alphabet : List α} {s z : α} {rs : List (Row α)}
    (hb : BasedOn alphabet s rs) {t : Row α} (ht : t ∈ packingRows rs z) :
    (t.base ++ [t.satellite]).Perm (z :: (alphabet ++ [s])) := by
  obtain ⟨r, hr, ht⟩ := List.mem_flatMap.mp ht
  have hbr := hb r hr
  have hp := completeRows_alphabet_perm ht
  rw [hbr.2.2.1] at hp
  exact hp.trans ((hbr.2.1.append_right [s]).cons z)

theorem packingRows_word_mem {alphabet : List α} {s z : α} {rs : List (Row α)}
    (hb : BasedOn alphabet s rs) {t : Row α} (ht : t ∈ packingRows rs z) {a : α}
    (ha : a ∈ t.word) : a ∈ z :: (alphabet ++ [s]) := by
  apply (packingRows_alphabet_perm hb ht).mem_iff.mp
  simpa only [List.mem_append, List.mem_singleton] using Row.mem_word_iff.mp ha

theorem original_family_alphabet_perm_range (k : Nat) :
    ((k + 8) :: (Partition.blockAlphabet k ++ [6])).Perm (List.range (k + 9)) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hhead : (((k + 1) + 8) :: (Partition.blockAlphabet (k + 1) ++ [6])).Perm
        ((k + 9) :: List.range (k + 9)) := by
      simpa only [Partition.blockAlphabet, List.cons_append, Nat.add_assoc] using ih.cons (k + 9)
    apply hhead.trans
    rw [show k + 1 + 9 = (k + 9) + 1 by omega, List.range_succ (n := k + 9)]
    exact List.perm_append_comm (l₁ := [k + 9]) (l₂ := List.range (k + 9))

theorem original_family_row_alphabet_perm_range (k : Nat) {t : Row Nat}
    (ht : t ∈ packingRows (Partition.blockRows k) (k + 8)) :
    (t.base ++ [t.satellite]).Perm (List.range (k + 9)) :=
  (packingRows_alphabet_perm (Partition.blockRows_basedOn k) ht).trans
    (original_family_alphabet_perm_range k)

theorem original_family_word_support (k : Nat) {t : Row Nat}
    (ht : t ∈ packingRows (Partition.blockRows k) (k + 8)) :
    ∀ a ∈ t.word, a < k + 9 := by
  intro a ha
  apply List.mem_range.mp
  exact (original_family_alphabet_perm_range k).mem_iff.mp
    (packingRows_word_mem (Partition.blockRows_basedOn k) ht ha)

/-- Range-form coverage is ready to combine with supported natural-word
assembly and the conversion to actual finite-alphabet words. -/
theorem original_family_cover_range (k : Nat) {p : List Nat}
    (hp : p.Perm (List.range (k + 9))) :
    ∃ t ∈ packingRows (Partition.blockRows k) (k + 8), t.Assigned p :=
  original_family_cover k (hp.trans (original_family_alphabet_perm_range k).symm)

end SuperpermutationUpperBound.Completion
