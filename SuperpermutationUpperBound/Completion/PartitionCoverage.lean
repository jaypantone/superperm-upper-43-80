import SuperpermutationUpperBound.Completion.Coverage
import SuperpermutationUpperBound.Completion.Counts

/-! Literal permutation coverage for completed block families. The argument
deletes the new letter, locates the old insertion block using block completeness,
and uses the local visible/repair assignment theorem. No counting argument or
closed-component hypothesis is used to obtain coverage. -/

namespace SuperpermutationUpperBound.Completion

variable {α : Type}

/-- Completing a valid family representing every cyclic base block assigns
every permutation of the enlarged alphabet to one of its selected rows. -/
theorem packingRows_cover [DecidableEq α] {alphabet : List α} {s z : α}
    {rs : List (Row α)} (hb : BasedOn alphabet s rs) (hc : BlockComplete alphabet rs)
    (ha : alphabet.Nodup) (hne : alphabet ≠ []) (hs : s ∉ alphabet)
    (hz : z ∉ alphabet) (hzs : z ≠ s) {p : List α}
    (hp : p.Perm (z :: (alphabet ++ [s]))) :
    ∃ t ∈ packingRows rs z, t.Assigned p := by
  have hzold : z ∉ alphabet ++ [s] := by simp [List.mem_append, hz, hzs]
  have hperm : p.Perm ((alphabet ++ [s]) ++ [z]) := hp.trans
    (by simpa using (List.perm_append_comm (l₁ := [z]) (l₂ := alphabet ++ [s])))
  have hdel : (eraseSatellite z p).Perm (alphabet ++ [s]) :=
    eraseSatellite_perm_of_perm_append_satellite hperm hzold
  obtain ⟨x, hx, hblock⟩ :=
    exists_inInsertionBlock_of_perm_append_satellite ha hne hs hdel
  obtain ⟨r, hr, hcyc⟩ := hc x hx
  have hbr := hb r hr
  have hblock' : InInsertionBlock r.satellite r.base (eraseSatellite z p) := by
    rw [hbr.2.2.1]
    exact (InInsertionBlock.congr_base hcyc).mpr hblock
  have hpr : p.Perm (z :: (r.base ++ [r.satellite])) := by
    rw [hbr.2.2.1]
    exact hp.trans ((hbr.2.1.symm.append_right [s]).cons z)
  have hzr : z ∉ r.base := fun hm => hz (hbr.2.1.mem_iff.mp hm)
  have hzsr : z ≠ r.satellite := by simpa only [hbr.2.2.1] using hzs
  obtain ⟨t, ht, htp⟩ := completeRows_cover_block_extensions hbr.1 hzr hzsr hpr hblock'
  exact ⟨t, List.mem_flatMap.mpr ⟨r, hr, ht⟩, htp⟩

theorem blockAlphabet_satellite_fresh (k : Nat) : 6 ∉ Partition.blockAlphabet k := by
  induction k with
  | zero => decide
  | succ k ih =>
    change 6 ∉ (k + 8) :: Partition.blockAlphabet k
    simp only [List.mem_cons, not_or]
    exact ⟨by omega, ih⟩

/-- Unconditional literal assignment coverage for every completed member of
the original all-size block family. Joining these rows remains a separate task.
-/
theorem original_family_cover (k : Nat) {p : List Nat}
    (hp : p.Perm ((k + 8) :: (Partition.blockAlphabet k ++ [6]))) :
    ∃ t ∈ packingRows (Partition.blockRows k) (k + 8), t.Assigned p := by
  exact packingRows_cover (Partition.blockRows_basedOn k) (Partition.blockRows_complete k)
    (Partition.blockAlphabet_nodup k) (Partition.blockAlphabet_nonempty k)
    (blockAlphabet_satellite_fresh k) (Partition.blockAlphabet_fresh k) (by omega) hp

end SuperpermutationUpperBound.Completion
