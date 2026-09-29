import SuperpermutationUpperBound.Completion.Local
import SuperpermutationUpperBound.Completion.Projection

/-!
Local literal coverage for completion. Every extension of an old full block
is assigned either to a prescribed lifted row, when its deleted old class is
visible, or to the full repair row for the omitted old class. The proof uses
literal insertion identities and does not infer coverage from cardinalities.
-/

namespace SuperpermutationUpperBound.Completion

open Transport

variable {α : Type}

theorem assigned_of_entry_cyclicEq {r : Row α} {p : List α} {j : Nat}
    (hj : j < r.visible) (hc : CyclicEq (r.entry j) p) : r.Assigned p := by
  obtain ⟨i, hi⟩ := hc
  refine ⟨j, hj, i.val, ?_, hi.symm⟩
  simpa [Row.entry] using i.isLt

/-- Extensions of one old visible class belong to a prescribed lifted row. -/
theorem exists_liftRow_assigned_of_visible [DecidableEq α]
    {r : Row α} (hr : r.Valid) {z : α} (hzs : z ≠ r.satellite)
    {p : List α} (hp : p.Nodup) (hsp : r.satellite ∈ p) (hzp : z ∈ p)
    {j : Nat} (hj : j < r.visible)
    (hold : CyclicEq (rot r.base j ++ [r.satellite]) (eraseSatellite z p)) :
    ∃ t ∈ liftRows r z, t.Assigned p := by
  have hsrot : r.satellite ∉ rot r.base j :=
    fun hm => hr.2.1 ((rot_perm r.base j).mem_iff.mp hm)
  obtain ⟨b, hb, hclass⟩ := extension_normal_form hp hsp hzp hsrot hzs hold
  have hb' : b ≤ r.base.length := by simpa only [rot_length] using hb
  obtain ⟨i, hi, k, hk, he⟩ := visible_lift_rotation r.base z hr.2.2.2 hj hb'
  refine ⟨liftRow r z i, List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩, ?_⟩
  apply assigned_of_entry_cyclicEq hk
  change CyclicEq (rot (insertLetter r.base z i) k ++ [r.satellite]) p
  exact Eq.mp (congrArg (fun w => CyclicEq (w ++ [r.satellite]) p) he.symm) hclass

/-- An omitted old class is assigned in full to its satellite-z repair row. -/
theorem repairRow_assigned_of_omitted [DecidableEq α]
    {r : Row α} (hr : r.Valid) {z : α} (hz : z ∉ r.base) (hzs : z ≠ r.satellite)
    {p : List α} (hp : p.Nodup) (hzp : z ∈ p) {j : Nat}
    (hstart : r.visible ≤ j) (hj : j < r.base.length)
    (hold : CyclicEq (rot r.base j ++ [r.satellite]) (eraseSatellite z p)) :
    repairRow r z j ∈ repairRows r z ∧ (repairRow r z j).Assigned p := by
  constructor
  · apply List.mem_map.mpr
    refine ⟨j, List.mem_range'_1.mpr ⟨hstart, ?_⟩, rfl⟩
    have := hr.2.2.2
    omega
  · have hblock : InInsertionBlock z (rot r.base j ++ [r.satellite]) p :=
      inInsertionBlock_of_cyclicEq_eraseSatellite hp hzp hold
    apply (Row.assigned_iff_inInsertionBlock_of_full (repairRow_valid hr hz hzs j) ?_).mpr
    · exact hblock
    · simp [repairRow]

/-- Every literal extension of the old full insertion block is assigned to one
of the actual selected completion rows, including all omitted old gaps.
-/
theorem completeRows_cover_block_extensions [DecidableEq α]
    {r : Row α} (hr : r.Valid) {z : α} (hz : z ∉ r.base) (hzs : z ≠ r.satellite)
    {p : List α} (hp : p.Perm (z :: (r.base ++ [r.satellite])))
    (hblock : InInsertionBlock r.satellite r.base (eraseSatellite z p)) :
    ∃ t ∈ completeRows r z, t.Assigned p := by
  have hbase : (r.base ++ [r.satellite]).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hr.1, by simp, ?_⟩
    intro a ha b hb hab
    have hb' : b = r.satellite := List.mem_singleton.mp hb
    subst b
    subst a
    exact hr.2.1 ha
  have hpn : p.Nodup := hp.nodup_iff.mpr
    (List.nodup_cons.mpr ⟨by simp [List.mem_append, hz, hzs], hbase⟩)
  have hsp : r.satellite ∈ p := hp.mem_iff.mpr (by simp)
  have hzp : z ∈ p := hp.mem_iff.mpr (by simp)
  obtain ⟨j, hold⟩ := hblock
  by_cases hj : j.val < r.visible
  · obtain ⟨t, ht, htp⟩ := exists_liftRow_assigned_of_visible hr hzs hpn hsp hzp hj hold
    exact ⟨t, List.mem_append.mpr (Or.inl ht), htp⟩
  · obtain ⟨ht, htp⟩ := repairRow_assigned_of_omitted hr hz hzs hpn hzp
      (Nat.le_of_not_lt hj) j.isLt hold
    exact ⟨repairRow r z j.val, List.mem_append.mpr (Or.inr ht), htp⟩

end SuperpermutationUpperBound.Completion
