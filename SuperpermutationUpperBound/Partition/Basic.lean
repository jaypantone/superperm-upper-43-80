import SuperpermutationUpperBound.Transport.Counts
import SuperpermutationUpperBound.Packing
import SuperpermutationUpperBound.Transport.Blocks

/-! Block completeness means a row base represents every cyclic ordinary
permutation. It does not say that short rows cover their missing visible
classes. The latter requires the separate completion construction. -/
namespace SuperpermutationUpperBound

variable {α : Type}

def BlockComplete (alphabet : List α) (rs : List (Row α)) : Prop :=
  ∀ x : List α, x.Perm alphabet → ∃ r ∈ rs, CyclicEq r.base x

def BasedOn (alphabet : List α) (s : α) (rs : List (Row α)) : Prop :=
  ∀ r ∈ rs, r.Valid ∧ r.base.Perm alphabet ∧ r.satellite = s ∧
    (r.visible = r.base.length ∨ r.visible = r.base.length - 2)

def DistinctBlocks (rs : List (Row α)) : Prop :=
  rs.Pairwise (fun r t => ¬ CyclicEq r.base t.base)

namespace Transport

theorem rows_satellite {r t : Row α} {z : α} (ht : t ∈ rows r z) :
    t.satellite = r.satellite := by
  unfold rows at ht
  split at ht
  · obtain ⟨b, _, rfl⟩ := List.mem_map.mp ht
    rfl
  · obtain ⟨b, _, rfl⟩ := List.mem_map.mp ht
    rfl

theorem rows_base_perm {r t : Row α} {z : α} (ht : t ∈ rows r z) :
    t.base.Perm (z :: r.base) := by
  unfold rows at ht
  split at ht
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
    exact fullBases_perm hb
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
    exact shortBases_perm hb

end Transport

theorem BasedOn.ready {alphabet : List α} {s z : α} {rs : List (Row α)}
    (h : BasedOn alphabet s rs) (hz : z ∉ alphabet) (hzs : z ≠ s) :
    ∀ r ∈ rs, Transport.Ready z r ∧ r.base.length = alphabet.length := by
  intro r hr
  have h := h r hr
  refine ⟨⟨h.1, ?_, ?_, h.2.2.2⟩, h.2.1.length_eq⟩
  · intro hm
    exact hz (h.2.1.mem_iff.mp hm)
  · simpa only [h.2.2.1] using hzs

/-- Transport preserves the common alphabet, satellite, validity and allowed
deficits. This statement quantifies over arbitrary alphabet sizes. -/
theorem BasedOn.transport {alphabet : List α} {s z : α} {rs : List (Row α)}
    (h : BasedOn alphabet s rs) (hz : z ∉ alphabet) (hzs : z ≠ s) :
    BasedOn (z :: alphabet) s (Transport.packingRows rs z) := by
  intro t ht
  have hv := Transport.packingRows_valid (h.ready hz hzs) t ht
  obtain ⟨r, hr, ht⟩ := List.mem_flatMap.mp ht
  have hb := h r hr
  exact ⟨hv.1, (Transport.rows_base_perm ht).trans (hb.2.1.cons z),
    (Transport.rows_satellite ht).trans hb.2.2.1, hv.2.2⟩

/-- Every cyclic base block is still represented after adding a fresh letter.
This is a genuine all-size coverage induction step, including short rows. -/
theorem BlockComplete.transport [DecidableEq α] {alphabet : List α} {s z : α}
    {rs : List (Row α)} (hc : BlockComplete alphabet rs) (hb : BasedOn alphabet s rs)
    (ha : alphabet.Nodup) (hne : alphabet ≠ []) (hz : z ∉ alphabet) :
    BlockComplete (z :: alphabet) (Transport.packingRows rs z) := by
  intro y hy
  have hperm : y.Perm (alphabet ++ [z]) := hy.trans
    (by simpa using (List.perm_append_comm (l₁ := [z]) (l₂ := alphabet)))
  obtain ⟨x, hx, hblock⟩ := exists_inInsertionBlock_of_perm_append_satellite ha hne hz hperm
  obtain ⟨r, hr, hcyc⟩ := hc x hx
  have hblock' : InInsertionBlock z r.base y :=
    (InInsertionBlock.congr_base hcyc).mpr hblock
  obtain ⟨t, ht, hty⟩ :=
    (Transport.rows_cyclicEq_iff_inInsertionBlock (hb r hr).1 z y).mpr hblock'
  exact ⟨t, List.mem_flatMap.mpr ⟨r, hr, ht⟩, hty⟩

/-- Distinct old blocks have distinct descendants, including within each old
block. Equal actual endpoint tuples are permitted throughout. -/
theorem DistinctBlocks.transport [DecidableEq α] {alphabet : List α} {s z : α}
    {rs : List (Row α)} (hd : DistinctBlocks rs) (hb : BasedOn alphabet s rs)
    (hz : z ∉ alphabet) : DistinctBlocks (Transport.packingRows rs z) := by
  induction rs with
  | nil => exact List.Pairwise.nil
  | cons r rs ih =>
    have hd' := List.pairwise_cons.mp hd
    have hbr := hb r (by simp)
    have hzr : z ∉ r.base := fun hm => hz (hbr.2.1.mem_iff.mp hm)
    have hbt : BasedOn alphabet s rs := fun t ht => hb t (List.mem_cons_of_mem _ ht)
    change (Transport.rows r z ++ Transport.packingRows rs z).Pairwise _
    apply List.pairwise_append.mpr
    refine ⟨Transport.rows_pairwise_not_cyclicEq hbr.1 hzr, ih hd'.2 hbt, ?_⟩
    intro t ht u hu hcyc
    obtain ⟨q, hq, hu⟩ := List.mem_flatMap.mp hu
    have hbq := hbt q hq
    have hzq : z ∉ q.base := fun hm => hz (hbq.2.1.mem_iff.mp hm)
    exact hd'.1 q hq
      (Transport.rows_cyclicEq_implies_old_cyclicEq hbr.1 hbq.1 hzr hzq ht hu hcyc)

end SuperpermutationUpperBound
