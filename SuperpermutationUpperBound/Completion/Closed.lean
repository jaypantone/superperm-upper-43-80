import SuperpermutationUpperBound.Completion.Paths
import SuperpermutationUpperBound.Completion.Counts
import SuperpermutationUpperBound.Partition.ClosedFamily

/-! Exact closed-trail decomposition of the final completion. Literal row
occurrences are preserved; the port successor is inherited from transport. -/
namespace SuperpermutationUpperBound.Completion
variable {α : Type}
open Transport

theorem portPaths_inventory (rs : List (Row α)) (z : α) (n : Nat)
    (hn : 3 ≤ n) (hlen : ∀ r ∈ rs, r.base.length = n)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2) :
    ((List.finRange rs.length).flatMap (fun i =>
      (List.finRange (n - 1)).flatMap (fun p => portPath rs[i.val] z p.val))).Perm
      (rs.flatMap (fun r => completeRows r z)) := by
  have hp : ((List.finRange rs.length).flatMap (fun i =>
      (List.finRange (n - 1)).flatMap (fun p => portPath rs[i.val] z p.val))).Perm
      ((List.finRange rs.length).flatMap (fun i => completeRows rs[i.val] z)) := by
    apply flatMap_perm_of_pointwise
    intro i _
    have hi := hlen rs[i.val] (List.getElem_mem _)
    have hk := hkind rs[i.val] (List.getElem_mem _)
    have he := portPaths_flatten_perm z (by omega) hk
    rw [hi] at he
    have heq : (List.finRange (n - 1)).flatMap (fun p => portPath rs[i.val] z p.val) =
        ((List.range (n - 1)).map (portPath rs[i.val] z)).flatten := by
      rw [← map_val_finRange (n - 1), List.map_map]
      rfl
    rw [heq]
    exact he
  refine hp.trans ?_
  have heq := congrArg (fun xs => xs.flatMap (fun r => completeRows r z)) (finRange_map_getElem rs)
  rw [List.flatMap_map] at heq
  exact List.Perm.of_eq heq

theorem product_portPaths_inventory (rs : List (Row α)) (z : α) (n : Nat)
    (hn : 3 ≤ n) (hlen : ∀ r ∈ rs, r.base.length = n)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2) :
    (((List.finRange rs.length).product (List.finRange (n - 1))).flatMap
      (fun ip => portPath rs[ip.1.val] z ip.2.val)).Perm
        (rs.flatMap (fun r => completeRows r z)) := by
  simpa only [List.product, List.flatMap_assoc, List.flatMap_map, Function.comp_def]
    using portPaths_inventory rs z n hn hlen hkind

/-- Full/deficit-two closed trails complete to closed trails using every lift
and every repair row exactly once, with no distinct-endpoint assumption. -/
theorem completion_closedTrail {rs : List (Row α)} (z : α) (n : Nat)
    (hn : 3 ≤ n) (hc : ClosedTrail rs)
    (hlen : ∀ r ∈ rs, r.base.length = n)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2) :
    ∃ trails : List (List (Row α)), (∀ trail ∈ trails, ClosedTrail trail) ∧
      trails.flatten.Perm (rs.flatMap (fun r => completeRows r z)) := by
  have hR : 0 < rs.length := List.length_pos_iff.mpr hc.1
  let σ := rowPortSuccessor hR n hn (fun i => rs[i.val])
  let labels := (List.finRange rs.length).product (List.finRange (n - 1))
  let paths := fun ip : Fin rs.length × Fin (n - 1) => portPath rs[ip.1.val] z ip.2.val
  have hi (i : Fin rs.length) : (rs[i.val]).base.length = n :=
    hlen _ (List.getElem_mem _)
  have hk (i : Fin rs.length) := hkind _ (List.getElem_mem (l := rs) (n := i.val) i.isLt)
  have hne : ∀ ip, paths ip ≠ [] := fun ip => portPath_nonempty _ _ _
  have hinternal : ∀ ip, RowTrailCompatible ((paths ip).head (hne ip)) (paths ip).tail := by
    intro ip
    exact portPath_internal z _ (by rw [hi]; omega) (hk ip.1)
  have hboundary : ∀ ip, ((paths ip).getLast (hne ip)).Compatible
      ((paths (σ ip)).head (hne (σ ip))) := by
    intro ip
    change ((portPath rs[ip.1.val] z ip.2.val).getLast _).tail =
      ((portPath rs[(σ ip).1.val] z (σ ip).2.val).head _).head
    rw [portPath_last_tail z (by rw [hi]; exact hn) (hk ip.1) (by rw [hi]; exact ip.2.isLt),
      portPath_head z (by rw [hi]; exact hn) (hk (σ ip).1)
        (by rw [hi]; exact (σ ip).2.isLt)]
    have hs : (σ ip).2.val = portTarget rs[ip.1.val] ip.2.val :=
      rowPortSuccessor_snd_val hR n hn _ hi ip
    rw [hs]
    have hrow := closedTrail_getElem_compatible hc ip.1
    have hf : (σ ip).1.val = (ip.1.val + 1) % rs.length :=
      rowPortSuccessor_fst_val hR n hn _ ip
    simp only [hf]
    rw [hrow]
  obtain ⟨trails, hclosed, hperm⟩ := finite_labels_path_assembly σ labels
    ((nodup_finRange _).product (nodup_finRange _))
    (by
      intro ip
      exact List.mem_product.mpr ⟨List.mem_finRange _, List.mem_finRange _⟩) paths hne hinternal hboundary
  exact ⟨trails, hclosed, hperm.trans (product_portPaths_inventory rs z n hn hlen hkind)⟩

end SuperpermutationUpperBound.Completion

namespace SuperpermutationUpperBound
variable {α : Type}

/-- Completion preserves an exact closed decomposition of all row occurrences. -/
theorem HasClosedDecomposition.completion {rs : List (Row α)}
    (h : HasClosedDecomposition rs) (z : α) (n : Nat) (hn : 3 ≤ n)
    (hlen : ∀ r ∈ rs, r.base.length = n)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2) :
    HasClosedDecomposition (rs.flatMap (fun r => Completion.completeRows r z)) := by
  obtain ⟨trails, hc, hp⟩ := h
  have hlocal : ∀ trail ∈ trails,
      HasClosedDecomposition (trail.flatMap (fun r => Completion.completeRows r z)) := by
    intro trail ht
    apply Completion.completion_closedTrail z n hn (hc trail ht)
    · intro r hr
      exact hlen r (hp.mem_iff.mp (List.mem_flatten.mpr ⟨trail, ht, hr⟩))
    · intro r hr
      exact hkind r (hp.mem_iff.mp (List.mem_flatten.mpr ⟨trail, ht, hr⟩))
  exact (HasClosedDecomposition.flatMap trails _ hlocal).perm (hp.flatMap_right _)

namespace Completion

/-- The actual recursively constructed original family completes to closed
trails at every size. The inventory is the same family used by the completion
coverage and accounting theorems. -/
theorem original_family_closedDecomposition (k : Nat) :
    HasClosedDecomposition (packingRows (Partition.blockRows k) (k + 8)) := by
  apply (Partition.blockRows_closedDecomposition k).completion (k + 8) (k + 7) (by omega)
  · intro r hr
    exact (Partition.blockRows_basedOn k r hr).2.1.length_eq.trans (Partition.blockAlphabet_length k)
  · intro r hr
    exact (Partition.blockRows_basedOn k r hr).2.2.2

end Completion
end SuperpermutationUpperBound

#print axioms SuperpermutationUpperBound.Completion.completion_closedTrail
#print axioms SuperpermutationUpperBound.HasClosedDecomposition.completion
#print axioms SuperpermutationUpperBound.Completion.original_family_closedDecomposition
