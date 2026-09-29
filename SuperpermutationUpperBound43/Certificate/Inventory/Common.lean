import SuperpermutationUpperBound43.Certificate.Canonical
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Nodup

/-! Abstract facts for checking the canonical inventory in finite chunks. -/
namespace SuperpermutationUpperBound43.Certificate.Inventory

open SuperpermutationUpperBound

def key (x : List Nat) : Nat := x.foldl (fun v a => 10 * v + a) 0

def le (x y : List Nat) : Bool := decide (key x ≤ key y)

theorem canonical_mem {x : List Nat}
    (hx : x.Perm Partition.SprintBase.alphabet9) :
    canonical x ∈ canonicalBases := by
  have hx' := hx.trans alphabet9_perm_standard
  have hzero : 0 ∈ x := hx'.mem_iff.mpr (by decide)
  obtain ⟨a, b, rfl, ha⟩ := List.eq_append_cons_of_mem hzero
  have hi : (a ++ 0 :: b).idxOf 0 = a.length := by
    simp [List.idxOf_append, ha]
  have he : canonical (a ++ 0 :: b) = 0 :: (b ++ a) := by
    simp only [canonical, hi, rot_append_length, List.cons_append]
  have hp : (0 :: (b ++ a)).Perm [0, 1, 2, 3, 4, 5, 6, 7, 8] := by
    simpa only [rot_append_length, List.cons_append] using
      ((rot_perm (a ++ 0 :: b) a.length).trans hx')
  rw [he]
  exact List.mem_map.mpr ⟨b ++ a,
    List.mem_permutations'.mpr ((List.perm_cons 0).mp hp), rfl⟩

theorem canonicalBases_card : canonicalBases.length = 40320 := by
  rw [canonicalBases, List.length_map,
    ← (List.permutations_perm_permutations'
      ([1, 2, 3, 4, 5, 6, 7, 8] : List Nat)).length_eq,
    List.length_permutations]
  decide

theorem inventory_of_nodup {rs : List (Row Nat)}
    (hb : BasedOn Partition.SprintBase.alphabet9 9 rs)
    (hn : (rs.map (fun r => canonical r.base)).Nodup)
    (hl : rs.length = 40320) :
    (rs.map (fun r => canonical r.base)).Perm canonicalBases := by
  have hs : (rs.map (fun r => canonical r.base)) ⊆ canonicalBases := by
    intro b hbmem
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hbmem
    exact canonical_mem (hb r hr).2.1
  apply (List.subperm_of_subset hn hs).perm_of_length_le
  rw [canonicalBases_card, List.length_map, hl]

theorem nodup_of_strict_keys {bs : List (List Nat)}
    (hs : (bs.map key).IsChain (· < ·)) : bs.Nodup :=
  List.Nodup.of_map key (List.isChain_iff_pairwise.mp hs).nodup

theorem normalized_nodup_of_keys {rs : List (Row Nat)}
    (hn : (rs.map (fun r => key (canonical r.base))).Nodup) :
    (rs.map (fun r => canonical r.base)).Nodup := by
  apply List.Nodup.of_map key
  simpa only [List.map_map, Function.comp_def] using hn

def chunkRows (rs : List (Row Nat)) (size count : Nat) : List (Row Nat) :=
  (List.range count).flatMap (fun i => (rs.drop (i * size)).take size)

theorem chunkRows_eq_take (rs : List (Row Nat)) (size count : Nat) :
    chunkRows rs size count = rs.take (count * size) := by
  induction count with
  | zero => simp [chunkRows]
  | succ count ih =>
    unfold chunkRows at ih ⊢
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, ih,
      Nat.succ_mul, List.take_add]

theorem mapped_chunkRows {β : Type*} (rs : List (Row Nat)) (size count : Nat)
    (f : Row Nat → β) :
    (List.range count).flatMap (fun i => ((rs.drop (i * size)).take size).map f) =
      (rs.take (count * size)).map f := by
  simpa only [chunkRows, List.map_flatMap] using
    congrArg (List.map f) (chunkRows_eq_take rs size count)

end SuperpermutationUpperBound43.Certificate.Inventory
