import SuperpermutationUpperBound.Certificates.EightSeed
import SuperpermutationUpperBound.Completion.Closed
import SuperpermutationUpperBound.Completion.Alphabet
import SuperpermutationUpperBound.Assembly.Supported

namespace SuperpermutationUpperBound.Certificates.Word8
open Transport
open EightSeed

def paths (ip : State) : List (Row Nat) := Completion.portPath (seedRow ip.1) 7 ip.2.val

def trail : List (Row Nat) := labels.flatMap paths

theorem seedRow_length (i : Fin 120) : (seedRow i).base.length = 6 :=
  (seed_basedOn _ (List.getElem_mem _)).2.1.length_eq

theorem seedRow_kind (i : Fin 120) :
    (seedRow i).visible = (seedRow i).base.length ∨
    (seedRow i).visible = (seedRow i).base.length - 2 :=
  (seed_basedOn _ (List.getElem_mem _)).2.2.2

theorem seedRow_compatible (i : Fin 120) :
    (seedRow i).Compatible (seedRow (i + 1)) := by
  have hc := closedTrail_getElem_compatible seed_closed
    (⟨i.val, by rw [seed_length]; exact i.isLt⟩ : Fin seed.length)
  simpa only [seedRow, seed_length, Fin.val_add, Fin.val_one, Nat.add_mod_mod] using hc

theorem paths_nonempty (ip : State) : paths ip ≠ [] :=
  Completion.portPath_nonempty _ _ _

theorem paths_internal (ip : State) :
    RowTrailCompatible ((paths ip).head (paths_nonempty ip)) (paths ip).tail :=
  Completion.portPath_internal 7 _ (by rw [seedRow_length]; decide) (seedRow_kind ip.1)

theorem paths_boundary (ip : State) :
    ((paths ip).getLast (paths_nonempty ip)).Compatible
      ((paths (next ip)).head (paths_nonempty (next ip))) := by
  change ((Completion.portPath (seedRow ip.1) 7 ip.2.val).getLast _).tail =
    ((Completion.portPath (seedRow (next ip).1) 7 (next ip).2.val).head _).head
  rw [Completion.portPath_last_tail 7 (by rw [seedRow_length]; decide) (seedRow_kind ip.1)
      (by rw [seedRow_length]; exact ip.2.isLt),
    Completion.portPath_head 7 (by rw [seedRow_length]; decide) (seedRow_kind (next ip).1)
      (by rw [seedRow_length]; exact (next ip).2.isLt)]
  have hs : (next ip).2.val = portTarget (seedRow ip.1) ip.2.val := by
    rw [next_eq]
    exact rowPortSuccessor_snd_val (by decide) 6 (by decide) seedRow seedRow_length ip
  rw [hs]
  have hf : (next ip).1 = ip.1 + 1 := rfl
  rw [hf, seedRow_compatible ip.1]

theorem trail_closed : ClosedTrail trail :=
  orbitRows_closedTrail_of_endpoints paths next paths_nonempty paths_internal paths_boundary
    (0,0) (by decide : 0 < 600) orbit_return

theorem seedRow_map : (List.finRange 120).map seedRow = seed := by
  apply List.ext_getElem (by simp [seed_length])
  intro i hi hj
  simp [seedRow]

theorem trail_inventory : trail.Perm (Completion.packingRows seed 7) := by
  have hlocal (i : Fin 120) :
      ((List.finRange 5).flatMap (fun p => paths (i,p))).Perm (Completion.completeRows (seedRow i) 7) := by
    have he := Completion.portPaths_flatten_perm 7
      (by rw [seedRow_length]; decide) (seedRow_kind i)
    have heq : (List.finRange 5).flatMap (fun p => paths (i,p)) =
        ((List.range 5).map (Completion.portPath (seedRow i) 7)).flatten := by
      rw [← map_val_finRange 5, List.map_map]
      rfl
    rw [heq]
    simpa only [seedRow_length] using he
  have hp := flatMap_perm_of_pointwise (List.finRange 120)
    (fun i => (List.finRange 5).flatMap (fun p => paths (i,p)))
    (fun i => Completion.completeRows (seedRow i) 7) (fun i _ => hlocal i)
  have heq := congrArg (fun xs => xs.flatMap (fun r => Completion.completeRows r 7)) seedRow_map
  rw [List.flatMap_map] at heq
  have hi : (((List.finRange 120).product (List.finRange 5)).flatMap paths).Perm
      (Completion.packingRows seed 7) := by
    simpa only [Completion.packingRows, List.product, List.flatMap_assoc, List.flatMap_map, Function.comp_def]
      using hp.trans (List.Perm.of_eq heq)
  exact (labels_inventory.flatMap_right paths).trans hi

theorem completed_valid : ∀ r ∈ Completion.packingRows seed 7,
    r.Valid ∧ r.base.length = 7 :=
  Completion.packingRows_valid seed_basedOn (by decide) (by decide)

theorem completed_length : (Completion.packingRows seed 7).length = 816 := by
  rw [Completion.packingRows_length 7 6
    (fun r hr => ⟨(seed_basedOn r hr).1, (seed_basedOn r hr).2.1.length_eq⟩),
    seed_length, seed_charge]

theorem completed_visible : ((Completion.packingRows seed 7).map Row.visible).sum = 5040 := by
  rw [Completion.packingRows_visible_sum 7 6
    (fun r hr => ⟨(seed_basedOn r hr).1, (seed_basedOn r hr).2.1.length_eq⟩), seed_length]

theorem trail_word_spec : (trailWord 8 trail).length = 46181 ∧
    (∀ r ∈ trail, ∀ p, r.Assigned p → p.IsInfix (trailWord 8 trail)) := by
  have hv : ∀ r ∈ trail, 1 ≤ r.visible ∧ r.base.length + 1 = 8 := by
    intro r hr
    have h := completed_valid r (trail_inventory.mem_iff.mp hr)
    exact ⟨h.1.2.2.1, by omega⟩
  have hw := trailWord_spec (by decide : 4 ≤ 8) trail_closed hv
  refine ⟨?_, hw.2⟩
  rw [hw.1, (trail_inventory.map Row.visible).sum_eq, trail_inventory.length_eq,
    completed_visible, completed_length]

theorem trail_word_support : ∀ a ∈ trailWord 8 trail, a < 8 := by
  apply trailWord_support
  intro r hr a ha
  have hm := Completion.packingRows_word_mem seed_basedOn (trail_inventory.mem_iff.mp hr) ha
  have hp : (7 :: (Partition.SeedBase.alphabet6 ++ [6])).Perm (List.range 8) := by decide
  exact List.mem_range.mp (hp.mem_iff.mp hm)

def word : Word 8 := liftWord (trailWord 8 trail) trail_word_support

theorem word_length : word.length = 46181 := by
  simpa only [word, liftWord_length] using trail_word_spec.1

theorem word_superpermutation : IsSuperpermutation word := by
  apply isSuperpermutation_liftWord_of_covers
  intro p hp
  have hp' : p.Perm (7 :: (Partition.SeedBase.alphabet6 ++ [6])) :=
    hp.trans (by decide)
  obtain ⟨r, hr, ha⟩ := Completion.packingRows_cover seed_basedOn seed_complete
    (by decide) (by decide) (by decide) (by decide) (by decide) hp'
  exact trail_word_spec.2 r (trail_inventory.mem_iff.mpr hr) p ha

theorem word8_46181 : HasSuperpermutationOfLengthAtMost 8 46181 :=
  ⟨word, word_superpermutation, word_length.le⟩

#print axioms next_eq
#print axioms orbit_return
#print axioms labels_inventory
#print axioms trail_closed
#print axioms trail_inventory
#print axioms word8_46181

end SuperpermutationUpperBound.Certificates.Word8
