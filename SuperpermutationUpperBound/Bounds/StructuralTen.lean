import SuperpermutationUpperBound.Assembly.CircleRows
import SuperpermutationUpperBound.Certificates.Circle54
import SuperpermutationUpperBound.Completion.Alphabet

/-! A ten-symbol bound obtained from the literal 54-circle certificate and
balanced module cuts, independently of the larger finite word certificate. -/
namespace SuperpermutationUpperBound.Bounds.StructuralTen
open CircleTransport Transport Certificates Certificates.CircleBase Partition

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

abbrev Index := Fin 52 × Fin 7

def sourceRows : List (Row Nat) := SprintBase.rows8.map (retag 8)
def completedRows : List (Row Nat) := Completion.packingRows sourceRows 9
def family (i : Index) : List (Row Nat) := completionWalk (family8 i.1) 9 i.2.val
def labels : List Index := (List.finRange 52).product (List.finRange 7)
def stateAlphabet : Finset Nat := (Finset.range 10).erase 8

theorem source_basedOn : BasedOn SprintBase.alphabet8 8 sourceRows := by
  intro r hr
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hr
  have hb := SprintBase.rows8_basedOn t ht
  refine ⟨⟨hb.1.1, ?_, hb.1.2.2⟩, hb.2.1, rfl, hb.2.2.2⟩
  intro hm
  exact (by decide : 8 ∉ SprintBase.alphabet8) (hb.2.1.mem_iff.mp hm)

theorem source_complete : BlockComplete SprintBase.alphabet8 sourceRows := by
  intro x hx
  obtain ⟨r, hr, hc⟩ := SprintBase.rows8_complete x hx
  exact ⟨retag 8 r, List.mem_map_of_mem hr, hc⟩

theorem source_counts : sourceRows.length = 5040 ∧ (sourceRows.map Row.charge).sum = 2352 := by
  constructor
  · simpa only [sourceRows, List.length_map] using SprintBase.rows8_counts.1
  · have he : sourceRows.map Row.charge = SprintBase.rows8.map Row.charge := by
      rw [sourceRows, List.map_map]
      rfl
    rw [he]
    exact SprintBase.rows8_counts.2

theorem source_ready : ∀ r ∈ sourceRows, r.Valid ∧ r.base.length = 8 :=
  fun r hr => ⟨(source_basedOn r hr).1, (source_basedOn r hr).2.1.length_eq⟩

theorem family8_inventory : ((List.finRange 52).flatMap family8).Perm sourceRows := by
  have he : (List.finRange 52).map family8 = components8 8 := by
    apply List.ext_getElem
    · simp [components8_count]
    · intro i hi hj
      simp [family8, componentAt, List.getElem?_eq_getElem hj]
  have hi := rawComponents8_inventory.map (retag 8)
  simpa only [List.flatMap_def, he, components8, ← List.map_flatten, sourceRows] using hi

theorem family8_shape (i : Fin 52) : ∀ r ∈ family8 i,
    r.base.length = 8 ∧ r.satellite = 8 ∧
      (r.visible = r.base.length ∨ r.visible = r.base.length - 2) :=
  components8_shape 8 _ (componentAt_mem _ i.val (by rw [components8_count]; exact i.isLt))

theorem family8_closed_winding (i : Fin 52) :
    ClosedTrail (family8 i) ∧ (7 : Int) ∣ signedExcess (family8 i) := by
  have hm : family8 i ∈ components8 8 :=
    componentAt_mem _ i.val (by rw [components8_count]; exact i.isLt)
  exact ⟨components8_closed 8 _ hm, components8_winding 8 _ hm⟩

theorem labels_perm_univ : labels.Perm Finset.univ.toList := by
  apply (List.perm_ext_iff_of_nodup ?_ (Finset.nodup_toList _)).mpr
  · intro i
    constructor
    · intro _; simp
    · intro _; exact List.mem_product.mpr ⟨List.mem_finRange i.1, List.mem_finRange i.2⟩
  · exact List.Nodup.product (nodup_finRange _) (nodup_finRange _)

theorem family_inventory : (labels.flatMap family).Perm completedRows := by
  have hl : ((List.finRange 52).flatMap (fun i => (List.finRange 7).flatMap
      (fun p => completionWalk (family8 i) 9 p.val))).Perm
      ((List.finRange 52).flatMap (fun i => Completion.packingRows (family8 i) 9)) := by
    apply List.Perm.flatMap (List.Perm.refl _)
    intro i _
    exact completionWalk_inventory (family8 i) 9 8 (by decide)
      (fun r hr => (family8_shape i r hr).1) (fun r hr => (family8_shape i r hr).2.2)
  have hi := family8_inventory.flatMap_right (fun r => Completion.completeRows r 9)
  have he : labels.flatMap family = (List.finRange 52).flatMap (fun i =>
      (List.finRange 7).flatMap (fun p => completionWalk (family8 i) 9 p.val)) := by
    simp only [labels, List.product, List.flatMap_assoc, List.flatMap_map, family]
  rw [he]
  exact hl.trans (by simpa only [completedRows, Completion.packingRows, List.flatMap_assoc] using hi)

theorem family_univ_inventory :
    ((Finset.univ.toList : List Index).flatMap family).Perm completedRows :=
  (labels_perm_univ.symm.flatMap_right family).trans family_inventory

theorem family_row_mem (i : Index) {r : Row Nat} (hr : r ∈ family i) : r ∈ completedRows :=
  family_univ_inventory.mem_iff.mp (List.mem_flatMap.mpr ⟨i, by simp, hr⟩)

theorem family_closed (i : Index) : ClosedTrail (family i) := by
  have hc := (family8_closed_winding i.1).1
  have hw := (family8_closed_winding i.1).2
  let rs := family8 i.1
  let p := i.2.val
  have hlen := fun r hr => (family8_shape i.1 r hr).1
  have hkind := fun r hr => (family8_shape i.1 r hr).2.2
  have hne := completionWalk_nonempty rs 9 p hc.1
  have hchainG : ∀ (ts : List (Row Nat)) (hc : ClosedTrail ts),
      RowTrailCompatible (ts.head hc.1) ts.tail := by
    intro ts ht
    cases ts with
    | nil => exact False.elim (ht.1 rfl)
    | cons r rest => exact closedTrail_internal ht
  have hchain := hchainG rs hc
  have hi := completionWalk_internal rs hc.1 9 8 p (by decide) i.2.isLt hlen hkind hchain
  have hb : ((completionWalk rs 9 p).getLast hne).Compatible ((completionWalk rs 9 p).head hne) := by
    change _ = _
    rw [completionWalk_last_tail rs hc.1 9 8 p (by decide) i.2.isLt hlen hkind,
      completionWalk_head rs hc.1 9 8 p (by decide) i.2.isLt hlen hkind,
      completionExit_eq_self_of_winding rs 7 (by decide) hlen hkind hw p i.2.isLt,
      closedTrail_last_compatible_head hc]
  have hr := pathRunsTo_of_path_spec _ _ hne hi hb
  obtain ⟨a, as, he⟩ := List.exists_cons_of_ne_nil hne
  simp only [he, List.head_cons] at hr
  change ClosedTrail (completionWalk rs 9 p)
  rw [he]
  exact closedTrail_of_pathRunsTo hr

theorem completed_counts : completedRows.length = 42672 ∧
    (completedRows.map Row.visible).sum = 362880 := by
  constructor
  · rw [completedRows, Completion.packingRows_length 9 8 source_ready, source_counts.1, source_counts.2]
  · rw [completedRows, Completion.packingRows_visible_sum 9 8 source_ready, source_counts.1]

theorem completed_valid {r : Row Nat} (hr : r ∈ completedRows) : r.Valid ∧ r.base.length = 9 :=
  Completion.packingRows_valid source_basedOn (by decide) (by decide) r hr

theorem alphabet_range : (9 :: (SprintBase.alphabet8 ++ [8])).Perm (List.range 10) := by decide

theorem completed_support {r : Row Nat} (hr : r ∈ completedRows) : ∀ a ∈ r.word, a < 10 := by
  intro a ha
  exact List.mem_range.mp (alphabet_range.mem_iff.mp (Completion.packingRows_word_mem source_basedOn hr ha))

theorem completed_cover {p : List Nat} (hp : p.Perm (List.range 10)) :
    ∃ r ∈ completedRows, r.Assigned p :=
  Completion.packingRows_cover source_basedOn source_complete (by decide) (by decide)
    (by decide) (by decide) (by decide) (hp.trans alphabet_range.symm)

theorem family_cover {p : List Nat} (hp : p.Perm (List.range 10)) :
    ∃ i, ∃ r ∈ family i, r.Assigned p := by
  obtain ⟨r, hr, ha⟩ := completed_cover hp
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp (family_univ_inventory.mem_iff.mpr hr)
  exact ⟨i, r, hi, ha⟩

theorem stateAlphabet_card : stateAlphabet.card = 9 := by decide

theorem exists_superpermutation : ∃ w : Word 10, IsSuperpermutation w ∧ w.length ≤ 4035009 := by
  have hcover := Circle54.safe_cover.sound Circle54.circles_valid (by decide : 3 ≤ 7 + 1)
  obtain ⟨t, J, w, hw, ht, hJ, hlen⟩ := exists_word_of_circle_rows (K := 10) (ell := 1)
    family Circle54.circles (by decide) (by decide)
    (fun i r hr => by have h := (completed_valid (family_row_mem i hr)).2; omega)
    (fun i r hr => (completed_valid (family_row_mem i hr)).1.2.2.1)
    family_closed Circle54.circles_valid hcover stateAlphabet
    (fun c hc a ha => by
      exact Finset.mem_erase.mpr ⟨fun he => Circle54.circles_avoid_satellite c hc (he ▸ ha),
        Finset.mem_range.mpr (Circle54.circles_support c hc a ha)⟩)
    Circle54.circles_support (fun i r hr => completed_support (family_row_mem i hr))
    (fun p hp => family_cover hp)
  have hrlen := family_univ_inventory.length_eq.trans completed_counts.1
  have hrvis := (family_univ_inventory.map Row.visible).sum_eq.trans completed_counts.2
  rw [hrlen, hrvis, Circle54.circles_count] at hlen
  rw [Circle54.circles_count] at ht
  rw [stateAlphabet_card] at hJ
  norm_num at hlen hJ
  refine ⟨w, hw, ?_⟩
  omega

end SuperpermutationUpperBound.Bounds.StructuralTen
