import SuperpermutationUpperBound.Certificates.NineRecipe
import SuperpermutationUpperBound.Completion.Alphabet
import SuperpermutationUpperBound.Completion.Closed
import SuperpermutationUpperBound.Assembly.MacroSpelling
import SuperpermutationUpperBound.Assembly.Supported

/-! Semantic integration of the nine-symbol finite recipe.
The final word bound is not asserted until its cut-trail inventory is checked. -/
namespace SuperpermutationUpperBound.Certificates.Word9
open NineRecipe Partition Transport

/-- Every ordinary permutation rotates to the canonical zero-first list. -/
theorem canonicalBases_complete {x : List Nat} (hx : x.Perm alphabet7) :
    ∃ b ∈ canonicalBases, CyclicEq b x := by
  have hzero : 0 ∈ x := hx.mem_iff.mpr (by decide)
  obtain ⟨a, b, rfl, _⟩ := List.eq_append_cons_of_mem hzero
  have hc : CyclicEq (a ++ 0 :: b) (0 :: (b ++ a)) := by
    have h := CyclicEq.of_rot (x := a ++ 0 :: b) (by simp) a.length
    simpa only [rot_append_length, List.cons_append] using h
  have hp : (b ++ a).Perm [1,2,3,4,5,6] :=
    (List.perm_cons 0).mp (hc.perm.symm.trans hx)
  exact ⟨0 :: (b ++ a), List.mem_map.mpr
    ⟨b ++ a, List.mem_permutations'.mpr hp, rfl⟩, hc.symm⟩

/-- The direct finite rotation pointers supply literal block completeness. -/
theorem accountingRows_complete : BlockComplete alphabet7 accountingRows := by
  intro x hx
  obtain ⟨b, hb, hbx⟩ := canonicalBases_complete hx
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hb
  let i : Fin 720 := ⟨j, by rwa [canonicalBases_length] at hj⟩
  refine ⟨canonicalWitness i, canonicalWitness_mem i, ?_⟩
  apply CyclicEq.trans _ hbx
  refine ⟨⟨(pointer i).2, ?_⟩, ?_⟩
  · have hl := (accountingRows_basedOn _ (canonicalWitness_mem i)).2.1.length_eq
    have hb := (pointer_bounds i).2
    change (canonicalWitness i).base.length = 7 at hl
    omega
  · exact canonicalWitness_rotation i

/-- The selected completion and the unused full charts are the exact family
whose literal trail decomposition is prescribed by the nine-symbol packing. -/
def rows : List (Row Nat) :=
  Completion.packingRows selectedRows 8 ++ unusedBases.flatMap (fun x => fullChart x 7 8)

private theorem fullChart_covers {r : Row Nat} (hr : r.Valid)
    {p : List Nat} (hp : p.Nodup) (h8p : 8 ∈ p)
    (h8 : 8 ∉ r.base) (hs : 8 ≠ r.satellite)
    (hb : InInsertionBlock r.satellite r.base (eraseSatellite 8 p)) :
    ∃ t ∈ fullChart r.base r.satellite 8, t.Assigned p := by
  obtain ⟨j, hc⟩ := hb
  refine ⟨fullChartAt r.base r.satellite 8 j.val,
    List.mem_map.mpr ⟨j.val, List.mem_range.mpr j.isLt, rfl⟩, ?_⟩
  apply (Row.assigned_iff_inInsertionBlock_of_full
    (fullChartAt_valid hr.1 hr.2.1 h8 hs j.val) ?_).mpr
  · exact inInsertionBlock_of_cyclicEq_eraseSatellite hp h8p hc
  · simp

/-- Coverage is obtained by deleting 8 and locating its old cyclic block,
including the full-chart case; it is not inferred from visible counts. -/
theorem rows_cover {p : List Nat} (hp : p.Perm (List.range 9)) :
    ∃ t ∈ rows, t.Assigned p := by
  have hp' : p.Perm (8 :: (alphabet7 ++ [7])) := hp.trans (by decide)
  have hpn : p.Nodup := hp.nodup_iff.mpr List.nodup_range
  have h8p : 8 ∈ p := hp.mem_iff.mpr (by decide)
  have hperm : p.Perm ((alphabet7 ++ [7]) ++ [8]) := hp.trans (by decide)
  have hdel := eraseSatellite_perm_of_perm_append_satellite hperm (by decide : 8 ∉ alphabet7 ++ [7])
  obtain ⟨x, hx, hb⟩ := exists_inInsertionBlock_of_perm_append_satellite
    (by decide : alphabet7.Nodup) (by decide : alphabet7 ≠ []) (by decide : 7 ∉ alphabet7) hdel
  obtain ⟨r, hr, hcyc⟩ := accountingRows_complete x hx
  have hbr := accountingRows_basedOn r hr
  have hb' : InInsertionBlock r.satellite r.base (eraseSatellite 8 p) := by
    rw [hbr.2.2.1]
    exact (InInsertionBlock.congr_base hcyc).mpr hb
  have hpr : p.Perm (8 :: (r.base ++ [r.satellite])) := by
    rw [hbr.2.2.1]
    exact hp'.trans ((hbr.2.1.symm.append_right [7]).cons 8)
  have h8r : 8 ∉ r.base := fun hm => (by decide : 8 ∉ alphabet7) (hbr.2.1.mem_iff.mp hm)
  have h8s : 8 ≠ r.satellite := by rw [hbr.2.2.1]; decide
  rcases List.mem_append.mp hr with hselected | hunused
  · obtain ⟨t, ht, ha⟩ := Completion.completeRows_cover_block_extensions hbr.1 h8r h8s hpr hb'
    exact ⟨t, List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr ⟨r, hselected, ht⟩)), ha⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hunused
    obtain ⟨t, ht, ha⟩ := fullChart_covers hbr.1 hpn h8p h8r h8s hb'
    exact ⟨t, List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨x, hx, ht⟩)), ha⟩

variable {α : Type}

/-- Variable-width literal overlaps, used by the finite cut recipe. -/
def joinWords (first : List α) : List (Nat × List α) → List α
  | [] => first
  | (h, next) :: rest => overlapJoin first (joinWords next rest) h

def JoinCompatible (first : List α) : List (Nat × List α) → Prop
  | [] => True
  | (h, next) :: rest => OverlapCompatible h first next ∧ JoinCompatible next rest

instance instDecidableJoinCompatible [DecidableEq α] (first : List α)
    (rest : List (Nat × List α)) : Decidable (JoinCompatible first rest) :=
  match rest with
  | [] => isTrue True.intro
  | (h,next) :: rest => by
    haveI := instDecidableJoinCompatible next rest
    unfold JoinCompatible OverlapCompatible
    infer_instance

theorem prefix_joinWords (first : List α) (rest : List (Nat × List α)) :
    first.IsPrefix (joinWords first rest) := by
  cases rest with
  | nil => exact List.prefix_refl _
  | cons q rest => exact prefix_overlapJoin _ _ _

theorem take_joinWords {first : List α} {k : Nat} (rest : List (Nat × List α))
    (hk : k ≤ first.length) : (joinWords first rest).take k = first.take k := by
  cases rest with
  | nil => rfl
  | cons q rest => exact take_overlapJoin hk

theorem joinWords_spec {first : List α} {rest : List (Nat × List α)}
    (hc : JoinCompatible first rest) :
    (joinWords first rest).length + (rest.map Prod.fst).sum =
      first.length + (rest.map (fun q => q.2.length)).sum ∧
    (∀ piece ∈ first :: rest.map Prod.snd, piece.IsInfix (joinWords first rest)) := by
  induction rest generalizing first with
  | nil =>
    constructor
    · simp [joinWords]
    · intro piece hp
      simp only [List.map_nil, List.mem_singleton] at hp
      subst piece
      exact List.infix_refl _
  | cons q rest ih =>
    rcases q with ⟨h,next⟩
    have hi := ih hc.2
    have hm : first.drop (first.length - h) = (joinWords next rest).take h := by
      rw [take_joinWords rest hc.1.2.1]
      exact hc.1.2.2
    have hlen : h ≤ (joinWords next rest).length :=
      hc.1.2.1.trans (prefix_joinWords next rest).length_le
    constructor
    · have hj := length_overlapJoin_add (u := first) hlen
      change (overlapJoin first (joinWords next rest) h).length + _ = _
      simp only [List.map_cons, List.sum_cons]
      omega
    · intro piece hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact infix_overlapJoin_left _ _ _
      · apply (hi.2 piece hp).trans
        exact infix_overlapJoin_right hm

theorem joinWords_support (first : List α) (rest : List (Nat × List α)) (P : α → Prop)
    (hs : ∀ a ∈ first, P a) (hr : ∀ q ∈ rest, ∀ a ∈ q.2, P a) :
    ∀ a ∈ joinWords first rest, P a := by
  induction rest generalizing first with
  | nil => exact hs
  | cons q rest ih =>
    intro a ha
    rcases mem_overlapJoin ha with hfirst | hrest
    · exact hs a hfirst
    · exact ih q.2 (hr q (by simp)) (fun r h => hr r (by simp [h])) a hrest

theorem last_compatible_of_loop (first last : Row α) (rest : List (Row α))
    (hc : RowTrailCompatible first (rest ++ [last])) : (rest.getLastD first).Compatible last := by
  induction rest generalizing first with
  | nil => exact hc.1
  | cons next rest ih =>
    simpa only [List.getLastD_cons] using ih next hc.2

def boundary (rs : List (Row α)) : List α := (rs.head?.map Row.head).getD []

theorem trailWord_boundary {K : Nat} {rs : List (Row α)} (hK : 4 ≤ K)
    (hc : ClosedTrail rs) (hv : ∀ r ∈ rs, 1 ≤ r.visible ∧ r.base.length + 1 = K) :
    (boundary rs).length = K - 3 ∧
    (boundary rs).IsPrefix (trailWord K rs) ∧ (boundary rs).IsSuffix (trailWord K rs) := by
  obtain ⟨first,rest,rfl⟩ := List.exists_cons_of_ne_nil hc.1
  have hf := hv first (by simp)
  have hl := hv (rest.getLastD first) List.getLastD_mem_cons
  have hwords := rowTrail_overlapCompatible hK (closedTrail_internal hc) hv
  have hloop : RowTrailCompatible first (rest ++ [first]) := by
    apply (Transport.rowTrailCompatible_loop_iff_zip first first rest).mpr
    have h := hc.2
    change ∀ pair ∈ (first :: rest).zip (rot (first :: rest) 1), _ at h
    rwa [Transport.rot_cons_one] at h
  have hend := last_compatible_of_loop first first rest hloop
  change first.head.length = K - 3 ∧ first.head.IsPrefix (rowTrailWord K first rest) ∧
    first.head.IsSuffix (rowTrailWord K first rest)
  refine ⟨?_, ?_, ?_⟩
  · simp only [Row.head, List.length_take]
    omega
  · exact first.head_prefix_word.trans (prefix_overlapTrail _ _ _)
  · have hs : (rest.getLastD first).word.IsSuffix (rowTrailWord K first rest) := by
      simpa only [rowTrailWord, List.getLastD_map] using suffix_overlapTrail hwords
    rw [← hend]
    exact ((rest.getLastD first).tail_suffix_word hl.1 (by omega)).trans hs

theorem overlap_of_boundaries {a b u v : List α} {h : Nat}
    (ha : a.IsSuffix u) (hb : b.IsPrefix v) (hah : h ≤ a.length) (hbh : h ≤ b.length)
    (hm : a.drop (a.length - h) = b.take h) : OverlapCompatible h u v := by
  refine ⟨hah.trans ha.length_le, hbh.trans hb.length_le, ?_⟩
  rw [drop_length_sub_of_suffix ha hah]
  obtain ⟨tail, rfl⟩ := hb
  rw [List.take_append_of_le_length hbh]
  exact hm

theorem joinCompatible_map {β : Type} (boundary spell : β → List α)
    (first : β) (rest : List (Nat × β))
    (hc : JoinCompatible (boundary first) (rest.map (fun q => (q.1, boundary q.2))))
    (hb : ∀ b ∈ first :: rest.map Prod.snd,
      (boundary b).IsPrefix (spell b) ∧ (boundary b).IsSuffix (spell b)) :
    JoinCompatible (spell first) (rest.map (fun q => (q.1, spell q.2))) := by
  induction rest generalizing first with
  | nil => trivial
  | cons q rest ih =>
    rcases q with ⟨h,next⟩
    have hf := hb first (by simp)
    have hn := hb next (by simp)
    refine ⟨overlap_of_boundaries hf.2 hn.1 hc.1.1 hc.1.2.1 hc.1.2.2, ?_⟩
    exact ih next hc.2 (fun b hm => hb b (List.mem_cons_of_mem _ hm))


theorem sum_lengths_pieces (first : List α) (rest : List (Nat × List α)) :
    ((first :: rest.map Prod.snd).map List.length).sum =
      first.length + (rest.map (fun q => q.2.length)).sum := by
  simp only [List.map_cons, List.sum_cons, List.map_map, Function.comp_def]

theorem sum_lengths_map {β : Type} (f : β → List α) (xs : List β) :
    ((xs.map f).map List.length).sum = (xs.map (fun x => (f x).length)).sum := by
  simp only [List.map_map, Function.comp_def]

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem recipeTrails_nonempty : recipeTrails ≠ [] := by
  intro h
  have hn := recipeTrails_count
  rw [h] at hn
  contradiction

def firstTrail : List (Row Nat) := recipeTrails.head recipeTrails_nonempty

def trailRest : List (Nat × List (Row Nat)) := overlaps.zip recipeTrails.tail

theorem overlaps_length : overlaps.length = 51 := by decide

theorem trailPieces : firstTrail :: trailRest.map Prod.snd = recipeTrails := by
  rw [trailRest, List.map_snd_zip (by simp [overlaps_length, recipeTrails_count])]
  exact List.cons_head_tail recipeTrails_nonempty

theorem trailRest_overlaps : (trailRest.map Prod.fst).sum = 145 := by
  rw [trailRest, List.map_fst_zip (by simp [overlaps_length, recipeTrails_count]), overlaps_sum]

theorem recipe_visible_size : ∀ r ∈ recipeTrails.flatten,
    1 ≤ r.visible ∧ r.base.length + 1 = 9 := by
  intro r hr
  have h := recipeTrails_valid r hr
  exact ⟨h.1.2.2.1, by omega⟩

def wordPlan : List (Nat × List Nat) := trailRest.map (fun q => (q.1, trailWord 9 q.2))

def firstWord : List Nat := trailWord 9 firstTrail

def naturalWord : List Nat := joinWords firstWord wordPlan

theorem recipe_boundary_compatible :
    JoinCompatible (boundary firstTrail) (trailRest.map (fun q => (q.1, boundary q.2))) := by decide

theorem wordPlan_compatible : JoinCompatible firstWord wordPlan := by
  unfold firstWord wordPlan
  apply joinCompatible_map boundary (trailWord 9) firstTrail trailRest recipe_boundary_compatible
  intro rs hrs
  rw [trailPieces] at hrs
  exact (trailWord_boundary (by decide : 4 ≤ 9) (recipeTrails_closed rs hrs)
    (fun r hr => recipe_visible_size r (List.mem_flatten.mpr ⟨rs, hrs, hr⟩))).2

theorem wordPieces : firstWord :: wordPlan.map Prod.snd = recipeTrails.map (trailWord 9) := by
  have h := congrArg (List.map (trailWord 9)) trailPieces
  simpa only [firstWord, wordPlan, List.map_cons, List.map_map, Function.comp_def] using h

theorem naturalWord_length : naturalWord.length = 408743 := by
  have hj := (joinWords_spec wordPlan_compatible).1
  have ho : (wordPlan.map Prod.fst).sum = 145 := by
    simpa only [wordPlan, List.map_map, Function.comp_def] using trailRest_overlaps
  have he : firstWord.length + (wordPlan.map (fun q => q.2.length)).sum =
      (recipeTrails.map (fun rs => (trailWord 9 rs).length)).sum := by
    calc
      _ = ((firstWord :: wordPlan.map Prod.snd).map List.length).sum :=
        (sum_lengths_pieces firstWord wordPlan).symm
      _ = ((recipeTrails.map (trailWord 9)).map List.length).sum :=
        congrArg (fun ws : List (List Nat) => (ws.map List.length).sum) wordPieces
      _ = _ := sum_lengths_map (trailWord 9) recipeTrails
  have hf := (familyWord_spec (by decide : 4 ≤ 9) recipeTrails_closed recipe_visible_size).1
  have hsum : (recipeTrails.map (fun rs => (trailWord 9 rs).length)).sum =
      (familyWord 9 recipeTrails).length := by
    simp only [familyWord, List.length_flatten, List.map_map, Function.comp_def]
  rw [hsum, hf, recipeTrails_visible, recipeTrails_row_count, recipeTrails_count] at he
  rw [ho] at hj
  change (joinWords firstWord wordPlan).length = _
  omega

theorem trailWord_support9 {rs : List (Row Nat)} (hrs : rs ∈ recipeTrails) :
    ∀ a ∈ trailWord 9 rs, a < 9 := by
  apply trailWord_support
  intro r hr a ha
  have h := recipeTrails_valid r (List.mem_flatten.mpr ⟨rs,hrs,hr⟩)
  rcases Row.mem_word_iff.mp ha with hb | rfl
  · exact h.2.2.2 a hb
  · exact h.2.2.1

theorem naturalWord_support : ∀ a ∈ naturalWord, a < 9 := by
  apply joinWords_support
  · apply trailWord_support9
    rw [← trailPieces]
    exact List.mem_cons_self
  · intro q hq
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hq
    apply trailWord_support9
    rw [← trailPieces]
    exact List.mem_cons_of_mem _ (List.mem_map_of_mem hr)

theorem naturalWord_covers : CoversPermutationsOf (List.range 9) naturalWord := by
  intro p hp
  obtain ⟨r,hr,ha⟩ := rows_cover hp
  change r ∈ completedFamily at hr
  have hm : r ∈ recipeTrails.flatten := recipeTrails_inventory.mem_iff.mpr hr
  obtain ⟨rs,hrs,hrr⟩ := List.mem_flatten.mp hm
  have hs := (trailWord_spec (by decide : 4 ≤ 9) (recipeTrails_closed rs hrs)
    (fun t ht => recipe_visible_size t (List.mem_flatten.mpr ⟨rs,hrs,ht⟩))).2 r hrr p ha
  apply hs.trans
  apply (joinWords_spec wordPlan_compatible).2
  rw [wordPieces]
  exact List.mem_map_of_mem hrs

def word : Word 9 := liftWord naturalWord naturalWord_support

theorem word_length : word.length = 408743 := by
  simpa only [word, liftWord_length] using naturalWord_length

theorem word_superpermutation : IsSuperpermutation word :=
  isSuperpermutation_liftWord_of_covers naturalWord naturalWord_support naturalWord_covers

theorem word9_408743 : HasSuperpermutationOfLengthAtMost 9 408743 :=
  ⟨word, word_superpermutation, word_length.le⟩

#print axioms naturalWord_length
#print axioms naturalWord_covers
#print axioms word9_408743

#print axioms accountingRows_complete
#print axioms rows_cover

end SuperpermutationUpperBound.Certificates.Word9
