import SuperpermutationUpperBound.CircleTransport.Transport

/-! Literal single-lap transport tracks and the interfaces needed to iterate
circle covers. The track order is the prescribed local insertion-path order. -/
namespace SuperpermutationUpperBound.CircleTransport

open Transport
variable {α : Type}

/-- One source-row lap at an initial transport port, without regrouping or rotating rows. -/
def transportWalk (rs : List (Row α)) (newOrd : α) (p : Nat) : List (Row α) :=
  match rs with
  | [] => []
  | r :: rest => Transport.portPath r newOrd p ++
      transportWalk rest newOrd (portTarget r p)

@[simp] theorem pairRowPerm_fst (r : Row α) (h : Nat) (hh : 0 < h)
    (pq : Fin h × Fin (h + 1)) :
    (pairRowPerm r h hh pq).1 = oldRowPerm r h hh pq.1 := by
  by_cases hf : r.visible = r.base.length
  · simp [pairRowPerm, oldRowPerm, hf]
  · simp [pairRowPerm, oldRowPerm, hf]

theorem pairRowPerm_snd_val_completionExit (r : Row α) (newOrd : α) (h : Nat)
    (hn : 3 ≤ h + 1) (hbase : r.base.length = h + 1)
    (hkind : r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (pq : Fin h × Fin (h + 1)) :
    (pairRowPerm r h (by omega) pq).2.val =
      completionExit (Transport.portPath r newOrd pq.1.val) pq.2.val := by
  rcases hkind with hf | hs
  · simpa only [pairRowPerm, if_pos hf, twoInsertion_snd] using
      (full_pair_second r newOrd h hn hbase hf pq).symm
  · have hf : r.visible ≠ r.base.length := by omega
    simpa only [pairRowPerm, if_neg hf, twoInsertion_symm_snd] using
      (short_pair_second r newOrd h hn hbase hs pq).symm

/-- The pair path construction is literally completion along one actual
transport track, with all intermediate macro rows in the same order. -/
theorem pairTrail_eq_completionWalk_transportWalk (rs : List (Row α))
    (newOrd final : α) (h : Nat) (hn : 3 ≤ h + 1)
    (hlen : ∀ r ∈ rs, r.base.length = h + 1)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (pq : Fin h × Fin (h + 1)) :
    pairTrail h (by omega) newOrd final rs pq =
      completionWalk (transportWalk rs newOrd pq.1.val) final pq.2.val := by
  induction rs generalizing pq with
  | nil => rfl
  | cons r rs ih =>
    rw [pairTrail, transportWalk, completionWalk_append,
      ih (fun r hr => hlen r (by simp [hr])) (fun r hr => hkind r (by simp [hr]))]
    have hr := hlen r (by simp)
    have hk := hkind r (by simp)
    rw [pairRowPerm_fst, oldRowPerm_val_portTarget r h hn hr hk,
      pairRowPerm_snd_val_completionExit r newOrd h hn hr hk]
    rfl

/-- A literal ordered initial segment of a full chart. -/
def chartSegment (circle : List α) (active satellite : α) : Nat → List (Row α)
  | 0 => []
  | k + 1 => ⟨circle ++ [active], satellite, circle.length + 1⟩ ::
      chartSegment (rot circle 1) active satellite k

@[simp] theorem chartSegment_length (circle : List α) (active satellite : α) (k : Nat) :
    (chartSegment circle active satellite k).length = k := by
  induction k generalizing circle with
  | zero => rfl
  | succ k ih => simp [chartSegment, ih]

theorem chartSegment_eq_range (circle : List α) (active satellite : α) (k : Nat) :
    chartSegment circle active satellite k =
      (List.range k).map (Partition.fullChartAt circle active satellite) := by
  induction k generalizing circle with
  | zero => rfl
  | succ k ih =>
    rw [chartSegment, ih, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Partition.fullChartAt, rot_zero]
    congr 1
    apply List.map_congr_left
    intro j _
    simp [Partition.fullChartAt, rot_add, Nat.add_comm]

theorem fullChart_eq_chartSegment (circle : List α) (active satellite : α) :
    Partition.fullChart circle active satellite = chartSegment circle active satellite circle.length :=
  (chartSegment_eq_range circle active satellite circle.length).symm

theorem rot_cons_one_generic (a : α) (x : List α) : rot (a :: x) 1 = x ++ [a] := by
  rw [rot_eq_drop_append_take_of_le _ _ (by simp)]
  simp

/-- Rotating past an ordinary symbol shifts a later insertion gap down by one. -/
theorem rot_insertLetter_one_pos (x : List α) (newOrd : α) (p : Nat)
    (hp : 0 < p) (hpn : p ≤ x.length) :
    rot (insertLetter x newOrd p) 1 = insertLetter (rot x 1) newOrd (p - 1) := by
  cases x with
  | nil => simp at hpn; omega
  | cons a x =>
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
    rw [insertLetter_cons_succ, rot_cons_one_generic, rot_cons_one_generic,
      Nat.succ_sub_one, insertLetter_append_of_le _ _ _ _ (by simpa using hpn)]

/-- The doubled zero-port branch advances two positions in the new circle. -/
theorem rot_insertLetter_zero_two (x : List α) (newOrd : α) (hx : 0 < x.length) :
    rot (insertLetter x newOrd 0) 2 = insertLetter (rot x 1) newOrd (x.length - 1) := by
  cases x with
  | nil => simp at hx
  | cons a x =>
    simp only [insertLetter, List.take_zero, List.nil_append, List.drop_zero,
      List.singleton_append, List.length_cons, Nat.add_sub_cancel]
    rw [show (2 : Nat) = 1 + 1 by rfl, ← rot_add, rot_cons_one_generic]
    rw [rot_cons_one_generic]
    change rot (a :: (x ++ [newOrd])) 1 = _
    rw [rot_cons_one_generic]
    simp [List.append_assoc]

/-- Insertion before the fixed active last letter preserves the literal chart-row form. -/
theorem fullAt_chartRow (x : List α) (active satellite newOrd : α) (p : Nat)
    (hp : p ≤ x.length) :
    fullAt (Row.mk (x ++ [active]) satellite (x.length + 1)) newOrd p =
      Row.mk (insertLetter x newOrd p ++ [active]) satellite (x.length + 2) := by
  simp only [fullAt, insertLetter_append_of_le x [active] newOrd p hp,
    List.length_append, List.length_singleton]

theorem transportWalk_chartSegment_succ (x : List α) (active satellite newOrd : α)
    (k p : Nat) (hx : 2 ≤ x.length) (hp : p < x.length) :
    transportWalk (chartSegment x active satellite (k + 1)) newOrd p =
      if p = 0 then
        Row.mk (insertLetter x newOrd 0 ++ [active]) satellite (x.length + 2) ::
        Row.mk (insertLetter x newOrd x.length ++ [active]) satellite (x.length + 2) ::
          transportWalk (chartSegment (rot x 1) active satellite k) newOrd (x.length - 1)
      else
        Row.mk (insertLetter x newOrd p ++ [active]) satellite (x.length + 2) ::
          transportWalk (chartSegment (rot x 1) active satellite k) newOrd (p - 1) := by
  let r := Row.mk (x ++ [active]) satellite (x.length + 1)
  have hr : r.visible = r.base.length := by simp [r]
  have hlen : r.base.length = x.length + 1 := by simp [r]
  change Transport.portPath r newOrd p ++
    transportWalk (chartSegment (rot x 1) active satellite k) newOrd (portTarget r p) = _
  by_cases hp0 : p = 0
  · subst p
    rw [portTarget_full_zero (by omega) hr, hlen]
    have he : x.length + 1 - 2 = x.length - 1 := by omega
    simp only [Transport.portPath, fullPathAt, if_true, hlen, Nat.add_sub_cancel, he]
    rw [fullAt_chartRow x active satellite newOrd 0 (by omega),
      fullAt_chartRow x active satellite newOrd x.length (by omega)]
    simp [r]
  · rw [portTarget_full_pos (by omega) hr (by omega) (by omega)]
    simp only [Transport.portPath, if_pos hr, fullPathAt, if_neg hp0,
      List.cons_append, List.nil_append]
    rw [fullAt_chartRow x active satellite newOrd p (Nat.le_of_lt hp)]

/-- Every initial chart segment transports to the corresponding initial segment
of the literal insertion chart; precisely one extra row appears after the cut. -/
theorem transportWalk_chartSegment (x : List α) (active satellite newOrd : α)
    (k p : Nat) (hx : 2 ≤ x.length) (hk : k ≤ x.length) (hp : p < x.length) :
    transportWalk (chartSegment x active satellite k) newOrd p =
      chartSegment (insertLetter x newOrd p) active satellite (k + if p < k then 1 else 0) := by
  induction k generalizing x p with
  | zero => simp [chartSegment, transportWalk]
  | succ k ih =>
    rw [transportWalk_chartSegment_succ x active satellite newOrd k p hx hp]
    by_cases hp0 : p = 0
    · subst p
      simp only [if_true, Nat.zero_lt_succ]
      have hk' : k ≤ (rot x 1).length := by simp; omega
      have hp' : x.length - 1 < (rot x 1).length := by simp; omega
      have hi := ih (rot x 1) (x.length - 1) (by simpa using hx) hk' hp'
      have hnot : ¬x.length - 1 < k := by omega
      rw [if_neg hnot, Nat.add_zero] at hi
      rw [hi]
      have hrot1 : rot (insertLetter x newOrd 0) 1 = x ++ [newOrd] := by
        change rot (newOrd :: x) 1 = _
        exact rot_cons_one_generic _ _
      have hrot2 := rot_insertLetter_zero_two x newOrd (by omega)
      rw [show k.succ + 1 = k + 1 + 1 by omega, chartSegment, chartSegment]
      simp only [insertLetter_length, rot_length]
      rw [← hrot2, ← rot_add (insertLetter x newOrd 0) 1 1, hrot1, insertLetter_at_length]
    · have hp0' : 0 < p := by omega
      have hi := ih (rot x 1) (p - 1) (by simpa using hx)
        (by simp; omega) (by simp; omega)
      rw [if_neg hp0, hi]
      have hcount : k.succ + (if p < k.succ then 1 else 0) =
          (k + (if p - 1 < k then 1 else 0)) + 1 := by split_ifs <;> omega
      rw [hcount, chartSegment, ← rot_insertLetter_one_pos x newOrd p hp0' (Nat.le_of_lt hp)]
      simp only [insertLetter_length]

/-- A full chart transports to a full chart on the literal insertion base.
This is equality of ordered row lists, not merely a cyclic or multiset correspondence. -/
theorem transportWalk_fullChart (circle : List α) (active satellite newOrd : α)
    (hh : 2 ≤ circle.length) (p : Nat) (hp : p < circle.length) :
    transportWalk (Partition.fullChart circle active satellite) newOrd p =
      Partition.fullChart (insertLetter circle newOrd p) active satellite := by
  rw [fullChart_eq_chartSegment, transportWalk_chartSegment _ _ _ _ _ _ hh (Nat.le_refl _) hp,
    if_pos hp, fullChart_eq_chartSegment, insertLetter_length]

/-- The semantic mixed-cover predicate is preserved by the actual single-lap
transport family. This is the all-size induction step, with fixed satellite
and completion letters and an arbitrary fresh new ordinary letter. -/
theorem SafeCircleCover.transport {ι : Type} (family : ι → List (Row α))
    (newOrd final : α) (h : Nat) (hn : 3 ≤ h + 1) (circles : List (List α))
    (hvalid : CircleFamilyValid h circles)
    (hlen : ∀ i r, r ∈ family i → r.base.length = h + 1)
    (hkind : ∀ i r, r ∈ family i → r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (hfresh : ∀ i r, r ∈ family i → final ∉ r.base)
    (hcover : SafeCircleCover family final h circles) :
    SafeCircleCover (fun ip : ι × Fin h => transportWalk (family ip.1) newOrd ip.2.val)
      final (h + 1) (extendCircles circles newOrd) := by
  intro ⟨i, p⟩ q
  obtain ⟨c, hc, hs⟩ := hcover i (deleteLabel (p, q))
  rcases hs with ⟨hz, v, ⟨r, hr, hv⟩, hcv⟩ | ⟨x, active, satellite, hcx, he⟩
  · have hzv : final ∈ r.head := by rw [hv]; exact hcv.perm.mem_iff.mp hz
    have hb := completionWalk_head_contains_boundary (family i) final h hn (hlen i) (hkind i)
      (hfresh i) (deleteLabel (p, q)) hr hzv
    obtain ⟨j, hj, hbj⟩ := boundaryVertex_lifts (family i) newOrd final h (by omega) (hlen i)
      (p, q) r.head hb
    obtain ⟨d, hd, hdv⟩ := circleVertex_insertLetter (hv ▸ hcv) newOrd hj
    refine ⟨d, List.mem_flatMap.mpr ⟨c, hc, hd⟩, Or.inl ⟨?_, _, ?_, hdv⟩⟩
    · exact (fullBases_perm hd).mem_iff.mpr (List.mem_cons_of_mem _ hz)
    · have hm := hbj.mem_pairTrail hn (hlen i) (hkind i)
      rw [pairTrail_eq_completionWalk_transportWalk _ _ _ h hn (hlen i) (hkind i)] at hm
      exact hm
  · have hxl : x.length = h := hcx.length_eq.symm.trans (hvalid c hc).1
    have hp : p.val ≤ x.length := by omega
    obtain ⟨d, hd, hdv⟩ := circleVertex_insertLetter hcx newOrd hp
    refine ⟨d, List.mem_flatMap.mpr ⟨c, hc, hd⟩,
      Or.inr ⟨insertLetter x newOrd p.val, active, satellite, hdv, ?_⟩⟩
    change transportWalk (family i) newOrd p.val = _
    rw [he, transportWalk_fullChart x active satellite newOrd (by omega) p.val (by omega)]

/-- Exact circle-count growth accompanies preservation of the semantic cover. -/
theorem safeCircleCover_transport_step {ι : Type} (family : ι → List (Row α))
    (newOrd final : α) (h : Nat) (hn : 3 ≤ h + 1) (circles : List (List α))
    (hvalid : CircleFamilyValid h circles) (hw : ∀ c ∈ circles, newOrd ∉ c)
    (hlen : ∀ i r, r ∈ family i → r.base.length = h + 1)
    (hkind : ∀ i r, r ∈ family i → r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (hfresh : ∀ i r, r ∈ family i → final ∉ r.base)
    (hcover : SafeCircleCover family final h circles) :
    CircleFamilyValid (h + 1) (extendCircles circles newOrd) ∧
    (extendCircles circles newOrd).length = h * circles.length ∧
    SafeCircleCover (fun ip : ι × Fin h => transportWalk (family ip.1) newOrd ip.2.val)
      final (h + 1) (extendCircles circles newOrd) :=
  ⟨hvalid.extend newOrd hw, extendCircles_length h circles newOrd (fun c hc => (hvalid c hc).1),
    hcover.transport family newOrd final h hn circles hvalid hlen hkind hfresh⟩

end SuperpermutationUpperBound.CircleTransport
