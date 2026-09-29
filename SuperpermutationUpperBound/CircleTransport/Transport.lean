import SuperpermutationUpperBound.CircleTransport.Circles
import SuperpermutationUpperBound.CircleTransport.PairPaths
import SuperpermutationUpperBound.Transport.Winding

/-! Tagged boundary walks for circle-cover transport. All paths retain actual
row occurrences; equal literal tuples are never required to have equal tags. -/
namespace SuperpermutationUpperBound.CircleTransport

open Transport
variable {α : Type}

/-- Old completion labels move by decrement on full rows and increment on short rows. -/
def oldRowPerm (r : Row α) (h : Nat) (hh : 0 < h) : Equiv.Perm (Fin h) :=
  if r.visible = r.base.length then decrement h hh else rowIndexPerm h hh

/-- Composite port maps in the order of the listed source row occurrences. -/
def oldWalkPerm (h : Nat) (hh : 0 < h) : List (Row α) → Equiv.Perm (Fin h)
  | [] => Equiv.refl _
  | r :: rs => (oldRowPerm r h hh).trans (oldWalkPerm h hh rs)

def pairWalkPerm (h : Nat) (hh : 0 < h) : List (Row α) → Equiv.Perm (Fin h × Fin (h + 1))
  | [] => Equiv.refl _
  | r :: rs => (pairRowPerm r h hh).trans (pairWalkPerm h hh rs)

@[simp] theorem oldWalkPerm_nil (h : Nat) (hh : 0 < h) (p : Fin h) :
    oldWalkPerm (α := α) h hh [] p = p := rfl
@[simp] theorem pairWalkPerm_nil (h : Nat) (hh : 0 < h) (pq : Fin h × Fin (h + 1)) :
    pairWalkPerm (α := α) h hh [] pq = pq := rfl

/-- Deletion intertwines each actual full/short pair step with the old completion step. -/
theorem deleteLabel_pairRowPerm (r : Row α) (h : Nat) (hh : 0 < h)
    (pq : Fin h × Fin (h + 1)) :
    deleteLabel (pairRowPerm r h hh pq) = oldRowPerm r h hh (deleteLabel pq) := by
  by_cases hf : r.visible = r.base.length
  · simpa only [pairRowPerm, oldRowPerm, if_pos hf] using deleteLabel_twoInsertion h hh pq
  · simp only [pairRowPerm, oldRowPerm, if_neg hf]
    have he := deleteLabel_twoInsertion h hh ((twoInsertion h hh).symm pq)
    rw [Equiv.apply_symm_apply] at he
    have hs := congrArg (rowIndexPerm h hh) he
    simpa only [decrement, Equiv.apply_symm_apply] using hs.symm

theorem deleteLabel_pairWalkPerm (rs : List (Row α)) (h : Nat) (hh : 0 < h)
    (pq : Fin h × Fin (h + 1)) :
    deleteLabel (pairWalkPerm h hh rs pq) = oldWalkPerm h hh rs (deleteLabel pq) := by
  induction rs generalizing pq with
  | nil => rfl
  | cons r rs ih =>
    change deleteLabel (pairWalkPerm h hh rs (pairRowPerm r h hh pq)) = _
    rw [ih, deleteLabel_pairRowPerm]
    rfl

theorem pairChart_pairRowPerm (r : Row α) (h : Nat) (hh : 0 < h)
    (pq : Fin h × Fin (h + 1)) :
    pairChart h (pairRowPerm r h hh pq) =
      (oldRowPerm r h hh pq.1, (pairChart h pq).2) := by
  by_cases hf : r.visible = r.base.length
  · simpa only [pairRowPerm, oldRowPerm, if_pos hf] using pairChart_twoInsertion h hh pq
  · simp only [pairRowPerm, oldRowPerm, if_neg hf]
    apply Prod.ext
    · exact twoInsertion_symm_fst h hh pq
    · have he := congrArg Prod.snd (pairChart_twoInsertion h hh ((twoInsertion h hh).symm pq))
      simpa only [Equiv.apply_symm_apply] using he.symm

theorem pairChart_pairWalkPerm (rs : List (Row α)) (h : Nat) (hh : 0 < h)
    (pq : Fin h × Fin (h + 1)) :
    pairChart h (pairWalkPerm h hh rs pq) =
      (oldWalkPerm h hh rs pq.1, (pairChart h pq).2) := by
  induction rs generalizing pq with
  | nil => rfl
  | cons r rs ih =>
    change pairChart h (pairWalkPerm h hh rs (pairRowPerm r h hh pq)) = _
    rw [ih]
    have he := pairChart_pairRowPerm r h hh pq
    have hfst := congrArg Prod.fst he
    have hsnd := congrArg Prod.snd he
    simp only [pairChart_fst] at hfst
    rw [hfst, hsnd]
    rfl

/-- Identity old monodromy implies identity pair monodromy, with no condition
on distinctness of row or endpoint values. -/
theorem pairWalkPerm_eq_self_of_old (rs : List (Row α)) (h : Nat) (hh : 0 < h)
    (hold : ∀ p, oldWalkPerm h hh rs p = p) (pq : Fin h × Fin (h + 1)) :
    pairWalkPerm h hh rs pq = pq := by
  apply (pairChart h).injective
  rw [pairChart_pairWalkPerm, hold]
  rfl

/-- The clamped insertion agrees with `insertIdx` on a genuine linear gap. -/
theorem insertLetter_eq_insertIdx (u : List α) (a : α) (j : Nat) (hj : j ≤ u.length) :
    insertLetter u a j = u.insertIdx j a := by
  induction u generalizing j with
  | nil =>
    have hj0 : j = 0 := by simpa using hj
    subst j
    rfl
  | cons b u ih =>
    cases j with
    | zero => rfl
    | succ j =>
      rw [insertLetter_cons_succ, List.insertIdx_succ_cons, ih _ (by simpa using hj)]

/-- Swapping the order of the two literal insertions gives exactly the
delete-new-letter label, at every linear cut including both end cuts. -/
theorem double_insertLetter_swap (u : List α) (newOrd final : α) (p q : Nat)
    (hp : p ≤ u.length) (hq : q ≤ u.length + 1) :
    insertLetter (insertLetter u newOrd p) final q =
      insertLetter (insertLetter u final (q - if p < q then 1 else 0)) newOrd
        (p + if q ≤ p then 1 else 0) := by
  by_cases hpq : p < q
  · have hqp : ¬q ≤ p := by omega
    simp only [if_pos hpq, if_neg hqp, Nat.add_zero]
    have he : q = (q - 1) + 1 := by omega
    rw [insertLetter_eq_insertIdx _ _ _ (by simpa using hq),
      insertLetter_eq_insertIdx u newOrd p hp,
      insertLetter_eq_insertIdx _ _ _ (by simp; omega),
      insertLetter_eq_insertIdx u final (q - 1) (by omega), he]
    exact List.insertIdx_comm newOrd final (by omega) (by omega)
  · have hqp : q ≤ p := by omega
    simp only [if_neg hpq, if_pos hqp, Nat.sub_zero]
    rw [insertLetter_eq_insertIdx _ _ _ (by simpa using hq),
      insertLetter_eq_insertIdx u newOrd p hp,
      insertLetter_eq_insertIdx _ _ _ (by simp; omega),
      insertLetter_eq_insertIdx u final q (by omega)]
    exact (List.insertIdx_comm final newOrd hqp hp).symm

/-- A designated boundary occurrence in the completed old row walk. -/
def BoundaryVertex (rs : List (Row α)) (final : α) (h : Nat) (hh : 0 < h)
    (j : Fin h) (v : List α) : Prop :=
  ∃ pre r post, rs = pre ++ r :: post ∧
    v = insertLetter r.head final (oldWalkPerm h hh pre j).val

/-- The corresponding boundary occurrences in the literal double-insertion walk. -/
def PairBoundaryVertex (rs : List (Row α)) (newOrd final : α)
    (h : Nat) (hh : 0 < h) (pq : Fin h × Fin (h + 1)) (v : List α) : Prop :=
  ∃ pre r post, rs = pre ++ r :: post ∧
    v = insertLetter (insertLetter r.head newOrd (pairWalkPerm h hh pre pq).1.val)
      final (pairWalkPerm h hh pre pq).2.val

/-- Every descendant tag has a literal insertion extension of each boundary
occurrence of its deleted old tag. -/
theorem boundaryVertex_lifts (rs : List (Row α)) (newOrd final : α)
    (h : Nat) (hh : 0 < h) (hlen : ∀ r ∈ rs, r.base.length = h + 1)
    (pq : Fin h × Fin (h + 1)) (v : List α)
    (hv : BoundaryVertex rs final h hh (deleteLabel pq) v) :
    ∃ j, j ≤ v.length ∧ PairBoundaryVertex rs newOrd final h hh pq (insertLetter v newOrd j) := by
  obtain ⟨pre, r, post, he, rfl⟩ := hv
  have hr : r ∈ rs := by simp [he]
  have hrlen : r.head.length = h - 1 := by simp [Row.head, hlen r hr]; omega
  let pq' := pairWalkPerm h hh pre pq
  have hp : pq'.1.val ≤ r.head.length := by rw [hrlen]; exact Nat.le_pred_of_lt pq'.1.isLt
  have hq : pq'.2.val ≤ r.head.length + 1 := by rw [hrlen]; have := pq'.2.isLt; omega
  refine ⟨pq'.1.val + (if pq'.2.val ≤ pq'.1.val then 1 else 0), ?_, pre, r, post, he, ?_⟩
  · rw [insertLetter_length, hrlen]
    split <;> have := pq'.1.isLt <;> omega
  · have hswap := double_insertLetter_swap r.head newOrd final pq'.1.val pq'.2.val hp hq
    have hdel := congrArg Fin.val (deleteLabel_pairWalkPerm pre h hh pq)
    change (deleteLabel pq').val = _ at hdel
    change pq'.2.val - (if pq'.1.val < pq'.2.val then 1 else 0) = _ at hdel
    rw [hdel] at hswap
    exact hswap.symm

/-- Insertion of every selected circle transports coverage of tagged original
boundaries to coverage of every tagged pair-boundary descendant. -/
theorem boundary_circle_cover_transport (rs : List (Row α)) (newOrd final : α)
    (h : Nat) (hh : 0 < h) (hlen : ∀ r ∈ rs, r.base.length = h + 1)
    (circles : List (List α)) (hc : CoversDesignated circles (BoundaryVertex rs final h hh)) :
    CoversDesignated (extendCircles circles newOrd) (PairBoundaryVertex rs newOrd final h hh) :=
  hc.extend newOrd deleteLabel (boundaryVertex_lifts rs newOrd final h hh hlen)

theorem oldRowPerm_eq_shift (r : Row α) (h : Nat)
    (hbase : r.base.length = h + 2)
    (hkind : r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (p : Fin (h + 1)) : oldRowPerm r (h + 1) (by omega) p = shiftPort h (delta r) p := by
  by_cases hf : r.visible = r.base.length
  · have hd : delta r = -1 := delta_full (by simp [Row.charge, hf])
    simp only [oldRowPerm, if_pos hf, hd]
    apply Fin.ext
    rw [decrement_val, shiftPort_neg_one_val_cases]
    simp
  · have hs := hkind.resolve_left hf
    have hd : delta r = 1 := delta_short (by simp only [Row.charge]; omega)
    simp only [oldRowPerm, if_neg hf, hd]
    apply Fin.ext
    rw [rowIndexPerm_val, shiftPort_one_val]

theorem oldWalkPerm_eq_shift (rs : List (Row α)) (h : Nat)
    (hlen : ∀ r ∈ rs, r.base.length = h + 2)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (p : Fin (h + 1)) :
    oldWalkPerm (h + 1) (by omega) rs p = shiftPort h ((rs.map delta).sum) p := by
  induction rs generalizing p with
  | nil => simp
  | cons r rs ih =>
    change oldWalkPerm (h + 1) _ rs (oldRowPerm r (h + 1) _ p) = _
    rw [ih (fun r hr => hlen r (by simp [hr])) (fun r hr => hkind r (by simp [hr])),
      oldRowPerm_eq_shift r h (hlen r (by simp)) (hkind r (by simp)), shiftPort_add]
    simp

/-- The paper's signed winding divisibility gives identity combined monodromy. -/
theorem pairWalkPerm_eq_self_of_winding (rs : List (Row α)) (h : Nat) (hh : 0 < h)
    (hlen : ∀ r ∈ rs, r.base.length = h + 1)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (hw : (h : Int) ∣ signedExcess rs) (pq : Fin h × Fin (h + 1)) :
    pairWalkPerm h hh rs pq = pq := by
  apply pairWalkPerm_eq_self_of_old
  intro p
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hh)
  rw [oldWalkPerm_eq_shift rs k hlen hkind]
  apply (shiftPort_eq_self_iff k _ p).mpr
  rw [signedExcess_eq_neg_sum_delta] at hw
  exact dvd_neg.mp hw

/-- The actual descendant macro trail starting at a tagged pair port. -/
def pairTrail (h : Nat) (hh : 0 < h) (newOrd final : α) :
    List (Row α) → Fin h × Fin (h + 1) → List (Row α)
  | [], _ => []
  | r :: rs, pq => pairPath r newOrd final pq.1.val pq.2.val ++
      pairTrail h hh newOrd final rs (pairRowPerm r h hh pq)

theorem pairTrail_nonempty (rs : List (Row α)) (hne : rs ≠ [])
    (h : Nat) (hh : 0 < h) (newOrd final : α) (pq : Fin h × Fin (h + 1)) :
    pairTrail h hh newOrd final rs pq ≠ [] := by
  cases rs with
  | nil => exact False.elim (hne rfl)
  | cons r rs =>
    intro hn
    exact pairPath_nonempty r newOrd final pq.1.val pq.2.val (List.append_eq_nil_iff.mp hn).1

theorem pairTrail_append (pre post : List (Row α)) (h : Nat) (hh : 0 < h)
    (newOrd final : α) (pq : Fin h × Fin (h + 1)) :
    pairTrail h hh newOrd final (pre ++ post) pq =
      pairTrail h hh newOrd final pre pq ++
        pairTrail h hh newOrd final post (pairWalkPerm h hh pre pq) := by
  induction pre generalizing pq with
  | nil => rfl
  | cons r pre ih =>
    simp only [List.cons_append, pairTrail, ih, List.append_assoc]
    rfl

/-- Each tagged pair boundary is the head of an actual macro row occurrence. -/
theorem PairBoundaryVertex.mem_pairTrail {rs : List (Row α)} {newOrd final : α}
    {h : Nat} {hh : 0 < h} {pq : Fin h × Fin (h + 1)} {v : List α}
    (hv : PairBoundaryVertex rs newOrd final h hh pq v) (hn : 3 ≤ h + 1)
    (hlen : ∀ r ∈ rs, r.base.length = h + 1)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2) :
    ∃ r ∈ pairTrail h hh newOrd final rs pq, r.head = v := by
  obtain ⟨pre, r, post, he, rfl⟩ := hv
  have hr : r ∈ rs := by simp [he]
  let pq' := pairWalkPerm h hh pre pq
  refine ⟨(pairPath r newOrd final pq'.1.val pq'.2.val).head (pairPath_nonempty _ _ _ _ _), ?_, ?_⟩
  · rw [he, pairTrail_append, pairTrail]
    apply List.mem_append_right
    apply List.mem_append_left
    exact List.head_mem _
  · exact (pairPath_literal_endpoints r newOrd final h hn (hlen r hr) (hkind r hr) pq').1

/-- Compatible source rows give compatible actual pair paths at the propagated pair port. -/
theorem pairPath_boundary {r next : Row α} (hc : r.Compatible next)
    (newOrd final : α) (h : Nat) (hn : 3 ≤ h + 1)
    (hr : r.base.length = h + 1) (hrn : next.base.length = h + 1)
    (hkr : r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (hkn : next.visible = next.base.length ∨ next.visible = next.base.length - 2)
    (pq : Fin h × Fin (h + 1)) :
    ((pairPath r newOrd final pq.1.val pq.2.val).getLast (pairPath_nonempty _ _ _ _ _)).Compatible
      ((pairPath next newOrd final (pairRowPerm r h (by omega) pq).1.val
        (pairRowPerm r h (by omega) pq).2.val).head (pairPath_nonempty _ _ _ _ _)) := by
  change _ = _
  rw [(pairPath_literal_endpoints r newOrd final h hn hr hkr pq).2,
    (pairPath_literal_endpoints next newOrd final h hn hrn hkn _).1, hc]

theorem pairTrail_runsTo (rs : List (Row α)) (last : Row α)
    (hc : PathRunsTo rs last) (newOrd final : α) (h : Nat) (hn : 3 ≤ h + 1)
    (hlen : ∀ r ∈ rs ++ [last], r.base.length = h + 1)
    (hkind : ∀ r ∈ rs ++ [last], r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (pq : Fin h × Fin (h + 1)) :
    PathRunsTo (pairTrail h (by omega) newOrd final rs pq)
      ((pairPath last newOrd final (pairWalkPerm h (by omega) rs pq).1.val
        (pairWalkPerm h (by omega) rs pq).2.val).head (pairPath_nonempty _ _ _ _ _)) := by
  induction rs generalizing pq with
  | nil => exact False.elim hc
  | cons r rs ih =>
    have hri := pairPath_internal r newOrd final (h + 1) pq.1.val pq.2.val hn
      (hlen r (by simp)) (hkind r (by simp)) pq.2.isLt
    cases rs with
    | nil =>
      change PathRunsTo (pairPath r newOrd final pq.1.val pq.2.val ++ []) _
      rw [List.append_nil]
      apply pathRunsTo_of_path_spec _ _ (pairPath_nonempty _ _ _ _ _) hri
      exact pairPath_boundary hc.1 newOrd final h hn (hlen r (by simp))
        (hlen last (by simp)) (hkind r (by simp)) (hkind last (by simp)) pq
    | cons a rs =>
      have hi := ih hc.2 (fun b hb => hlen b (by simp only [List.cons_append, List.mem_cons] at *; tauto))
        (fun b hb => hkind b (by simp only [List.cons_append, List.mem_cons] at *; tauto))
        (pairRowPerm r h (by omega) pq)
      have hb := pairPath_boundary hc.1 newOrd final h hn (hlen r (by simp))
        (hlen a (by simp)) (hkind r (by simp)) (hkind a (by simp)) pq
      have hl := pathRunsTo_of_path_spec _ _ (pairPath_nonempty r newOrd final pq.1.val pq.2.val) hri hb
      have hne := pairTrail_nonempty (a :: rs) (by simp) h (by omega) newOrd final
        (pairRowPerm r h (by omega) pq)
      have hh : (pairTrail h (by omega) newOrd final (a :: rs)
          (pairRowPerm r h (by omega) pq)).head hne =
          (pairPath a newOrd final (pairRowPerm r h (by omega) pq).1.val
            (pairRowPerm r h (by omega) pq).2.val).head (pairPath_nonempty _ _ _ _ _) := by
        simp only [pairTrail, List.head_append_of_ne_nil (pairPath_nonempty _ _ _ _ _)]
      rw [← hh] at hl
      obtain ⟨b, bs, he⟩ := List.exists_cons_of_ne_nil hne
      have hl' := hl
      simp only [he, List.head_cons] at hl'
      rw [he] at hi
      change PathRunsTo (pairPath r newOrd final pq.1.val pq.2.val ++ _) _
      rw [he]
      exact pathRunsTo_append hl' hi

/-- Under winding divisibility every initial pair port gives one literal
closed macro trail, even when several such trails share actual endpoint tuples. -/
theorem pairTrail_closedTrail {rs : List (Row α)} (hc : ClosedTrail rs)
    (newOrd final : α) (h : Nat) (hn : 3 ≤ h + 1)
    (hlen : ∀ r ∈ rs, r.base.length = h + 1)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (hw : (h : Int) ∣ signedExcess rs) (pq : Fin h × Fin (h + 1)) :
    ClosedTrail (pairTrail h (by omega) newOrd final rs pq) := by
  obtain ⟨r, rest, he⟩ := List.exists_cons_of_ne_nil hc.1
  have hruns : PathRunsTo rs r := by
    rw [he]
    apply (rowTrailCompatible_loop_iff_zip r r rest).mpr
    have hz := hc.2
    simpa only [CyclicallyCompatible, he, rot_cons_one] using hz
  have ht := pairTrail_runsTo rs r hruns newOrd final h hn
    (fun a ha => hlen a (by simp only [he, List.mem_append, List.mem_cons] at *; tauto))
    (fun a ha => hkind a (by simp only [he, List.mem_append, List.mem_cons] at *; tauto)) pq
  rw [pairWalkPerm_eq_self_of_winding rs h (by omega) hlen hkind hw pq] at ht
  have hne := pairTrail_nonempty rs hc.1 h (by omega) newOrd final pq
  have hh : (pairTrail h (by omega) newOrd final rs pq).head hne =
      (pairPath r newOrd final pq.1.val pq.2.val).head (pairPath_nonempty _ _ _ _ _) := by
    simp only [he, pairTrail, List.head_append_of_ne_nil (pairPath_nonempty _ _ _ _ _)]
  rw [← hh] at ht
  obtain ⟨a, as, hea⟩ := List.exists_cons_of_ne_nil hne
  simp only [hea, List.head_cons] at ht
  rw [hea]
  exact closedTrail_of_pathRunsTo ht

/-- Canonical complete list of pair-port occurrence labels. -/
def pairLabels (h : Nat) : List (Fin h × Fin (h + 1)) :=
  (List.finRange h).product (List.finRange (h + 1))

@[simp] theorem pairLabels_length (h : Nat) : (pairLabels h).length = h * (h + 1) := by
  simp [pairLabels, List.product]

theorem pairLabels_map_perm (h : Nat) (σ : Equiv.Perm (Fin h × Fin (h + 1))) :
    ((pairLabels h).map σ).Perm (pairLabels h) := by
  have hnodup : (pairLabels h).Nodup := (nodup_finRange h).product (nodup_finRange (h + 1))
  apply perm_of_nodup_subset_length (hnodup.map σ.injective)
  · intro pq _
    exact List.mem_product.mpr ⟨List.mem_finRange _, List.mem_finRange _⟩
  · simp

/-- All initial pair labels together use every transported-then-completed row
occurrence exactly once. This excludes hidden extra internal cycles. -/
theorem pairTrail_inventory (rs : List (Row α)) (newOrd final : α)
    (h : Nat) (hn : 3 ≤ h + 1)
    (hlen : ∀ r ∈ rs, r.base.length = h + 1)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2) :
    ((pairLabels h).flatMap (pairTrail h (by omega) newOrd final rs)).Perm
      ((Transport.packingRows rs newOrd).flatMap (fun r => Completion.completeRows r final)) := by
  induction rs with
  | nil => simp [pairTrail, Transport.packingRows]
  | cons r rs ih =>
    have ht := ih (fun r hr => hlen r (List.mem_cons_of_mem _ hr))
      (fun r hr => hkind r (List.mem_cons_of_mem _ hr))
    have hreindex := (pairLabels_map_perm h (pairRowPerm r h (by omega))).flatMap_right
      (pairTrail h (by omega) newOrd final rs)
    simp only [List.flatMap_map] at hreindex
    have hlocal := pairPath_product_inventory r newOrd final (h + 1) hn
      (hlen r (by simp)) (hkind r (by simp))
    change ((pairLabels h).flatMap (fun pq =>
      pairPath r newOrd final pq.1.val pq.2.val ++
        pairTrail h (by omega) newOrd final rs (pairRowPerm r h (by omega) pq))).Perm _
    rw [Transport.packingRows, List.flatMap_cons, List.flatMap_append]
    exact (List.flatMap_append_perm _ _ _).symm.trans
      (hlocal.append (hreindex.trans ht))

/-- A concrete designated cover by all h(h+1) returning pair walks, with exact
row-occurrence inventory; each old completion label has h+1 descendants. -/
theorem pairTrail_assembly {rs : List (Row α)} (hc : ClosedTrail rs)
    (newOrd final : α) (h : Nat) (hn : 3 ≤ h + 1)
    (hlen : ∀ r ∈ rs, r.base.length = h + 1)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (hw : (h : Int) ∣ signedExcess rs) :
    let trails := (pairLabels h).map (pairTrail h (by omega) newOrd final rs)
    (∀ t ∈ trails, ClosedTrail t) ∧
    trails.flatten.Perm ((Transport.packingRows rs newOrd).flatMap
      (fun r => Completion.completeRows r final)) ∧ trails.length = h * (h + 1) := by
  refine ⟨?_, pairTrail_inventory rs newOrd final h hn hlen hkind, ?_⟩
  · intro t ht
    obtain ⟨pq, _, rfl⟩ := List.mem_map.mp ht
    exact pairTrail_closedTrail hc newOrd final h hn hlen hkind hw pq
  · simp

/-- Swap insertion order in the occurrence labels. Its first coordinate is
exactly the deletion label and its second is the new letter's linear gap. -/
def deletionChartFun (h : Nat) (pq : Fin h × Fin (h + 1)) : Fin h × Fin (h + 1) :=
  (deleteLabel pq, ⟨pq.1.val + (if pq.2.val ≤ pq.1.val then 1 else 0), by
    split <;> have := pq.1.isLt <;> omega⟩)

theorem deletionChartFun_involutive (h : Nat) : Function.Involutive (deletionChartFun h) := by
  intro pq
  apply Prod.ext <;> apply Fin.ext <;>
    simp only [deletionChartFun, deleteLabel_val] <;>
    split_ifs <;> omega

def deletionChart (h : Nat) : Equiv.Perm (Fin h × Fin (h + 1)) :=
  ⟨deletionChartFun h, deletionChartFun h, deletionChartFun_involutive h,
    deletionChartFun_involutive h⟩

@[simp] theorem deletionChart_fst (h : Nat) (pq : Fin h × Fin (h + 1)) :
    (deletionChart h pq).1 = deleteLabel pq := rfl

/-- An explicit bijection between one old label's descendant tags and all h+1
linear insertion gaps. It uses no uniqueness of actual endpoint tuples. -/
def descendantEquiv (h : Nat) (j : Fin h) :
    Fin (h + 1) ≃ {pq : Fin h × Fin (h + 1) // deleteLabel pq = j} where
  toFun k := ⟨(deletionChart h).symm (j, k), by
    change (deletionChart h ((deletionChart h).symm (j, k))).1 = j
    rw [Equiv.apply_symm_apply]⟩
  invFun pq := (deletionChart h pq.val).2
  left_inv k := by
    change (deletionChart h ((deletionChart h).symm (j, k))).2 = k
    rw [Equiv.apply_symm_apply]
  right_inv pq := by
    apply Subtype.ext
    apply (deletionChart h).injective
    rw [Equiv.apply_symm_apply]
    apply Prod.ext
    · exact pq.property.symm
    · rfl

theorem descendant_count (h : Nat) (j : Fin h) :
    Fintype.card {pq : Fin h × Fin (h + 1) // deleteLabel pq = j} = h + 1 := by
  rw [← Fintype.card_congr (descendantEquiv h j), Fintype.card_fin]

/-- The occurrence-coordinate bijection is literally the two-insertion swap. -/
theorem descendant_literal_vertex (u : List α) (newOrd final : α)
    (h : Nat) (hu : u.length + 1 = h) (j : Fin h) (k : Fin (h + 1)) :
    let pq := (descendantEquiv h j k).val
    insertLetter (insertLetter u newOrd pq.1.val) final pq.2.val =
      insertLetter (insertLetter u final j.val) newOrd k.val := by
  dsimp only
  let pq := (descendantEquiv h j k).val
  have hp : pq.1.val ≤ u.length := by have := pq.1.isLt; omega
  have hq : pq.2.val ≤ u.length + 1 := by have := pq.2.isLt; omega
  have he := double_insertLetter_swap u newOrd final pq.1.val pq.2.val hp hq
  have hc : deletionChart h pq = (j, k) := (deletionChart h).apply_symm_apply (j, k)
  have hf := congrArg (fun t : Fin h × Fin (h + 1) => t.1.val) hc
  have hs := congrArg (fun t : Fin h × Fin (h + 1) => t.2.val) hc
  change pq.2.val - (if pq.1.val < pq.2.val then 1 else 0) = j.val at hf
  change pq.1.val + (if pq.2.val ≤ pq.1.val then 1 else 0) = k.val at hs
  rw [hf, hs] at he
  exact he

theorem take_insertLetter_at_gap (u : List α) (z : α) (j : Nat) (hj : j ≤ u.length) :
    (insertLetter u z j).take j = u.take j := by
  have ht : j ≤ (u.take j).length := by simp [List.length_take_of_le hj]
  simp only [insertLetter, List.append_assoc, List.take_append_of_le_length ht,
    List.take_take, Nat.min_self]

/-- Every completion macro head containing the final letter is an original
insertion boundary. Heads internal to the exceptional paths contain no final letter. -/
theorem completion_portPath_head_contains {r t : Row α} (final : α) (j : Nat)
    (hn : 3 ≤ r.base.length)
    (hkind : r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (hj : j < r.base.length - 1) (hfresh : final ∉ r.base)
    (ht : t ∈ Completion.portPath r final j) (hz : final ∈ t.head) :
    t.head = insertLetter r.head final j := by
  have hfirst := Completion.portPath_head final hn hkind hj
  by_cases hf : r.visible = r.base.length
  · simp only [Completion.portPath, if_pos hf, fullPathAt] at ht hfirst
    by_cases hj0 : j = 0
    · subst j
      simp only [if_true, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · simpa using hfirst
      · have he : (fullAt r final (r.base.length - 1)).head =
            r.base.take (r.base.length - 1) := by
          simp only [Row.head, fullAt, insertLetter_length]
          rw [show r.base.length + 1 - 2 = r.base.length - 1 by omega,
            take_insertLetter_at_gap _ _ _ (by omega)]
        rw [he] at hz
        exact False.elim (hfresh (List.mem_of_mem_take hz))
    · simp only [if_neg hj0, List.mem_singleton] at ht
      subst t
      simpa only [if_neg hj0, List.head_cons] using hfirst
  · have hs := hkind.resolve_left hf
    simp only [Completion.portPath, if_neg hf, Completion.shortPathAt] at ht hfirst
    by_cases hjshort : j < r.base.length - 2
    · simp only [if_pos hjshort, List.mem_singleton] at ht
      subst t
      simpa only [if_pos hjshort, List.head_cons] using hfirst
    · have hjlast : j = r.base.length - 2 := by omega
      subst j
      have he := Completion.short_exceptional_endpoints final hn hs
      simp only [Nat.lt_irrefl, if_false, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · simpa only [Nat.lt_irrefl, if_false, List.head_cons] using hfirst
      · rw [Completion.repairRow_head] at hz
        exact False.elim (hfresh ((rot_perm _ _).mem_iff.mp (List.mem_of_mem_take hz)))
      · rw [Completion.repairRow_head] at hz
        exact False.elim (hfresh ((rot_perm _ _).mem_iff.mp (List.mem_of_mem_take hz)))
      · have hh : (Completion.liftRow r final (r.base.length - 1)).head =
            r.base.take (r.base.length - 1) := by
          rw [← he.2.2.2.1, Completion.repairRow_final_tail r final (by omega)]
        rw [hh] at hz
        exact False.elim (hfresh (List.mem_of_mem_take hz))

theorem oldRowPerm_val_portTarget (r : Row α) (h : Nat) (hn : 3 ≤ h + 1)
    (hbase : r.base.length = h + 1)
    (hkind : r.visible = r.base.length ∨ r.visible = r.base.length - 2) (j : Fin h) :
    (oldRowPerm r h (by omega) j).val = portTarget r j.val := by
  rcases hkind with hf | hs
  · simpa only [oldRowPerm, if_pos hf] using (full_pair_first r h hn hbase hf j).symm
  · have hf : r.visible ≠ r.base.length := by omega
    simpa only [oldRowPerm, if_neg hf] using (short_pair_first r h hn hbase hs j).symm

theorem completionExit_eq_oldWalk (rs : List (Row α)) (h : Nat) (hn : 3 ≤ h + 1)
    (hlen : ∀ r ∈ rs, r.base.length = h + 1)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2) (j : Fin h) :
    completionExit rs j.val = (oldWalkPerm h (by omega) rs j).val := by
  induction rs generalizing j with
  | nil => rfl
  | cons r rs ih =>
    rw [completionExit, ← oldRowPerm_val_portTarget r h hn (hlen r (by simp)) (hkind r (by simp))]
    exact ih (fun r hr => hlen r (by simp [hr])) (fun r hr => hkind r (by simp [hr])) _

theorem completionWalk_append (pre post : List (Row α)) (final : α) (j : Nat) :
    completionWalk (pre ++ post) final j = completionWalk pre final j ++
      completionWalk post final (completionExit pre j) := by
  induction pre generalizing j with
  | nil => rfl
  | cons r pre ih => simp only [List.cons_append, completionWalk, completionExit, ih, List.append_assoc]

/-- Old original-boundary tags also refer to literal macro row heads. -/
theorem BoundaryVertex.mem_completionWalk {rs : List (Row α)} {final : α}
    {h : Nat} {hh : 0 < h} {j : Fin h} {v : List α}
    (hv : BoundaryVertex rs final h hh j v) (hn : 3 ≤ h + 1)
    (hlen : ∀ r ∈ rs, r.base.length = h + 1)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2) :
    ∃ r ∈ completionWalk rs final j.val, r.head = v := by
  obtain ⟨pre, r, post, he, rfl⟩ := hv
  have hr : r ∈ rs := by simp [he]
  have hpre : ∀ a ∈ pre, a ∈ rs := fun a ha => by simp [he, ha]
  have hexit := completionExit_eq_oldWalk pre h hn
    (fun a ha => hlen a (hpre a ha)) (fun a ha => hkind a (hpre a ha)) j
  let j' := oldWalkPerm h hh pre j
  refine ⟨(Completion.portPath r final j'.val).head (Completion.portPath_nonempty _ _ _), ?_, ?_⟩
  · rw [he, completionWalk_append, hexit, completionWalk]
    exact List.mem_append_right _ (List.mem_append_left _ (List.head_mem _))
  · exact Completion.portPath_head final (by rw [hlen r hr]; exact hn) (hkind r hr)
      (by rw [hlen r hr]; exact j'.isLt)

/-- A final-letter-containing macro head in an actual designated old trail
has an original boundary occurrence with the same tag and literal tuple. -/
theorem completionWalk_head_contains_boundary (rs : List (Row α)) (final : α)
    (h : Nat) (hn : 3 ≤ h + 1)
    (hlen : ∀ r ∈ rs, r.base.length = h + 1)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (hfresh : ∀ r ∈ rs, final ∉ r.base) (j : Fin h) {t : Row α}
    (ht : t ∈ completionWalk rs final j.val) (hz : final ∈ t.head) :
    BoundaryVertex rs final h (by omega) j t.head := by
  induction rs generalizing j with
  | nil => simp [completionWalk] at ht
  | cons r rs ih =>
    have hr := hlen r (by simp)
    have hk := hkind r (by simp)
    rw [completionWalk] at ht
    rcases List.mem_append.mp ht with ht | ht
    · have he := completion_portPath_head_contains final j.val (by omega) hk (by omega)
        (hfresh r (by simp)) ht hz
      exact ⟨[], r, rs, rfl, he⟩
    · rw [← oldRowPerm_val_portTarget r h hn hr hk] at ht
      obtain ⟨pre, a, post, he, hv⟩ := ih (fun a ha => hlen a (by simp [ha]))
        (fun a ha => hkind a (by simp [ha])) (fun a ha => hfresh a (by simp [ha]))
        (oldRowPerm r h (by omega) j) ht
      exact ⟨r :: pre, a, post, by simp [he], hv⟩

/-- Incidence at a literal macro head. For a closed trail this also includes
all macro tails, by the compatibility edge to the next row occurrence. -/
def HeadVertex (trail : List (Row α)) (v : List α) : Prop :=
  ∃ r ∈ trail, r.head = v

/-- The general final-letter circle step refers only to actual completed
macro occurrences in its hypotheses and actual descendant occurrences in its conclusion. -/
theorem final_circle_cover_transport (rs : List (Row α)) (newOrd final : α)
    (h : Nat) (hn : 3 ≤ h + 1)
    (hlen : ∀ r ∈ rs, r.base.length = h + 1)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (hfresh : ∀ r ∈ rs, final ∉ r.base) (circles : List (List α))
    (hcontains : ∀ c ∈ circles, final ∈ c)
    (hc : CoversDesignated circles (fun j : Fin h => HeadVertex (completionWalk rs final j.val))) :
    CoversDesignated (extendCircles circles newOrd)
      (fun pq => HeadVertex (pairTrail h (by omega) newOrd final rs pq)) := by
  have hboundary : CoversDesignated circles (BoundaryVertex rs final h (by omega)) := by
    intro j
    obtain ⟨c, hcm, v, ⟨r, hr, hv⟩, hcv⟩ := hc j
    have hz : final ∈ r.head := by
      rw [hv]
      exact hcv.perm.mem_iff.mp (hcontains c hcm)
    refine ⟨c, hcm, v, ?_, hcv⟩
    rw [← hv]
    exact completionWalk_head_contains_boundary rs final h hn hlen hkind hfresh j hr hz
  have he := boundary_circle_cover_transport rs newOrd final h (by omega) hlen circles hboundary
  intro pq
  obtain ⟨c, hm, v, hv, hcv⟩ := he pq
  exact ⟨c, hm, v, hv.mem_pairTrail hn hlen hkind, hcv⟩

theorem completion_port_zero_internal_head (r : Row α) (final : α)
    (hf : r.visible = r.base.length) :
    fullAt r final (r.base.length - 1) ∈ Completion.portPath r final 0 ∧
      (fullAt r final (r.base.length - 1)).head = r.base.take (r.base.length - 1) := by
  constructor
  · simp [Completion.portPath, hf, fullPathAt]
  · simp only [Row.head, fullAt, insertLetter_length]
    rw [show r.base.length + 1 - 2 = r.base.length - 1 by omega,
      take_insertLetter_at_gap _ _ _ (by omega)]

/-- At deletion label zero, a full-row pair path traverses a completion path
at port zero. The doubled transport branch covers the p=0,q=1 boundary case. -/
theorem full_pairPath_contains_zero_completion (r : Row α) (newOrd final : α)
    (h : Nat) (hh : 0 < h) (hbase : r.base.length = h + 1)
    (hf : r.visible = r.base.length) (pq : Fin h × Fin (h + 1))
    (hz : (deleteLabel pq).val = 0) :
    ∃ j, j ≤ h ∧ ∀ t ∈ Completion.portPath (fullAt r newOrd j) final 0,
      t ∈ pairPath r newOrd final pq.1.val pq.2.val := by
  have hz' : pq.2.val = 0 ∨ pq.1.val = 0 ∧ pq.2.val = 1 := by
    simp only [deleteLabel_val] at hz
    split_ifs at hz <;> omega
  rcases hz' with hq | ⟨hp, hq⟩
  · refine ⟨pq.1.val, Nat.le_of_lt pq.1.isLt, ?_⟩
    intro t ht
    by_cases hp : pq.1.val = 0
    · simp only [pairPath, Transport.portPath, if_pos hf, fullPathAt, hp,
        if_true, completionWalk, hq]
      exact List.mem_append_left _ (by simpa only [hp] using ht)
    · simp only [pairPath, Transport.portPath, if_pos hf, fullPathAt, if_neg hp,
        completionWalk, hq, List.append_nil]
      exact ht
  · refine ⟨h, Nat.le_refl _, ?_⟩
    intro t ht
    have htgt : portTarget (fullAt r newOrd 0) 1 = 0 := by
      simp only [portTarget, fullAt, insertLetter_length, hbase]
      rw [show h + 1 + 1 - 2 = h by omega, show h + 1 + 1 - 1 = h + 1 by omega,
        Nat.add_comm 1 h, Nat.mod_self]
      simp
    have he : r.base.length - 1 = h := by omega
    simp only [pairPath, Transport.portPath, if_pos hf, fullPathAt, hp, if_true,
      completionWalk, hq, htgt, he, List.append_nil]
    exact List.mem_append_right _ ht

/-- An ordinary full-chart circle covers every local pair path at deleted
label zero by one of its cyclic-gap extension circles. -/
theorem fullChartAt_pairPath_circle (circle : List α) (active satellite newOrd final : α)
    (hh : 0 < circle.length) (i : Nat) (pq : Fin circle.length × Fin (circle.length + 1))
    (hz : (deleteLabel pq).val = 0) :
    ∃ c ∈ circleExtensions circle newOrd, ∃ t ∈ pairPath
      (Partition.fullChartAt circle active satellite i) newOrd final pq.1.val pq.2.val,
      CircleVertex c t.head := by
  let r := Partition.fullChartAt circle active satellite i
  obtain ⟨j, hj, hmem⟩ := full_pairPath_contains_zero_completion r newOrd final circle.length hh
    (by simp [r]) (by simp [r]) pq hz
  let t := fullAt (fullAt r newOrd j) final ((fullAt r newOrd j).base.length - 1)
  have hf : (fullAt r newOrd j).visible = (fullAt r newOrd j).base.length := by simp [fullAt]
  have ht := completion_port_zero_internal_head (fullAt r newOrd j) final hf
  have hh' : t.head = insertLetter (rot circle i) newOrd j := by
    rw [show t.head = (fullAt r newOrd j).base.take ((fullAt r newOrd j).base.length - 1) from ht.2]
    simp only [fullAt, insertLetter_length, Nat.add_sub_cancel]
    simp only [r, Partition.fullChartAt, List.length_append, rot_length, List.length_singleton]
    rw [insertLetter_append_of_le _ _ _ _ (by simpa using hj)]
    have hl : circle.length + 1 = (insertLetter (rot circle i) newOrd j).length := by simp
    rw [hl, List.take_append_length]
  obtain ⟨c, hc, hcv⟩ := circleVertex_insertLetter
    (CyclicEq.of_rot (List.length_pos_iff.mp hh) i) newOrd (by simpa using hj)
  exact ⟨c, hc, t, hmem t ht.1, hh' ▸ hcv⟩

/-- On an all-full prefix, the actual pair port is the corresponding iterate of T. -/
theorem pairWalkPerm_full (rs : List (Row α)) (h : Nat) (hh : 0 < h)
    (hf : ∀ r ∈ rs, r.visible = r.base.length) (pq : Fin h × Fin (h + 1)) :
    pairWalkPerm h hh rs pq = (twoInsertion h hh : _ → _)^[rs.length] pq := by
  induction rs generalizing pq with
  | nil => rfl
  | cons r rs ih =>
    change pairWalkPerm h hh rs (pairRowPerm r h hh pq) = _
    rw [ih (fun r hr => hf r (by simp [hr]))]
    simp only [pairRowPerm, if_pos (hf r (by simp)), List.length_cons, Function.iterate_succ_apply]

/-- Ordinary full-chart circles transport separately: their h cyclic-gap
extensions meet every one of the actual h(h+1) pair trails of the chart. -/
theorem fullChart_pairTrail_circle_cover (circle : List α) (active satellite newOrd final : α)
    (hh : 0 < circle.length) :
    CoversDesignated (circleExtensions circle newOrd)
      (fun pq => HeadVertex (pairTrail circle.length hh newOrd final
        (Partition.fullChart circle active satellite) pq)) := by
  intro pq
  obtain ⟨i, hi, hzero⟩ := twoInsertion_orbit_meets_deleteLabel circle.length hh pq ⟨0, hh⟩
  let rs := Partition.fullChart circle active satellite
  have hil : i < rs.length := by simpa [rs] using hi
  have he : rs = rs.take i ++ (Partition.fullChartAt circle active satellite i) :: rs.drop (i + 1) := by
    have hd := List.take_append_drop i rs
    rw [List.drop_eq_getElem_cons hil] at hd
    have hg : rs[i] = Partition.fullChartAt circle active satellite i := by
      simp [rs, Partition.fullChart]
    simpa only [hg] using hd.symm
  have hfull : ∀ r ∈ rs.take i, r.visible = r.base.length := by
    intro r hr
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp (List.mem_of_mem_take hr)
    simp [Partition.fullChartAt]
  have hp : pairWalkPerm circle.length hh (rs.take i) pq =
      (twoInsertion circle.length hh : _ → _)^[i] pq := by
    rw [pairWalkPerm_full _ _ _ hfull, List.length_take_of_le (Nat.le_of_lt hil)]
  obtain ⟨c, hc, t, ht, hcv⟩ := fullChartAt_pairPath_circle circle active satellite newOrd final hh i
    (pairWalkPerm circle.length hh (rs.take i) pq) (by rw [hp, hzero])
  refine ⟨c, hc, t.head, ⟨t, ?_, rfl⟩, hcv⟩
  change t ∈ pairTrail circle.length hh newOrd final rs pq
  rw [he, pairTrail_append, pairTrail]
  exact List.mem_append_right _ (List.mem_append_left _ ht)

/-- The finite checker records actual final-letter incidence or the literal
full-chart source of an ordinary circle. Representative changes remain explicit. -/
def SafeIncidence {h : Nat} (rs : List (Row α)) (final : α) (j : Fin h)
    (circle : List α) : Prop :=
  (final ∈ circle ∧ ∃ v, HeadVertex (completionWalk rs final j.val) v ∧ CircleVertex circle v) ∨
    ∃ x active satellite, CircleVertex circle x ∧ rs = Partition.fullChart x active satellite

def SafeCircleCover {ι : Type} (family : ι → List (Row α)) (final : α) (h : Nat)
    (circles : List (List α)) : Prop :=
  ∀ i (j : Fin h), ∃ c ∈ circles, SafeIncidence (family i) final j c

/-- The two allowed circle types give a literal cover of all tagged new
macro trails. A selected occurrence contributes exactly h new circle occurrences. -/
theorem safe_circle_cover_transport {ι : Type} (family : ι → List (Row α))
    (newOrd final : α) (h : Nat) (hn : 3 ≤ h + 1) (circles : List (List α))
    (hvalid : CircleFamilyValid h circles)
    (hlen : ∀ i r, r ∈ family i → r.base.length = h + 1)
    (hkind : ∀ i r, r ∈ family i → r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (hfresh : ∀ i r, r ∈ family i → final ∉ r.base)
    (hcover : SafeCircleCover family final h circles) :
    CoversDesignated (extendCircles circles newOrd)
      (fun ipq : ι × (Fin h × Fin (h + 1)) =>
        HeadVertex (pairTrail h (by omega) newOrd final (family ipq.1) ipq.2)) := by
  intro ⟨i, pq⟩
  obtain ⟨c, hc, hs⟩ := hcover i (deleteLabel pq)
  rcases hs with ⟨hz, v, ⟨r, hr, hv⟩, hcv⟩ | ⟨x, active, satellite, hcx, he⟩
  · have hzv : final ∈ r.head := by rw [hv]; exact hcv.perm.mem_iff.mp hz
    have hb := completionWalk_head_contains_boundary (family i) final h hn (hlen i) (hkind i)
      (hfresh i) (deleteLabel pq) hr hzv
    obtain ⟨j, hj, hbj⟩ := boundaryVertex_lifts (family i) newOrd final h (by omega) (hlen i)
      pq r.head hb
    obtain ⟨d, hd, hdv⟩ := circleVertex_insertLetter (hv ▸ hcv) newOrd hj
    exact ⟨d, List.mem_flatMap.mpr ⟨c, hc, hd⟩, _, hbj.mem_pairTrail hn (hlen i) (hkind i), hdv⟩
  · have hxl : x.length = h := hcx.length_eq.symm.trans (hvalid c hc).1
    subst h
    obtain ⟨d, hd, v, hv, hdv⟩ := fullChart_pairTrail_circle_cover x active satellite newOrd final
      (by omega) pq
    obtain ⟨d', hd', hdv'⟩ := (circleExtensions_congr hcx newOrd).mpr ⟨d, hd, hdv⟩
    exact ⟨d', List.mem_flatMap.mpr ⟨c, hc, hd'⟩, v, by simpa only [he] using hv, hdv'⟩

/-- Circle count and validity accompanying the literal mixed-cover transfer. -/
theorem safe_circle_cover_step {ι : Type} (family : ι → List (Row α))
    (newOrd final : α) (h : Nat) (hn : 3 ≤ h + 1) (circles : List (List α))
    (hvalid : CircleFamilyValid h circles) (hw : ∀ c ∈ circles, newOrd ∉ c)
    (hlen : ∀ i r, r ∈ family i → r.base.length = h + 1)
    (hkind : ∀ i r, r ∈ family i → r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (hfresh : ∀ i r, r ∈ family i → final ∉ r.base)
    (hcover : SafeCircleCover family final h circles) :
    CircleFamilyValid (h + 1) (extendCircles circles newOrd) ∧
    (extendCircles circles newOrd).length = h * circles.length ∧
    CoversDesignated (extendCircles circles newOrd)
      (fun ipq : ι × (Fin h × Fin (h + 1)) =>
        HeadVertex (pairTrail h (by omega) newOrd final (family ipq.1) ipq.2)) :=
  ⟨hvalid.extend newOrd hw, extendCircles_length h circles newOrd (fun c hc => (hvalid c hc).1),
    safe_circle_cover_transport family newOrd final h hn circles hvalid hlen hkind hfresh hcover⟩

/-- For closed trails tail incidence can always use the next head occurrence,
without identifying the two row labels. -/
theorem closedTrail_tail_headVertex {rs : List (Row α)} (hc : ClosedTrail rs)
    {r : Row α} (hr : r ∈ rs) : HeadVertex rs r.tail := by
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hr
  have hb := closedTrail_getElem_compatible hc ⟨i, hi⟩
  refine ⟨rs[(i + 1) % rs.length]'(Nat.mod_lt _ (by omega)), List.getElem_mem _, ?_⟩
  exact hb.symm.trans (congrArg Row.tail he)

/-- The ordinary circle of a full chart already meets every actual designated
completion trail, so the ordinary-source branch of SafeIncidence is semantic. -/
theorem fullChart_completion_circle_cover (circle : List α) (active satellite final : α)
    (hn : 3 ≤ circle.length + 1) :
    CoversDesignated [circle] (fun j : Fin circle.length =>
      HeadVertex (completionWalk (Partition.fullChart circle active satellite) final j.val)) := by
  intro j
  have hh : 0 < circle.length := by omega
  let pq := (descendantEquiv circle.length j ⟨0, by omega⟩).val
  have hd : deleteLabel pq = j := (descendantEquiv circle.length j ⟨0, by omega⟩).property
  obtain ⟨i, hi, hzero⟩ := twoInsertion_orbit_meets_deleteLabel circle.length hh pq ⟨0, hh⟩
  let rs := Partition.fullChart circle active satellite
  have hil : i < rs.length := by simpa [rs] using hi
  have he : rs = rs.take i ++ (Partition.fullChartAt circle active satellite i) :: rs.drop (i + 1) := by
    have hd := List.take_append_drop i rs
    rw [List.drop_eq_getElem_cons hil] at hd
    have hg : rs[i] = Partition.fullChartAt circle active satellite i := by
      simp [rs, Partition.fullChart]
    simpa only [hg] using hd.symm
  have hfull : ∀ r ∈ rs.take i, r.visible = r.base.length := by
    intro r hr
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp (List.mem_of_mem_take hr)
    simp [Partition.fullChartAt]
  have hlen : ∀ r ∈ rs.take i, r.base.length = circle.length + 1 := by
    intro r hr
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp (List.mem_of_mem_take hr)
    simp [Partition.fullChartAt]
  have hp : pairWalkPerm circle.length hh (rs.take i) pq =
      (twoInsertion circle.length hh : _ → _)^[i] pq := by
    rw [pairWalkPerm_full _ _ _ hfull, List.length_take_of_le (Nat.le_of_lt hil)]
  have hold := deleteLabel_pairWalkPerm (rs.take i) circle.length hh pq
  rw [hd, hp, hzero] at hold
  have hzero' : (oldWalkPerm circle.length hh (rs.take i) j).val = 0 :=
    (congrArg Fin.val hold).symm
  have hexit : completionExit (rs.take i) j.val = 0 := by
    rw [completionExit_eq_oldWalk (rs.take i) circle.length hn hlen
      (fun r hr => Or.inl (hfull r hr)), hzero']
  let r := Partition.fullChartAt circle active satellite i
  let t := fullAt r final (r.base.length - 1)
  have ht := completion_port_zero_internal_head r final (by simp [r])
  have hh' : t.head = rot circle i := by
    rw [show t.head = r.base.take (r.base.length - 1) from ht.2]
    simp only [r, Partition.fullChartAt, List.length_append, rot_length,
      List.length_singleton, Nat.add_sub_cancel]
    have he : circle.length = (rot circle i).length := by simp
    rw [he, List.take_append_length]
  refine ⟨circle, by simp, t.head, ⟨t, ?_, rfl⟩, ?_⟩
  · change t ∈ completionWalk rs final j.val
    rw [he, completionWalk_append, hexit, completionWalk]
    exact List.mem_append_right _ (List.mem_append_left _ ht.1)
  · rw [hh']
    exact CyclicEq.of_rot (List.length_pos_iff.mp hh) i

/-- Both finite-checker alternatives imply the original actual macro-head
cover, independently of the transport proof. -/
theorem SafeCircleCover.sound {ι : Type} {family : ι → List (Row α)} {final : α}
    {h : Nat} {circles : List (List α)} (hc : SafeCircleCover family final h circles)
    (hv : CircleFamilyValid h circles) (hn : 3 ≤ h + 1) :
    CoversDesignated circles (fun ij : ι × Fin h =>
      HeadVertex (completionWalk (family ij.1) final ij.2.val)) := by
  intro ⟨i, j⟩
  obtain ⟨c, hcm, hs⟩ := hc i j
  rcases hs with ⟨_, v, hv, hcv⟩ | ⟨x, active, satellite, hcx, he⟩
  · exact ⟨c, hcm, v, hv, hcv⟩
  · have hxl : x.length = h := hcx.length_eq.symm.trans (hv c hcm).1
    subst h
    obtain ⟨d, hd, v, hv, hdv⟩ := fullChart_completion_circle_cover x active satellite final hn j
    have hdx : d = x := List.mem_singleton.mp hd
    subst d
    exact ⟨c, hcm, v, by simpa only [he] using hv, hcx.trans hdv⟩

end SuperpermutationUpperBound.CircleTransport
