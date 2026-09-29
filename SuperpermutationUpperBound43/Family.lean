import SuperpermutationUpperBound.CircleTransport.Iterated
import SuperpermutationUpperBound.Assembly.RowEdges
import SuperpermutationUpperBound.Foundation.SupportedWords

/-! Transport and completion for an independently certified degree-nine base.
The row inventory is a parameter; no equality with the historical rows is used. -/
namespace SuperpermutationUpperBound43.Family

open SuperpermutationUpperBound
open SuperpermutationUpperBound.Partition
open SuperpermutationUpperBound.CircleTransport
open SuperpermutationUpperBound.Transport

/-- The finite semantic data needed for the 43/80 construction. Labels and
their enumeration retain component occurrences, including equal row values. -/
structure Base (I0 : Type) where
  baseRows : List (Row Nat)
  baseLabels : List I0
  baseFamily : I0 → List (Row Nat)
  baseCircles : List (List Nat)
  labels_complete : ∀ i, i ∈ baseLabels
  labels_nodup : baseLabels.Nodup
  inventory : (baseLabels.flatMap baseFamily).Perm baseRows
  basedOn : BasedOn SprintBase.alphabet9 9 baseRows
  complete : BlockComplete SprintBase.alphabet9 baseRows
  row_count : baseRows.length = 40320
  charge : (baseRows.map Row.charge).sum = 18816
  closed : ∀ i, ClosedTrail (baseFamily i)
  winding : ∀ i, (8 : Int) ∣ signedExcess (baseFamily i)
  circles_valid : CircleFamilyValid 8 baseCircles
  circles_support : Iterated.CircleSupport 0 baseCircles
  circle_count : baseCircles.length = 357
  safe_cover : SafeCircleCover baseFamily 10 8 baseCircles

variable {I0 : Type} (B : Base I0)

abbrev Index (I0 : Type) (k : Nat) := Iterated.Index I0 k

def rows : Nat → List (Row Nat)
  | 0 => B.baseRows
  | k + 1 => Transport.packingRows (rows k) (k + 11)

def labels (k : Nat) : List (Index I0 k) := Iterated.labels B.baseLabels k

def family (k : Nat) : Index I0 k → List (Row Nat) :=
  Iterated.family B.baseFamily k

def completedRows (k : Nat) : List (Row Nat) := Completion.packingRows (rows B k) 10

def completedFamily (k : Nat) : Index I0 (k + 1) → List (Row Nat) :=
  Iterated.completedFamily B.baseFamily k

def circles (k : Nat) : List (List Nat) := Iterated.circles B.baseCircles k

def selectedCircleCount (k : Nat) : Nat := Iterated.circleCount 357 k

theorem rows_basedOn (k : Nat) : BasedOn (SprintFamily.alphabet k) 9 (rows B k) := by
  induction k with
  | zero => exact B.basedOn
  | succ k ih => exact ih.transport (SprintFamily.alphabet_fresh k) (by omega)

theorem rows_complete (k : Nat) : BlockComplete (SprintFamily.alphabet k) (rows B k) := by
  induction k with
  | zero => exact B.complete
  | succ k ih =>
    exact ih.transport (rows_basedOn B k) (SprintFamily.alphabet_nodup k)
      (SprintFamily.alphabet_nonempty k) (SprintFamily.alphabet_fresh k)

theorem rows_distinct (hd : DistinctBlocks B.baseRows) (k : Nat) :
    DistinctBlocks (rows B k) := by
  induction k with
  | zero => exact hd
  | succ k ih => exact ih.transport (rows_basedOn B k) (SprintFamily.alphabet_fresh k)

theorem rows_length (k : Nat) : (rows B k).length = (k + 8).factorial := by
  induction k with
  | zero => exact B.row_count
  | succ k ih =>
    have hc := Transport.packingRows_length (rows B k) (k + 11) (SprintFamily.alphabet k).length
      ((rows_basedOn B k).ready (SprintFamily.alphabet_fresh k) (by omega))
    change (Transport.packingRows (rows B k) (k + 11)).length = _
    rw [hc, SprintFamily.alphabet_length, ih]
    exact (Nat.factorial_succ (k + 8)).symm

theorem rows_chargeRatio (k : Nat) : ChargeRatio 7 15 (rows B k) := by
  induction k with
  | zero =>
    change ChargeRatio 7 15 B.baseRows
    unfold ChargeRatio
    rw [B.row_count, B.charge]
  | succ k ih =>
    exact chargeRatio_transport (rows_basedOn B k) (SprintFamily.alphabet_fresh k)
      (by omega : k + 11 ≠ 9) ih

theorem rows_charge (k : Nat) : 15 * ((rows B k).map Row.charge).sum = 7 * (k + 8).factorial := by
  simpa only [ChargeRatio, rows_length] using rows_chargeRatio B k

theorem labels_complete (k : Nat) (i : Index I0 k) : i ∈ labels B k :=
  Iterated.labels_complete _ B.labels_complete k i

theorem labels_nodup (k : Nat) : (labels B k).Nodup :=
  Iterated.labels_nodup B.labels_nodup k

theorem labels_perm_univ [Fintype I0] (k : Nat) :
    (labels B k).Perm Finset.univ.toList := by
  classical
  apply (List.perm_ext_iff_of_nodup (labels_nodup B k) (Finset.nodup_toList _)).mpr
  intro i
  simp only [labels_complete B k i, Finset.mem_toList, Finset.mem_univ]

/-- Transport preserves the actual new row inventory as a list permutation. -/
theorem family_inventory (k : Nat) :
    ((labels B k).flatMap (family B k)).Perm (rows B k) := by
  induction k with
  | zero => exact B.inventory
  | succ k ih =>
    have hlen : ∀ i (r : Row Nat), r ∈ family B k i → r.base.length = (k + 8) + 1 := by
      intro i r hr
      have hm : r ∈ rows B k := ih.mem_iff.mp
        (List.mem_flatMap.mpr ⟨i, labels_complete B k i, hr⟩)
      exact (rows_basedOn B k r hm).2.1.length_eq.trans (SprintFamily.alphabet_length k)
    have hp : ((labels B k).flatMap (fun i =>
        (List.finRange (k + 8)).flatMap (fun p => transportWalk (family B k i) (k + 11) p.val))).Perm
        ((labels B k).flatMap (fun i => Transport.packingRows (family B k i) (k + 11))) := by
      apply flatMap_perm_of_pointwise
      intro i _
      exact transportWalk_inventory _ _ (k + 8) (by omega) (hlen i)
    have hi := ih.flatMap_right (fun r => Transport.rows r (k + 11))
    change ((labels B (k + 1)).flatMap (family B (k + 1))).Perm
      (Transport.packingRows (rows B k) (k + 11))
    have he : ((labels B (k + 1)).flatMap (family B (k + 1))) =
        (labels B k).flatMap (fun i => (List.finRange (k + 8)).flatMap
          (fun p => transportWalk (family B k i) (k + 11) p.val)) := by
      change ((labels B k).product (List.finRange (k + 8))).flatMap
        (fun ip : Index I0 k × Fin (k + 8) => transportWalk (family B k ip.1) (k + 11) ip.2.val) = _
      rw [List.product, List.flatMap_assoc]
      simp only [List.flatMap_map]
    rw [he]
    apply hp.trans
    simpa only [Transport.packingRows, List.flatMap_assoc] using hi

theorem family_univ_inventory [Fintype I0] (k : Nat) :
    ((Finset.univ.toList : List (Index I0 k)).flatMap (family B k)).Perm (rows B k) :=
  ((labels_perm_univ B k).symm.flatMap_right (family B k)).trans (family_inventory B k)

theorem family_basedOn (k : Nat) (i : Index I0 k) :
    BasedOn (SprintFamily.alphabet k) 9 (family B k i) := by
  intro r hr
  apply rows_basedOn B k r
  exact (family_inventory B k).mem_iff.mp
    (List.mem_flatMap.mpr ⟨i, labels_complete B k i, hr⟩)

theorem family_length (k : Nat) (i : Index I0 k) (r : Row Nat) (hr : r ∈ family B k i) :
    r.base.length = k + 9 :=
  (family_basedOn B k i r hr).2.1.length_eq.trans (SprintFamily.alphabet_length k)

theorem family_kind (k : Nat) (i : Index I0 k) (r : Row Nat) (hr : r ∈ family B k i) :
    r.visible = r.base.length ∨ r.visible = r.base.length - 2 :=
  (family_basedOn B k i r hr).2.2.2

theorem family_final_fresh (k : Nat) (i : Index I0 k) (r : Row Nat) (hr : r ∈ family B k i) :
    10 ∉ r.base := fun hm => SprintFamily.alphabet_final k
      ((family_basedOn B k i r hr).2.1.mem_iff.mp hm)

theorem family_closed_winding (k : Nat) :
    ∀ i : Index I0 k,
      ClosedTrail (family B k i) ∧ ((k + 8 : Nat) : Int) ∣ signedExcess (family B k i) := by
  induction k with
  | zero => exact fun i => ⟨B.closed i, B.winding i⟩
  | succ k ih =>
    intro ⟨i, p⟩
    have hl := family_length B k i
    have hk := family_kind B k i
    exact ⟨transportWalk_closedTrail (ih i).1 (k + 11) (k + 8) (by omega) hl hk (ih i).2 p.val p.isLt,
      transportWalk_winding_divisible _ (k + 11) (k + 8) (by omega) hl hk (ih i).2 p.val p.isLt⟩

theorem circles_valid (k : Nat) : CircleFamilyValid (k + 8) (circles B k) :=
  Iterated.circles_valid _ B.circles_valid B.circles_support k

theorem circles_support (k : Nat) : Iterated.CircleSupport k (circles B k) :=
  Iterated.circles_support _ B.circles_support k

theorem circle_length (k : Nat) {c : List Nat} (hc : c ∈ circles B k) : c.length = k + 8 :=
  (circles_valid B k c hc).1

theorem circle_nodup (k : Nat) {c : List Nat} (hc : c ∈ circles B k) : c.Nodup :=
  (circles_valid B k c hc).2

theorem circles_count (k : Nat) : (circles B k).length = selectedCircleCount k := by
  have he := Iterated.circles_length _ B.circles_valid B.circles_support k
  rw [B.circle_count] at he
  exact he

theorem selectedCircleCount_factorial (k : Nat) :
    5040 * selectedCircleCount k = 357 * (k + 7).factorial :=
  Iterated.circleCount_factorial 357 k

theorem circles_count_factorial (k : Nat) :
    5040 * (circles B k).length = 357 * (k + 7).factorial := by
  rw [circles_count]
  exact selectedCircleCount_factorial k

theorem circle_edges_count (k : Nat) :
    5040 * ((k + 8) * (circles B k).length) = 357 * (k + 8).factorial := by
  rw [Nat.mul_left_comm, circles_count_factorial,
    Nat.factorial_succ (k + 7)]
  ring

theorem family_safeCircleCover (k : Nat) :
    SafeCircleCover (family B k) 10 (k + 8) (circles B k) := by
  induction k with
  | zero => exact B.safe_cover
  | succ k ih =>
    exact ih.transport (family B k) (k + 11) 10 (k + 8) (by omega)
      (circles B k) (circles_valid B k)
      (family_length B k) (family_kind B k) (family_final_fresh B k)

theorem completedRows_counts (k : Nat) :
    (completedRows B k).length = (k + 9).factorial + ((rows B k).map Row.charge).sum ∧
    ((completedRows B k).map Row.visible).sum = (k + 10).factorial ∧
    ∀ r ∈ completedRows B k, r.Valid ∧ r.base.length = k + 10 := by
  have hr : ∀ r ∈ rows B k, r.Valid ∧ r.base.length = k + 9 := by
    intro r hr
    exact ⟨(rows_basedOn B k r hr).1,
      (rows_basedOn B k r hr).2.1.length_eq.trans (SprintFamily.alphabet_length k)⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [completedRows, Completion.packingRows_length _ _ hr, rows_length,
      show (k + 9).factorial = (k + 9) * (k + 8).factorial from Nat.factorial_succ (k + 8)]
  · rw [completedRows, Completion.packingRows_visible_sum _ _ hr, rows_length,
      show (k + 10).factorial = (k + 10) * (k + 9).factorial from Nat.factorial_succ (k + 9),
      show (k + 9).factorial = (k + 9) * (k + 8).factorial from Nat.factorial_succ (k + 8)]
    ring
  · simpa only [completedRows, SprintFamily.alphabet_length, show k + 9 + 1 = k + 10 by omega] using
      Completion.packingRows_valid (rows_basedOn B k) (SprintFamily.alphabet_final k) (by decide : 10 ≠ 9)

theorem completedRows_cover_range (k : Nat) {p : List Nat}
    (hp : p.Perm (List.range (k + 11))) : ∃ r ∈ completedRows B k, r.Assigned p :=
  Completion.packingRows_cover (rows_basedOn B k) (rows_complete B k)
    (SprintFamily.alphabet_nodup k) (SprintFamily.alphabet_nonempty k)
    (SprintFamily.alphabet_satellite k) (SprintFamily.alphabet_final k)
    (by decide) (hp.trans (SprintFamily.full_alphabet_perm k).symm)

theorem completedRows_word_support (k : Nat) {r : Row Nat} (hr : r ∈ completedRows B k) :
    ∀ a ∈ r.word, a < k + 11 := by
  intro a ha
  apply List.mem_range.mp
  exact (SprintFamily.full_alphabet_perm k).mem_iff.mp
    (Completion.packingRows_word_mem (rows_basedOn B k) hr ha)

theorem completed_family_closed (k : Nat) (i : Index I0 (k + 1)) :
    ClosedTrail (completedFamily B k i) := by
  obtain ⟨i, p⟩ := i
  have hc := family_closed_winding B k i
  exact Iterated.completionWalk_closed hc.1 (k + 8) (by omega)
    (family_length B k i) (family_kind B k i) hc.2 p.val p.isLt

theorem completed_family_nonempty (k : Nat) (i : Index I0 (k + 1)) :
    completedFamily B k i ≠ [] := (completed_family_closed B k i).1

theorem completed_family_edgePath (k : Nat) (i : Index I0 (k + 1)) :
    ∃ a, EdgePath Row.head Row.tail a (completedFamily B k i) a :=
  (completed_family_closed B k i).edgePath

theorem completed_family_inventory (k : Nat) :
    ((labels B (k + 1)).flatMap (completedFamily B k)).Perm (completedRows B k) := by
  have hlocal : ((labels B k).flatMap (fun i => (List.finRange (k + 8)).flatMap
      (fun p => completionWalk (family B k i) 10 p.val))).Perm
      ((labels B k).flatMap (fun i => Completion.packingRows (family B k i) 10)) := by
    apply flatMap_perm_of_pointwise
    intro i _
    exact completionWalk_inventory _ 10 (k + 9) (by omega)
      (family_length B k i) (family_kind B k i)
  have hi := (family_inventory B k).flatMap_right (fun r => Completion.completeRows r 10)
  have he : ((labels B (k + 1)).flatMap (completedFamily B k)) =
      (labels B k).flatMap (fun i => (List.finRange (k + 8)).flatMap
        (fun p => completionWalk (family B k i) 10 p.val)) := by
    change ((labels B k).product (List.finRange (k + 8))).flatMap
      (fun ip : Index I0 k × Fin (k + 8) => completionWalk (family B k ip.1) 10 ip.2.val) = _
    rw [List.product, List.flatMap_assoc]
    simp only [List.flatMap_map]
  rw [he]
  refine hlocal.trans ?_
  simpa only [completedRows, Completion.packingRows, List.flatMap_assoc] using hi

theorem completed_family_univ_inventory [Fintype I0] (k : Nat) :
    ((Finset.univ.toList : List (Index I0 (k + 1))).flatMap (completedFamily B k)).Perm
      (completedRows B k) :=
  ((labels_perm_univ B (k + 1)).symm.flatMap_right (completedFamily B k)).trans
    (completed_family_inventory B k)

theorem completed_family_circle_cover (k : Nat) :
    CoversDesignated (circles B k) (fun i => HeadVertex (completedFamily B k i)) :=
  (family_safeCircleCover B k).sound (circles_valid B k) (by omega)

theorem completed_family_row_mem (k : Nat) (i : Index I0 (k + 1))
    {r : Row Nat} (hr : r ∈ completedFamily B k i) : r ∈ completedRows B k :=
  (completed_family_inventory B k).mem_iff.mp
    (List.mem_flatMap.mpr ⟨i, labels_complete B (k + 1) i, hr⟩)

theorem completed_family_valid (k : Nat) (i : Index I0 (k + 1))
    {r : Row Nat} (hr : r ∈ completedFamily B k i) : r.Valid ∧ r.base.length = k + 10 :=
  (completedRows_counts B k).2.2 r (completed_family_row_mem B k i hr)

theorem completed_family_word_support (k : Nat) (i : Index I0 (k + 1))
    {r : Row Nat} (hr : r ∈ completedFamily B k i) : ∀ a ∈ r.word, a < k + 11 :=
  completedRows_word_support B k (completed_family_row_mem B k i hr)

theorem completed_family_cover_range (k : Nat) {p : List Nat}
    (hp : p.Perm (List.range (k + 11))) :
    ∃ i : Index I0 (k + 1), ∃ r ∈ completedFamily B k i, r.Assigned p := by
  obtain ⟨r, hr, ha⟩ := completedRows_cover_range B k hp
  have hm := (completed_family_inventory B k).mem_iff.mpr hr
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hm
  exact ⟨i, r, hi, ha⟩

theorem completed_family_cover_infix (k : Nat) {p : List Nat}
    (hp : p.Perm (List.range (k + 11))) :
    ∃ i : Index I0 (k + 1), ∃ r ∈ completedFamily B k i, p.IsInfix r.word := by
  obtain ⟨i, r, hr, ha⟩ := completed_family_cover_range B k hp
  exact ⟨i, r, hr, r.assigned_infix_word ha⟩

theorem completed_family_cover_mapped_permutation (k : Nat) {p : Word (k + 11)}
    (hp : IsPermutation p) :
    ∃ i : Index I0 (k + 1), ∃ r ∈ completedFamily B k i, (p.map Fin.val).IsInfix r.word :=
  completed_family_cover_infix B k (isPermutation_map_val_perm_range hp)

theorem completed_family_row_count (k : Nat) :
    ((labels B (k + 1)).flatMap (completedFamily B k)).length =
      (k + 9).factorial + ((rows B k).map Row.charge).sum :=
  (completed_family_inventory B k).length_eq.trans (completedRows_counts B k).1

theorem completed_family_visible_sum (k : Nat) :
    (((labels B (k + 1)).flatMap (completedFamily B k)).map Row.visible).sum =
      (k + 10).factorial :=
  ((completed_family_inventory B k).map Row.visible).sum_eq.trans
    (completedRows_counts B k).2.1

end SuperpermutationUpperBound43.Family
