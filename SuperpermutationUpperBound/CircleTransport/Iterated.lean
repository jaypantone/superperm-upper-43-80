import SuperpermutationUpperBound.CircleTransport.TrackCounts
import SuperpermutationUpperBound.Partition.SprintFamily

/-! Iteration of the literal current-family circle construction. The old
satellite 9 and completion letter 10 remain fixed; new ordinary letters are 11, 12,... . -/
namespace SuperpermutationUpperBound.CircleTransport.Iterated

open Transport
open Partition
variable {I0 : Type}

/-- Source component occurrences, with one additional port label at each stage. -/
def Index (I0 : Type) : Nat → Type
  | 0 => I0
  | k + 1 => Index I0 k × Fin (k + 8)

instance indexFintype (I0 : Type) [Fintype I0] : (k : Nat) → Fintype (Index I0 k)
  | 0 => by change Fintype I0; infer_instance
  | k + 1 => by
    letI : Fintype (Index I0 k) := indexFintype I0 k
    change Fintype (Index I0 k × Fin (k + 8))
    infer_instance

instance indexDecidableEq (I0 : Type) [DecidableEq I0] : (k : Nat) → DecidableEq (Index I0 k)
  | 0 => by change DecidableEq I0; infer_instance
  | k + 1 => by
    letI : DecidableEq (Index I0 k) := indexDecidableEq I0 k
    change DecidableEq (Index I0 k × Fin (k + 8))
    infer_instance

/-- The enumeration order is explicit and agrees with the finite certificate's
base label list. No set conversion discards repeated row values. -/
def labels (baseLabels : List I0) : (k : Nat) → List (Index I0 k)
  | 0 => baseLabels
  | k + 1 => (labels baseLabels k).product (List.finRange (k + 8))

def family (baseFamily : I0 → List (Row Nat)) : (k : Nat) → Index I0 k → List (Row Nat)
  | 0, i => baseFamily i
  | k + 1, ip => transportWalk (family baseFamily k ip.1) (k + 11) ip.2.val

def circles (baseCircles : List (List Nat)) : Nat → List (List Nat)
  | 0 => baseCircles
  | k + 1 => extendCircles (circles baseCircles k) (k + 11)

/-- The recurrence can be instantiated with 377 without importing numerical bounds. -/
def circleCount (c0 : Nat) : Nat → Nat
  | 0 => c0
  | k + 1 => (k + 8) * circleCount c0 k

def CircleSupport (k : Nat) (cs : List (List Nat)) : Prop :=
  ∀ c ∈ cs, ∀ a ∈ c, a < k + 11 ∧ a ≠ 9

theorem labels_complete (baseLabels : List I0) (hb : ∀ i, i ∈ baseLabels) (k : Nat) :
    ∀ i, i ∈ labels baseLabels k := by
  induction k with
  | zero => exact hb
  | succ k ih =>
    intro ⟨i, p⟩
    exact List.mem_product.mpr ⟨ih i, List.mem_finRange p⟩

theorem labels_nodup {baseLabels : List I0} (hb : baseLabels.Nodup) (k : Nat) :
    (labels baseLabels k).Nodup := by
  induction k with
  | zero => exact hb
  | succ k ih => exact ih.product (nodup_finRange _)

/-- The literal indexed family has exactly the prescribed current row inventory. -/
theorem family_inventory (baseLabels : List I0) (baseFamily : I0 → List (Row Nat))
    (hlabels : ∀ i, i ∈ baseLabels)
    (hbase : (baseLabels.flatMap baseFamily).Perm SprintBase.rows9) (k : Nat) :
    ((labels baseLabels k).flatMap (family baseFamily k)).Perm (SprintFamily.rows k) := by
  induction k with
  | zero => exact hbase
  | succ k ih =>
    have hlen : ∀ i (r : Row Nat), r ∈ family baseFamily k i → r.base.length = (k + 8) + 1 := by
      intro i r hr
      have hm : r ∈ SprintFamily.rows k := ih.mem_iff.mp
        (List.mem_flatMap.mpr ⟨i, labels_complete baseLabels hlabels k i, hr⟩)
      exact (SprintFamily.rows_basedOn k r hm).2.1.length_eq.trans (SprintFamily.alphabet_length k)
    have hp : ((labels baseLabels k).flatMap (fun i =>
        (List.finRange (k + 8)).flatMap (fun p => transportWalk (family baseFamily k i) (k + 11) p.val))).Perm
        ((labels baseLabels k).flatMap (fun i => Transport.packingRows (family baseFamily k i) (k + 11))) := by
      apply flatMap_perm_of_pointwise
      intro i _
      exact transportWalk_inventory _ _ (k + 8) (by omega) (hlen i)
    have hi := ih.flatMap_right (fun r => Transport.rows r (k + 11))
    change ((labels baseLabels (k + 1)).flatMap (family baseFamily (k + 1))).Perm
      (Transport.packingRows (SprintFamily.rows k) (k + 11))
    have he : ((labels baseLabels (k + 1)).flatMap (family baseFamily (k + 1))) =
        (labels baseLabels k).flatMap (fun i => (List.finRange (k + 8)).flatMap
          (fun p => transportWalk (family baseFamily k i) (k + 11) p.val)) := by
      change ((labels baseLabels k).product (List.finRange (k + 8))).flatMap
        (fun ip : Index I0 k × Fin (k + 8) => transportWalk (family baseFamily k ip.1) (k + 11) ip.2.val) = _
      rw [List.product, List.flatMap_assoc]
      simp only [List.flatMap_map]
    rw [he]
    apply hp.trans
    simpa only [Transport.packingRows, List.flatMap_assoc] using hi

theorem family_basedOn (baseLabels : List I0) (baseFamily : I0 → List (Row Nat))
    (hlabels : ∀ i, i ∈ baseLabels)
    (hbase : (baseLabels.flatMap baseFamily).Perm SprintBase.rows9) (k : Nat) (i : Index I0 k) :
    BasedOn (SprintFamily.alphabet k) 9 (family baseFamily k i) := by
  intro r hr
  apply SprintFamily.rows_basedOn k r
  exact (family_inventory baseLabels baseFamily hlabels hbase k).mem_iff.mp
    (List.mem_flatMap.mpr ⟨i, labels_complete baseLabels hlabels k i, hr⟩)

theorem family_length (baseLabels : List I0) (baseFamily : I0 → List (Row Nat))
    (hlabels : ∀ i, i ∈ baseLabels)
    (hbase : (baseLabels.flatMap baseFamily).Perm SprintBase.rows9)
    (k : Nat) (i : Index I0 k) (r : Row Nat) (hr : r ∈ family baseFamily k i) :
    r.base.length = k + 9 :=
  (family_basedOn baseLabels baseFamily hlabels hbase k i r hr).2.1.length_eq.trans
    (SprintFamily.alphabet_length k)

theorem family_kind (baseLabels : List I0) (baseFamily : I0 → List (Row Nat))
    (hlabels : ∀ i, i ∈ baseLabels)
    (hbase : (baseLabels.flatMap baseFamily).Perm SprintBase.rows9)
    (k : Nat) (i : Index I0 k) (r : Row Nat) (hr : r ∈ family baseFamily k i) :
    r.visible = r.base.length ∨ r.visible = r.base.length - 2 :=
  (family_basedOn baseLabels baseFamily hlabels hbase k i r hr).2.2.2

theorem family_final_fresh (baseLabels : List I0) (baseFamily : I0 → List (Row Nat))
    (hlabels : ∀ i, i ∈ baseLabels)
    (hbase : (baseLabels.flatMap baseFamily).Perm SprintBase.rows9)
    (k : Nat) (i : Index I0 k) (r : Row Nat) (hr : r ∈ family baseFamily k i) :
    10 ∉ r.base := fun hm => SprintFamily.alphabet_final k
      ((family_basedOn baseLabels baseFamily hlabels hbase k i r hr).2.1.mem_iff.mp hm)

/-- Every actual indexed track remains closed with the next winding divisibility. -/
theorem family_closed_winding (baseLabels : List I0) (baseFamily : I0 → List (Row Nat))
    (hlabels : ∀ i, i ∈ baseLabels)
    (hbase : (baseLabels.flatMap baseFamily).Perm SprintBase.rows9)
    (hclosed : ∀ i, ClosedTrail (baseFamily i))
    (hwinding : ∀ i, (8 : Int) ∣ signedExcess (baseFamily i)) (k : Nat) :
    ∀ i, ClosedTrail (family baseFamily k i) ∧ ((k + 8 : Nat) : Int) ∣ signedExcess (family baseFamily k i) := by
  induction k with
  | zero => exact fun i => ⟨hclosed i, hwinding i⟩
  | succ k ih =>
    intro ⟨i, p⟩
    have hl := family_length baseLabels baseFamily hlabels hbase k i
    have hk := family_kind baseLabels baseFamily hlabels hbase k i
    exact ⟨transportWalk_closedTrail (ih i).1 (k + 11) (k + 8) (by omega) hl hk (ih i).2 p.val p.isLt,
      transportWalk_winding_divisible _ (k + 11) (k + 8) (by omega) hl hk (ih i).2 p.val p.isLt⟩

/-- Circle representatives use only the available word alphabet and exclude the satellite. -/
theorem circles_support (baseCircles : List (List Nat)) (hs : CircleSupport 0 baseCircles) (k : Nat) :
    CircleSupport k (circles baseCircles k) := by
  induction k with
  | zero => exact hs
  | succ k ih =>
    intro c hc a ha
    obtain ⟨old, hold, hc⟩ := List.mem_flatMap.mp hc
    have hm := (fullBases_perm hc).mem_iff.mp ha
    rcases List.mem_cons.mp hm with rfl | ha
    · exact ⟨by omega, by omega⟩
    · have ho := ih old hold a ha
      exact ⟨by omega, ho.2⟩

theorem circles_valid (baseCircles : List (List Nat))
    (hv : CircleFamilyValid 8 baseCircles) (hs : CircleSupport 0 baseCircles) (k : Nat) :
    CircleFamilyValid (k + 8) (circles baseCircles k) := by
  induction k with
  | zero => exact hv
  | succ k ih =>
    exact ih.extend (k + 11) (fun c hc ha => by
      have := (circles_support baseCircles hs k c hc (k + 11) ha).1
      omega)

theorem circles_length (baseCircles : List (List Nat))
    (hv : CircleFamilyValid 8 baseCircles) (hs : CircleSupport 0 baseCircles) (k : Nat) :
    (circles baseCircles k).length = circleCount baseCircles.length k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [circles, extendCircles_length (k + 8) _ _
      (fun c hc => (circles_valid baseCircles hv hs k c hc).1), ih]
    rfl

/-- The actual all-size current family retains the semantic mixed circle cover. -/
theorem family_safeCircleCover (baseLabels : List I0) (baseFamily : I0 → List (Row Nat))
    (baseCircles : List (List Nat)) (hlabels : ∀ i, i ∈ baseLabels)
    (hbase : (baseLabels.flatMap baseFamily).Perm SprintBase.rows9)
    (hv : CircleFamilyValid 8 baseCircles) (hs : CircleSupport 0 baseCircles)
    (hc : SafeCircleCover baseFamily 10 8 baseCircles) (k : Nat) :
    SafeCircleCover (family baseFamily k) 10 (k + 8) (circles baseCircles k) := by
  induction k with
  | zero => exact hc
  | succ k ih =>
    exact ih.transport (family baseFamily k) (k + 11) 10 (k + 8) (by omega)
      (circles baseCircles k) (circles_valid baseCircles hv hs k)
      (family_length baseLabels baseFamily hlabels hbase k)
      (family_kind baseLabels baseFamily hlabels hbase k)
      (family_final_fresh baseLabels baseFamily hlabels hbase k)

theorem circleCount_factorial (c0 k : Nat) :
    5040 * circleCount c0 k = c0 * (k + 7).factorial := by
  induction k with
  | zero => simp [circleCount, Nat.factorial, Nat.mul_comm]
  | succ k ih =>
    change 5040 * ((k + 8) * circleCount c0 k) = _
    rw [show (k + 1 + 7).factorial = (k + 8) * (k + 7).factorial from Nat.factorial_succ (k + 7)]
    calc
      5040 * ((k + 8) * circleCount c0 k) = (k + 8) * (5040 * circleCount c0 k) := by ring
      _ = (k + 8) * (c0 * (k + 7).factorial) := by rw [ih]
      _ = c0 * ((k + 8) * (k + 7).factorial) := by ring

theorem circles_length_factorial (baseCircles : List (List Nat))
    (hv : CircleFamilyValid 8 baseCircles) (hs : CircleSupport 0 baseCircles) (k : Nat) :
    5040 * (circles baseCircles k).length = baseCircles.length * (k + 7).factorial := by
  rw [circles_length baseCircles hv hs k]
  exact circleCount_factorial baseCircles.length k

/-- The designated completed macro trails at a stage have the same occurrence
index type as the next transport family. -/
def completedFamily (baseFamily : I0 → List (Row Nat)) (k : Nat) : Index I0 (k + 1) → List (Row Nat) :=
  fun ip => completionWalk (family baseFamily k ip.1) 10 ip.2.val

/-- Completion preserves closure for each individual returning port walk. -/
theorem completionWalk_closed {rs : List (Row Nat)} (hc : ClosedTrail rs)
    (h : Nat) (hn : 3 ≤ h + 1)
    (hlen : ∀ r ∈ rs, r.base.length = h + 1)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (hw : (h : Int) ∣ signedExcess rs) (p : Nat) (hp : p < h) :
    ClosedTrail (completionWalk rs 10 p) := by
  have hne := completionWalk_nonempty rs 10 p hc.1
  have hchain : RowTrailCompatible (rs.head hc.1) rs.tail := by
    cases rs with
    | nil => exact False.elim (hc.1 rfl)
    | cons r rs => exact closedTrail_internal hc
  have hi := completionWalk_internal rs hc.1 10 (h + 1) p hn (by omega) hlen hkind hchain
  have hb : ((completionWalk rs 10 p).getLast hne).Compatible ((completionWalk rs 10 p).head hne) := by
    change _ = _
    rw [completionWalk_last_tail rs hc.1 10 (h + 1) p hn (by omega) hlen hkind,
      completionWalk_head rs hc.1 10 (h + 1) p hn (by omega) hlen hkind,
      completionExit_eq_self_of_winding rs h hn hlen hkind hw p hp,
      closedTrail_last_compatible_head hc]
  have hr := pathRunsTo_of_path_spec _ _ hne hi hb
  obtain ⟨a, as, he⟩ := List.exists_cons_of_ne_nil hne
  simp only [he, List.head_cons] at hr
  rw [he]
  exact closedTrail_of_pathRunsTo hr

theorem completed_family_closed (baseLabels : List I0) (baseFamily : I0 → List (Row Nat))
    (hlabels : ∀ i, i ∈ baseLabels)
    (hbase : (baseLabels.flatMap baseFamily).Perm SprintBase.rows9)
    (hclosed : ∀ i, ClosedTrail (baseFamily i))
    (hwinding : ∀ i, (8 : Int) ∣ signedExcess (baseFamily i)) (k : Nat) :
    ∀ i, ClosedTrail (completedFamily baseFamily k i) := by
  intro ⟨i, p⟩
  have hc := family_closed_winding baseLabels baseFamily hlabels hbase hclosed hwinding k i
  exact completionWalk_closed hc.1 (k + 8) (by omega)
    (family_length baseLabels baseFamily hlabels hbase k i)
    (family_kind baseLabels baseFamily hlabels hbase k i) hc.2 p.val p.isLt

theorem completed_family_inventory (baseLabels : List I0) (baseFamily : I0 → List (Row Nat))
    (hlabels : ∀ i, i ∈ baseLabels)
    (hbase : (baseLabels.flatMap baseFamily).Perm SprintBase.rows9) (k : Nat) :
    ((labels baseLabels (k + 1)).flatMap (completedFamily baseFamily k)).Perm
      (SprintFamily.completedRows k) := by
  have hlocal : ((labels baseLabels k).flatMap (fun i => (List.finRange (k + 8)).flatMap
      (fun p => completionWalk (family baseFamily k i) 10 p.val))).Perm
      ((labels baseLabels k).flatMap (fun i => Completion.packingRows (family baseFamily k i) 10)) := by
    apply flatMap_perm_of_pointwise
    intro i _
    exact completionWalk_inventory _ 10 (k + 9) (by omega)
      (family_length baseLabels baseFamily hlabels hbase k i)
      (family_kind baseLabels baseFamily hlabels hbase k i)
  have hi := (family_inventory baseLabels baseFamily hlabels hbase k).flatMap_right
    (fun r => Completion.completeRows r 10)
  have he : ((labels baseLabels (k + 1)).flatMap (completedFamily baseFamily k)) =
      (labels baseLabels k).flatMap (fun i => (List.finRange (k + 8)).flatMap
        (fun p => completionWalk (family baseFamily k i) 10 p.val)) := by
    change ((labels baseLabels k).product (List.finRange (k + 8))).flatMap
      (fun ip : Index I0 k × Fin (k + 8) => completionWalk (family baseFamily k ip.1) 10 ip.2.val) = _
    rw [List.product, List.flatMap_assoc]
    simp only [List.flatMap_map]
  rw [he]
  refine hlocal.trans ?_
  simpa only [SprintFamily.completedRows, Completion.packingRows, List.flatMap_assoc] using hi

/-- Selected circle occurrences meet every actual designated completed trail. -/
theorem completed_family_circle_cover (baseLabels : List I0) (baseFamily : I0 → List (Row Nat))
    (baseCircles : List (List Nat)) (hlabels : ∀ i, i ∈ baseLabels)
    (hbase : (baseLabels.flatMap baseFamily).Perm SprintBase.rows9)
    (hv : CircleFamilyValid 8 baseCircles) (hs : CircleSupport 0 baseCircles)
    (hc : SafeCircleCover baseFamily 10 8 baseCircles) (k : Nat) :
    CoversDesignated (circles baseCircles k) (fun i => HeadVertex (completedFamily baseFamily k i)) := by
  exact (family_safeCircleCover baseLabels baseFamily baseCircles hlabels hbase hv hs hc k).sound
    (circles_valid baseCircles hv hs k) (by omega)

/-- Combined actual-family invariant, conditional only on the finite semantic base certificate. -/
theorem iteration_certificate (baseLabels : List I0) (baseFamily : I0 → List (Row Nat))
    (baseCircles : List (List Nat)) (hlabels : ∀ i, i ∈ baseLabels)
    (hbase : (baseLabels.flatMap baseFamily).Perm SprintBase.rows9)
    (hclosed : ∀ i, ClosedTrail (baseFamily i))
    (hwinding : ∀ i, (8 : Int) ∣ signedExcess (baseFamily i))
    (hv : CircleFamilyValid 8 baseCircles) (hs : CircleSupport 0 baseCircles)
    (hc : SafeCircleCover baseFamily 10 8 baseCircles) (k : Nat) :
    (∀ i, ClosedTrail (family baseFamily k i) ∧ ((k + 8 : Nat) : Int) ∣ signedExcess (family baseFamily k i)) ∧
    ((labels baseLabels k).flatMap (family baseFamily k)).Perm (SprintFamily.rows k) ∧
    SafeCircleCover (family baseFamily k) 10 (k + 8) (circles baseCircles k) ∧
    CircleFamilyValid (k + 8) (circles baseCircles k) ∧ CircleSupport k (circles baseCircles k) ∧
    (circles baseCircles k).length = circleCount baseCircles.length k :=
  ⟨family_closed_winding baseLabels baseFamily hlabels hbase hclosed hwinding k,
    family_inventory baseLabels baseFamily hlabels hbase k,
    family_safeCircleCover baseLabels baseFamily baseCircles hlabels hbase hv hs hc k,
    circles_valid baseCircles hv hs k, circles_support baseCircles hs k,
    circles_length baseCircles hv hs k⟩

/-- Every completed row occurrence belongs to the current complete row family. -/
theorem completed_family_row_mem (baseLabels : List I0) (baseFamily : I0 → List (Row Nat))
    (hlabels : ∀ i, i ∈ baseLabels)
    (hbase : (baseLabels.flatMap baseFamily).Perm SprintBase.rows9)
    (k : Nat) (i : Index I0 (k + 1)) {r : Row Nat} (hr : r ∈ completedFamily baseFamily k i) :
    r ∈ SprintFamily.completedRows k :=
  (completed_family_inventory baseLabels baseFamily hlabels hbase k).mem_iff.mp
    (List.mem_flatMap.mpr ⟨i, labels_complete baseLabels hlabels (k + 1) i, hr⟩)

theorem completed_family_valid (baseLabels : List I0) (baseFamily : I0 → List (Row Nat))
    (hlabels : ∀ i, i ∈ baseLabels)
    (hbase : (baseLabels.flatMap baseFamily).Perm SprintBase.rows9)
    (k : Nat) (i : Index I0 (k + 1)) {r : Row Nat} (hr : r ∈ completedFamily baseFamily k i) :
    r.Valid ∧ r.base.length = k + 10 :=
  (SprintFamily.completedRows_counts k).2.2 r
    (completed_family_row_mem baseLabels baseFamily hlabels hbase k i hr)

/-- Literal assigned-word coverage of every required permutation is retained
in the indexed completed family, rather than inferred from its scalar counts. -/
theorem completed_family_cover_range (baseLabels : List I0) (baseFamily : I0 → List (Row Nat))
    (hlabels : ∀ i, i ∈ baseLabels)
    (hbase : (baseLabels.flatMap baseFamily).Perm SprintBase.rows9)
    (k : Nat) {p : List Nat} (hp : p.Perm (List.range (k + 11))) :
    ∃ i : Index I0 (k + 1), ∃ r ∈ completedFamily baseFamily k i, r.Assigned p := by
  obtain ⟨r, hr, ha⟩ := SprintFamily.completedRows_cover_range k hp
  have hm := (completed_family_inventory baseLabels baseFamily hlabels hbase k).mem_iff.mpr hr
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hm
  exact ⟨i, r, hi, ha⟩

theorem completed_family_word_support (baseLabels : List I0) (baseFamily : I0 → List (Row Nat))
    (hlabels : ∀ i, i ∈ baseLabels)
    (hbase : (baseLabels.flatMap baseFamily).Perm SprintBase.rows9)
    (k : Nat) (i : Index I0 (k + 1)) {r : Row Nat} (hr : r ∈ completedFamily baseFamily k i) :
    ∀ a ∈ r.word, a < k + 11 :=
  SprintFamily.completedRows_word_support k
    (completed_family_row_mem baseLabels baseFamily hlabels hbase k i hr)

end SuperpermutationUpperBound.CircleTransport.Iterated
