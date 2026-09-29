import SuperpermutationUpperBound.CircleTransport.Iterated
import SuperpermutationUpperBound.Certificates.Circle377
import SuperpermutationUpperBound.Bounds.CircleCounts
import SuperpermutationUpperBound.Assembly.RowEdges

/-! The current all-size family, instantiated with the checked historical
377-circle certificate. Every label denotes an occurrence; equal rows or
equal endpoint tuples are never identified. -/
namespace SuperpermutationUpperBound.Bounds.CurrentCircleFamily

open CircleTransport
open Partition

abbrev Index (k : Nat) := Iterated.Index (Fin 364) k

def labels (k : Nat) : List (Index k) := Iterated.labels (List.finRange 364) k

def family (k : Nat) : Index k → List (Row Nat) :=
  Iterated.family Certificates.CircleBase.family9 k

def completedFamily (k : Nat) : Index (k + 1) → List (Row Nat) :=
  Iterated.completedFamily Certificates.CircleBase.family9 k

def circles (k : Nat) : List (List Nat) :=
  Iterated.circles Certificates.Circle377.circles k

private theorem base_support : Iterated.CircleSupport 0 Certificates.Circle377.circles := by
  intro c hc a ha
  exact ⟨Certificates.Circle377.circles_support c hc a ha,
    fun he => Certificates.Circle377.circles_avoid_satellite c hc (he ▸ ha)⟩

theorem labels_complete (k : Nat) (i : Index k) : i ∈ labels k :=
  Iterated.labels_complete _ List.mem_finRange k i

theorem labels_nodup (k : Nat) : (labels k).Nodup :=
  Iterated.labels_nodup (nodup_finRange 364) k

theorem labels_perm_univ (k : Nat) : (labels k).Perm Finset.univ.toList := by
  apply (List.perm_ext_iff_of_nodup (labels_nodup k) (Finset.nodup_toList _)).mpr
  intro i
  simp only [labels_complete k i, Finset.mem_toList, Finset.mem_univ]

theorem family_inventory (k : Nat) :
    ((labels k).flatMap (family k)).Perm (SprintFamily.rows k) :=
  Iterated.family_inventory _ _ List.mem_finRange Certificates.CircleBase.family9_inventory k

theorem family_univ_inventory (k : Nat) :
    ((Finset.univ.toList : List (Index k)).flatMap (family k)).Perm (SprintFamily.rows k) :=
  ((labels_perm_univ k).symm.flatMap_right (family k)).trans (family_inventory k)

theorem family_basedOn (k : Nat) (i : Index k) :
    BasedOn (SprintFamily.alphabet k) 9 (family k i) :=
  Iterated.family_basedOn _ _ List.mem_finRange Certificates.CircleBase.family9_inventory k i

theorem family_closed_winding (k : Nat) (i : Index k) :
    ClosedTrail (family k i) ∧ ((k + 8 : Nat) : Int) ∣ Transport.signedExcess (family k i) :=
  Iterated.family_closed_winding _ _ List.mem_finRange Certificates.CircleBase.family9_inventory
    (fun i => (Certificates.CircleBase.family9_closed_winding i).1)
    (fun i => (Certificates.CircleBase.family9_closed_winding i).2) k i

theorem family_length (k : Nat) (i : Index k) {r : Row Nat} (hr : r ∈ family k i) :
    r.base.length = k + 9 :=
  Iterated.family_length _ _ List.mem_finRange Certificates.CircleBase.family9_inventory k i r hr

theorem family_kind (k : Nat) (i : Index k) {r : Row Nat} (hr : r ∈ family k i) :
    r.visible = r.base.length ∨ r.visible = r.base.length - 2 :=
  Iterated.family_kind _ _ List.mem_finRange Certificates.CircleBase.family9_inventory k i r hr

theorem circles_valid (k : Nat) : CircleFamilyValid (k + 8) (circles k) :=
  Iterated.circles_valid _ Certificates.Circle377.circles_valid base_support k

theorem circle_length (k : Nat) {c : List Nat} (hc : c ∈ circles k) : c.length = k + 8 :=
  (circles_valid k c hc).1

theorem circle_nodup (k : Nat) {c : List Nat} (hc : c ∈ circles k) : c.Nodup :=
  (circles_valid k c hc).2

theorem circles_support (k : Nat) : Iterated.CircleSupport k (circles k) :=
  Iterated.circles_support _ base_support k

theorem circle_symbol_lt (k : Nat) {c : List Nat} (hc : c ∈ circles k)
    {a : Nat} (ha : a ∈ c) : a < k + 11 :=
  (circles_support k c hc a ha).1

theorem circle_avoid_satellite (k : Nat) {c : List Nat} (hc : c ∈ circles k) : 9 ∉ c :=
  fun ha => (circles_support k c hc 9 ha).2 rfl

theorem circleCount_eq_selectedCircleCount (k : Nat) :
    Iterated.circleCount 377 k = selectedCircleCount k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [Iterated.circleCount, selectedCircleCount, ih]

theorem circles_count (k : Nat) : (circles k).length = selectedCircleCount k := by
  have he := Iterated.circles_length _ Certificates.Circle377.circles_valid base_support k
  rw [Certificates.Circle377.circles_count, circleCount_eq_selectedCircleCount] at he
  exact he

theorem circles_count_factorial (k : Nat) :
    5040 * (circles k).length = 377 * (k + 7).factorial := by
  rw [circles_count]
  exact selectedCircleCount_factorial k

theorem circle_edges_count (k : Nat) :
    5040 * ((k + 8) * (circles k).length) = 377 * (k + 8).factorial := by
  rw [circles_count]
  exact selectedCircleCount_scaled k

theorem family_safeCircleCover (k : Nat) :
    SafeCircleCover (family k) 10 (k + 8) (circles k) :=
  Iterated.family_safeCircleCover _ _ _ List.mem_finRange Certificates.CircleBase.family9_inventory
    Certificates.Circle377.circles_valid base_support Certificates.Circle377.safe_cover k

theorem completed_family_closed (k : Nat) (i : Index (k + 1)) :
    ClosedTrail (completedFamily k i) :=
  Iterated.completed_family_closed _ _ List.mem_finRange Certificates.CircleBase.family9_inventory
    (fun i => (Certificates.CircleBase.family9_closed_winding i).1)
    (fun i => (Certificates.CircleBase.family9_closed_winding i).2) k i

theorem completed_family_nonempty (k : Nat) (i : Index (k + 1)) :
    completedFamily k i ≠ [] := (completed_family_closed k i).1

theorem completed_family_edgePath (k : Nat) (i : Index (k + 1)) :
    ∃ a, EdgePath Row.head Row.tail a (completedFamily k i) a :=
  (completed_family_closed k i).edgePath

theorem completed_family_inventory (k : Nat) :
    ((labels (k + 1)).flatMap (completedFamily k)).Perm (SprintFamily.completedRows k) :=
  Iterated.completed_family_inventory _ _ List.mem_finRange Certificates.CircleBase.family9_inventory k

theorem completed_family_univ_inventory (k : Nat) :
    ((Finset.univ.toList : List (Index (k + 1))).flatMap (completedFamily k)).Perm
      (SprintFamily.completedRows k) :=
  ((labels_perm_univ (k + 1)).symm.flatMap_right (completedFamily k)).trans
    (completed_family_inventory k)

theorem completed_family_circle_cover (k : Nat) :
    CoversDesignated (circles k) (fun i => HeadVertex (completedFamily k i)) :=
  Iterated.completed_family_circle_cover _ _ _ List.mem_finRange
    Certificates.CircleBase.family9_inventory Certificates.Circle377.circles_valid base_support
    Certificates.Circle377.safe_cover k

theorem completed_family_row_mem (k : Nat) (i : Index (k + 1))
    {r : Row Nat} (hr : r ∈ completedFamily k i) : r ∈ SprintFamily.completedRows k :=
  Iterated.completed_family_row_mem _ _ List.mem_finRange Certificates.CircleBase.family9_inventory k i hr

theorem completed_family_valid (k : Nat) (i : Index (k + 1))
    {r : Row Nat} (hr : r ∈ completedFamily k i) : r.Valid ∧ r.base.length = k + 10 :=
  Iterated.completed_family_valid _ _ List.mem_finRange Certificates.CircleBase.family9_inventory k i hr

theorem completed_family_word_support (k : Nat) (i : Index (k + 1))
    {r : Row Nat} (hr : r ∈ completedFamily k i) : ∀ a ∈ r.word, a < k + 11 :=
  Iterated.completed_family_word_support _ _ List.mem_finRange
    Certificates.CircleBase.family9_inventory k i hr

/-- Every required literal permutation is assigned to an actual row occurrence. -/
theorem completed_family_cover_range (k : Nat) {p : List Nat}
    (hp : p.Perm (List.range (k + 11))) :
    ∃ i : Index (k + 1), ∃ r ∈ completedFamily k i, r.Assigned p :=
  Iterated.completed_family_cover_range _ _ List.mem_finRange
    Certificates.CircleBase.family9_inventory k hp

theorem completed_family_cover_infix (k : Nat) {p : List Nat}
    (hp : p.Perm (List.range (k + 11))) :
    ∃ i : Index (k + 1), ∃ r ∈ completedFamily k i, p.IsInfix r.word := by
  obtain ⟨i, r, hr, ha⟩ := completed_family_cover_range k hp
  exact ⟨i, r, hr, r.assigned_infix_word ha⟩

theorem completed_family_cover_mapped_permutation (k : Nat) {p : Word (k + 11)}
    (hp : IsPermutation p) :
    ∃ i : Index (k + 1), ∃ r ∈ completedFamily k i, (p.map Fin.val).IsInfix r.word :=
  completed_family_cover_infix k (isPermutation_map_val_perm_range hp)

theorem completed_family_row_count (k : Nat) :
    ((labels (k + 1)).flatMap (completedFamily k)).length =
      (k + 9).factorial + ((SprintFamily.rows k).map Row.charge).sum :=
  (completed_family_inventory k).length_eq.trans (SprintFamily.completedRows_counts k).1

theorem completed_family_visible_sum (k : Nat) :
    (((labels (k + 1)).flatMap (completedFamily k)).map Row.visible).sum =
      (k + 10).factorial :=
  ((completed_family_inventory k).map Row.visible).sum_eq.trans
    (SprintFamily.completedRows_counts k).2.1

/-- Exact charge and selected-circle contribution for the actual family. -/
theorem principal_numerator (k : Nat) :
    5040 * ((((labels k).flatMap (family k)).map Row.charge).sum +
      (k + 8) * (circles k).length) = 2729 * (k + 8).factorial := by
  rw [((family_inventory k).map Row.charge).sum_eq, circles_count]
  exact current_principal_numerator k

end SuperpermutationUpperBound.Bounds.CurrentCircleFamily
