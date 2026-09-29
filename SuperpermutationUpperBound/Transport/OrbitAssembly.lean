import SuperpermutationUpperBound.TrailSpelling
import SuperpermutationUpperBound.Foundation.Rotation

/-! Concatenation of labeled literal paths along a returning successor orbit.
Path labels and row occurrences remain distinct from their endpoint tuples. -/
namespace SuperpermutationUpperBound.Transport

variable {α β : Type}

/-- A possibly empty row sequence has successive edges all the way to `last`. -/
def PathRunsTo (path : List (Row α)) (last : Row α) : Prop :=
  match path with
  | [] => False
  | first :: rest => RowTrailCompatible first (rest ++ [last])

theorem rowTrailCompatible_append_iff (first next : Row α)
    (rest more : List (Row α)) :
    RowTrailCompatible first (rest ++ next :: more) ↔
      RowTrailCompatible first (rest ++ [next]) ∧ RowTrailCompatible next more := by
  induction rest generalizing first with
  | nil => simp [RowTrailCompatible]
  | cons a rest ih =>
    simp only [List.cons_append, RowTrailCompatible, ih]
    exact and_assoc.symm

theorem rowTrailCompatible_loop_iff_zip (first last : Row α) (rest : List (Row α)) :
    RowTrailCompatible first (rest ++ [last]) ↔
      ∀ pair ∈ (first :: rest).zip (rest ++ [last]), pair.1.Compatible pair.2 := by
  induction rest generalizing first with
  | nil => simp [RowTrailCompatible]
  | cons a rest ih =>
    simp only [List.cons_append, List.zip_cons_cons, List.mem_cons,
      forall_eq_or_imp, RowTrailCompatible, ih]

theorem rot_cons_one (first : Row α) (rest : List (Row α)) :
    rot (first :: rest) 1 = rest ++ [first] := by
  rw [rot_eq_drop_append_take_of_le _ _ (by simp)]
  simp

theorem closedTrail_of_pathRunsTo {first : Row α} {rest : List (Row α)}
    (h : PathRunsTo (first :: rest) first) : ClosedTrail (first :: rest) := by
  refine ⟨by simp, ?_⟩
  change ∀ pair ∈ (first :: rest).zip (rot (first :: rest) 1), _
  rw [rot_cons_one]
  exact (rowTrailCompatible_loop_iff_zip first first rest).mp h

theorem pathRunsTo_nonempty {path : List (Row α)} {last : Row α}
    (h : PathRunsTo path last) : path ≠ [] := by
  intro heq
  subst path
  exact h

/-- Concatenation uses only actual boundary compatibility, never endpoint uniqueness. -/
theorem pathRunsTo_append {left : List (Row α)} {first last : Row α}
    {rest : List (Row α)} (hl : PathRunsTo left first)
    (hr : PathRunsTo (first :: rest) last) :
    PathRunsTo (left ++ first :: rest) last := by
  cases left with
  | nil => exact False.elim hl
  | cons a left =>
    change RowTrailCompatible a ((left ++ first :: rest) ++ [last])
    rw [List.append_assoc]
    exact (rowTrailCompatible_append_iff a first left (rest ++ [last])).mpr ⟨hl, hr⟩

/-- Internal compatibility plus a final literal boundary is the path contract. -/
theorem pathRunsTo_of_internal_and_last {first last : Row α} {rest : List (Row α)}
    (hi : RowTrailCompatible first rest)
    (hb : ((first :: rest).getLast (by simp)).Compatible last) :
    PathRunsTo (first :: rest) last := by
  induction rest generalizing first with
  | nil => exact ⟨hb, True.intro⟩
  | cons a rest ih =>
    refine ⟨hi.1, ?_⟩
    exact ih hi.2 (by simpa using hb)

/-- Advance a label a fixed number of successor steps. -/
def advance (next : β → β) (start : β) : Nat → β
  | 0 => start
  | k + 1 => advance next (next start) k

/-- Ordered labels visited before the final successor step. -/
def orbitLabels (next : β → β) (start : β) : Nat → List β
  | 0 => []
  | k + 1 => start :: orbitLabels next (next start) k

@[simp] theorem orbitLabels_length (next : β → β) (start : β) (k : Nat) :
    (orbitLabels next start k).length = k := by
  induction k generalizing start with
  | zero => rfl
  | succ k ih => simp [orbitLabels, ih]

/-- Literal concatenation, retaining all row occurrences along an orbit. -/
def orbitRows (paths : β → List (Row α)) (next : β → β) (start : β) (k : Nat) :
    List (Row α) := (orbitLabels next start k).flatMap paths

@[simp] theorem orbitRows_zero (paths : β → List (Row α)) (next : β → β) (start : β) :
    orbitRows paths next start 0 = [] := rfl

theorem orbitRows_succ (paths : β → List (Row α)) (next : β → β) (start : β) (k : Nat) :
    orbitRows paths next start (k + 1) = paths start ++ orbitRows paths next (next start) k := rfl

theorem orbitRows_nonempty (paths : β → List (Row α)) (next : β → β) (start : β)
    (hpaths : ∀ i, paths i ≠ []) {k : Nat} (hk : 0 < k) :
    orbitRows paths next start k ≠ [] := by
  cases k with
  | zero => exfalso; omega
  | succ k =>
    intro h
    exact hpaths start (List.append_eq_nil_iff.mp h).1

theorem orbitRows_head (paths : β → List (Row α)) (next : β → β) (start : β)
    (hpaths : ∀ i, paths i ≠ []) {k : Nat} (hk : 0 < k) :
    (orbitRows paths next start k).head (orbitRows_nonempty paths next start hpaths hk) =
      (paths start).head (hpaths start) := by
  cases k with
  | zero => exfalso; omega
  | succ k => simp only [orbitRows_succ, List.head_append_left (hpaths start)]

theorem orbitRows_runsTo (paths : β → List (Row α)) (next : β → β)
    (hpaths : ∀ i, paths i ≠ [])
    (hsteps : ∀ i, PathRunsTo (paths i) ((paths (next i)).head (hpaths (next i))))
    (start : β) {k : Nat} (hk : 0 < k) :
    PathRunsTo (orbitRows paths next start k)
      ((paths (advance next start k)).head (hpaths (advance next start k))) := by
  induction k generalizing start with
  | zero => exfalso; omega
  | succ k ih =>
    cases k with
    | zero => simpa [orbitRows_succ, advance] using hsteps start
    | succ k =>
      have hne := orbitRows_nonempty paths next (next start) hpaths (by omega : 0 < k + 1)
      obtain ⟨first, rest, heq⟩ := List.exists_cons_of_ne_nil hne
      have hh : first = (paths (next start)).head (hpaths (next start)) := by
        have hh := orbitRows_head paths next (next start) hpaths (by omega : 0 < k + 1)
        simpa only [heq, List.head_cons] using hh
      have hl : PathRunsTo (paths start) first := by rw [hh]; exact hsteps start
      have hr := ih (next start) (by omega : 0 < k + 1)
      rw [heq] at hr
      change PathRunsTo (paths start ++ orbitRows paths next (next start) (k + 1)) _
      rw [heq]
      exact pathRunsTo_append hl hr

/-- Any positive returning successor orbit spells one actual closed row trail.
This does not assume distinct endpoint tuples or distinct row values. -/
theorem orbitRows_closedTrail (paths : β → List (Row α)) (next : β → β)
    (hpaths : ∀ i, paths i ≠ [])
    (hsteps : ∀ i, PathRunsTo (paths i) ((paths (next i)).head (hpaths (next i))))
    (start : β) {k : Nat} (hk : 0 < k) (hreturn : advance next start k = start) :
    ClosedTrail (orbitRows paths next start k) := by
  have hne := orbitRows_nonempty paths next start hpaths hk
  obtain ⟨first, rest, heq⟩ := List.exists_cons_of_ne_nil hne
  have hh : first = (paths start).head (hpaths start) := by
    have hh := orbitRows_head paths next start hpaths hk
    simpa only [heq, List.head_cons] using hh
  have hr := orbitRows_runsTo paths next hpaths hsteps start hk
  rw [hreturn, heq, ← hh] at hr
  rw [heq]
  exact closedTrail_of_pathRunsTo hr

theorem orbitRows_length (paths : β → List (Row α)) (next : β → β) (start : β) (k : Nat) :
    (orbitRows paths next start k).length =
      ((orbitLabels next start k).map (fun i => (paths i).length)).sum := by
  induction k generalizing start with
  | zero => rfl
  | succ k ih => simp [orbitRows_succ, orbitLabels, ih]

theorem pathRunsTo_of_path_spec (path : List (Row α)) (last : Row α) (hne : path ≠ [])
    (hi : RowTrailCompatible (path.head hne) path.tail)
    (hb : (path.getLast hne).Compatible last) : PathRunsTo path last := by
  cases path with
  | nil => exact False.elim (hne rfl)
  | cons first rest => exact pathRunsTo_of_internal_and_last hi hb

/-- List-based input contract: each path is internally compatible and its
last row matches the first row at the successor label. -/
theorem orbitRows_closedTrail_of_endpoints (paths : β → List (Row α)) (next : β → β)
    (hpaths : ∀ i, paths i ≠ [])
    (hinternal : ∀ i, RowTrailCompatible ((paths i).head (hpaths i)) (paths i).tail)
    (hboundary : ∀ i, ((paths i).getLast (hpaths i)).Compatible
      ((paths (next i)).head (hpaths (next i))))
    (start : β) {k : Nat} (hk : 0 < k) (hreturn : advance next start k = start) :
    ClosedTrail (orbitRows paths next start k) := by
  apply orbitRows_closedTrail paths next hpaths _ start hk hreturn
  intro i
  exact pathRunsTo_of_path_spec (paths i) _ (hpaths i) (hinternal i) (hboundary i)

/-- The closed trail retains precisely the ordered row occurrences of this
returning orbit; no duplicate-valued row occurrence is discarded. -/
theorem returning_orbit_assembly (paths : β → List (Row α)) (next : β → β)
    (hpaths : ∀ i, paths i ≠ [])
    (hinternal : ∀ i, RowTrailCompatible ((paths i).head (hpaths i)) (paths i).tail)
    (hboundary : ∀ i, ((paths i).getLast (hpaths i)).Compatible
      ((paths (next i)).head (hpaths (next i))))
    (start : β) {k : Nat} (hk : 0 < k) (hreturn : advance next start k = start) :
    ∃ trail, ClosedTrail trail ∧
      trail = (orbitLabels next start k).flatMap paths ∧
      trail.length = ((orbitLabels next start k).map (fun i => (paths i).length)).sum := by
  exact ⟨orbitRows paths next start k,
    orbitRows_closedTrail_of_endpoints paths next hpaths hinternal hboundary start hk hreturn,
    rfl, orbitRows_length paths next start k⟩

/-- Once labeled successor orbits partition the labels, their literal path
concatenations partition every row occurrence into closed trails. -/
theorem assembly_of_orbit_partition (paths : β → List (Row α)) (next : β → β)
    (hpaths : ∀ i, paths i ≠ [])
    (hinternal : ∀ i, RowTrailCompatible ((paths i).head (hpaths i)) (paths i).tail)
    (hboundary : ∀ i, ((paths i).getLast (hpaths i)).Compatible
      ((paths (next i)).head (hpaths (next i))))
    (labels : List β) (orbits : List (β × Nat))
    (hperiods : ∀ orbit ∈ orbits, 0 < orbit.2 ∧ advance next orbit.1 orbit.2 = orbit.1)
    (hpartition : (orbits.flatMap (fun orbit => orbitLabels next orbit.1 orbit.2)).Perm labels) :
    ∃ trails : List (List (Row α)),
      (∀ trail ∈ trails, ClosedTrail trail) ∧
      trails.flatten.Perm (labels.flatMap paths) ∧ trails.length = orbits.length := by
  refine ⟨orbits.map (fun orbit => orbitRows paths next orbit.1 orbit.2), ?_, ?_, by simp⟩
  · intro trail ht
    obtain ⟨orbit, ho, rfl⟩ := List.mem_map.mp ht
    exact orbitRows_closedTrail_of_endpoints paths next hpaths hinternal hboundary
      orbit.1 (hperiods orbit ho).1 (hperiods orbit ho).2
  · have hp := hpartition.flatMap_right paths
    rw [List.flatMap_assoc] at hp
    exact hp

end SuperpermutationUpperBound.Transport
