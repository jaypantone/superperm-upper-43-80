import SuperpermutationUpperBound.CircleTransport.TwoInsertion
import SuperpermutationUpperBound.Completion.Paths
import SuperpermutationUpperBound.Transport.Closed
import SuperpermutationUpperBound.Transport.Winding

/-! Literal composition of transport paths and completion paths. -/
namespace SuperpermutationUpperBound.CircleTransport

open Transport
variable {α : Type}

/-- Complete each row on a transported local path, propagating the completion
port across every intermediate row occurrence. -/
def completionWalk (rs : List (Row α)) (final : α) (q : Nat) : List (Row α) :=
  match rs with
  | [] => []
  | r :: rest => Completion.portPath r final q ++ completionWalk rest final (portTarget r q)

/-- The completion port after traversing the whole transported path. -/
def completionExit (rs : List (Row α)) (q : Nat) : Nat :=
  match rs with
  | [] => q
  | r :: rest => completionExit rest (portTarget r q)

/-- Actual transport-then-completion path at a pair of tagged input ports. -/
def pairPath (r : Row α) (newOrd final : α) (p q : Nat) : List (Row α) :=
  completionWalk (Transport.portPath r newOrd p) final q

/-- Every input row has a nonempty literal completion path. -/
theorem completionWalk_nonempty (rs : List (Row α)) (final : α) (q : Nat) (hne : rs ≠ []) :
    completionWalk rs final q ≠ [] := by
  cases rs with
  | nil => exact False.elim (hne rfl)
  | cons r rest =>
    intro heq
    exact Completion.portPath_nonempty r final q (List.append_eq_nil_iff.mp heq).1

theorem pairPath_nonempty (r : Row α) (newOrd final : α) (p q : Nat) :
    pairPath r newOrd final p q ≠ [] :=
  completionWalk_nonempty _ final q (Transport.portPath_nonempty r newOrd p)

/-- Appending internally compatible nonempty paths requires only their one
literal interface equation. -/
theorem compatible_nonempty_append (left right : List (Row α))
    (hl : left ≠ []) (hr : right ≠ [])
    (hil : RowTrailCompatible (left.head hl) left.tail)
    (hir : RowTrailCompatible (right.head hr) right.tail)
    (hb : (left.getLast hl).Compatible (right.head hr)) :
    RowTrailCompatible ((left ++ right).head (by simp [hl])) (left ++ right).tail := by
  cases left with
  | nil => exact False.elim (hl rfl)
  | cons a rest =>
    cases right with
    | nil => exact False.elim (hr rfl)
    | cons b more =>
      exact (rowTrailCompatible_append_iff a b rest more).mpr
        ⟨pathRunsTo_of_internal_and_last hil hb, hir⟩

theorem completionWalk_head (rs : List (Row α)) (hne : rs ≠ []) (final : α) (n q : Nat)
    (hn : 3 ≤ n) (hq : q < n - 1)
    (hbase : ∀ r ∈ rs, r.base.length = n)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2) :
    ((completionWalk rs final q).head (completionWalk_nonempty rs final q hne)).head =
      insertLetter (rs.head hne).head final q := by
  cases rs with
  | nil => exact False.elim (hne rfl)
  | cons r rest =>
    have hr := hbase r (by simp)
    simp only [completionWalk, List.head_append_of_ne_nil
      (Completion.portPath_nonempty r final q), List.head_cons]
    exact Completion.portPath_head final (by omega) (hkind r (by simp)) (by omega)

theorem completionWalk_last_tail (rs : List (Row α)) (hne : rs ≠ []) (final : α) (n q : Nat)
    (hn : 3 ≤ n) (hq : q < n - 1)
    (hbase : ∀ r ∈ rs, r.base.length = n)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2) :
    ((completionWalk rs final q).getLast (completionWalk_nonempty rs final q hne)).tail =
      insertLetter (rs.getLast hne).tail final (completionExit rs q) := by
  cases rs with
  | nil => exact False.elim (hne rfl)
  | cons r rest =>
    induction rest generalizing r q with
    | nil =>
      have hr := hbase r (by simp)
      simp only [completionWalk, List.append_nil, completionExit, List.getLast_singleton]
      exact Completion.portPath_last_tail final (by omega) (hkind r (by simp)) (by omega)
    | cons a rest ih =>
      have hr := hbase r (by simp)
      have hq' : portTarget r q < n - 1 := by
        rw [← hr]
        exact portTarget_lt (by omega) q
      have hne' : a :: rest ≠ [] := by simp
      have hlast := ih (portTarget r q) hq' a hne'
        (fun b hb => hbase b (by simp [hb])) (fun b hb => hkind b (by simp [hb]))
      change ((Completion.portPath r final q ++ completionWalk (a :: rest) final (portTarget r q)).getLast _).tail =
        insertLetter ((a :: rest).getLast hne').tail final (completionExit (a :: rest) (portTarget r q))
      rw [List.getLast_append_of_ne_nil _ (completionWalk_nonempty (a :: rest) final (portTarget r q) hne')]
      exact hlast

theorem completionWalk_internal (rs : List (Row α)) (hne : rs ≠ []) (final : α) (n q : Nat)
    (hn : 3 ≤ n) (hq : q < n - 1)
    (hbase : ∀ r ∈ rs, r.base.length = n)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (hchain : RowTrailCompatible (rs.head hne) rs.tail) :
    RowTrailCompatible
      ((completionWalk rs final q).head (completionWalk_nonempty rs final q hne))
      (completionWalk rs final q).tail := by
  cases rs with
  | nil => exact False.elim (hne rfl)
  | cons r rest =>
    induction rest generalizing r q with
    | nil =>
      have hr := hbase r (by simp)
      simpa only [completionWalk, List.append_nil] using
        Completion.portPath_internal final q (by omega) (hkind r (by simp))
    | cons a rest ih =>
      have hr := hbase r (by simp)
      have hq' : portTarget r q < n - 1 := by
        rw [← hr]
        exact portTarget_lt (by omega) q
      have hne' : a :: rest ≠ [] := by simp
      have hb' := fun b (hb : b ∈ a :: rest) => hbase b (List.mem_cons_of_mem _ hb)
      have hk' := fun b (hb : b ∈ a :: rest) => hkind b (List.mem_cons_of_mem _ hb)
      have hi := ih (portTarget r q) hq' a hne' hb' hk' hchain.2
      apply compatible_nonempty_append _ _ (Completion.portPath_nonempty r final q)
        (completionWalk_nonempty (a :: rest) final (portTarget r q) hne')
        (Completion.portPath_internal final q (by omega) (hkind r (by simp))) hi
      change ((Completion.portPath r final q).getLast _).tail =
        ((completionWalk (a :: rest) final (portTarget r q)).head _).head
      rw [Completion.portPath_last_tail final (by omega) (hkind r (by simp)) (by omega),
        completionWalk_head _ hne' final n (portTarget r q) hn hq' hb' hk']
      exact congrArg (fun u => insertLetter u final (portTarget r q)) hchain.1

/-- Every finite port bijection merely reorders the input occurrence labels. -/
theorem finRange_map_perm {N : Nat} (σ : Equiv.Perm (Fin N)) :
    ((List.finRange N).map σ).Perm (List.finRange N) := by
  apply perm_of_nodup_subset_length ((nodup_finRange N).map σ.injective)
    (fun i _ => List.mem_finRange i) (by simp)

theorem completion_port_inventory (r : Row α) (final : α) (n : Nat) (hn : 3 ≤ n)
    (hbase : r.base.length = n)
    (hkind : r.visible = r.base.length ∨ r.visible = r.base.length - 2) :
    ((List.finRange (n - 1)).flatMap (fun q => Completion.portPath r final q.val)).Perm
      (Completion.completeRows r final) := by
  have he := Completion.portPaths_flatten_perm final (by omega) hkind
  rw [hbase] at he
  have hrewrite : (List.finRange (n - 1)).flatMap (fun q => Completion.portPath r final q.val) =
      ((List.range (n - 1)).map (Completion.portPath r final)).flatten := by
    rw [← map_val_finRange (n - 1), List.map_map]
    rfl
  rw [hrewrite]
  exact he

/-- Reindexing later completion ports by their actual local bijections keeps
every completed row occurrence exactly once. -/
theorem completionWalk_inventory (rs : List (Row α)) (final : α) (n : Nat) (hn : 3 ≤ n)
    (hbase : ∀ r ∈ rs, r.base.length = n)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2) :
    ((List.finRange (n - 1)).flatMap (fun q => completionWalk rs final q.val)).Perm
      (rs.flatMap (fun r => Completion.completeRows r final)) := by
  induction rs with
  | nil => simp [completionWalk]
  | cons r rest ih =>
    have hr := hbase r (by simp)
    have hk := hkind r (by simp)
    have ht := ih (fun r hr => hbase r (List.mem_cons_of_mem _ hr))
      (fun r hr => hkind r (List.mem_cons_of_mem _ hr))
    have hreindex := (finRange_map_perm (portPerm n hn r)).flatMap_right
      (fun q => completionWalk rest final q.val)
    simp only [List.flatMap_map,
      portPerm_val_eq_portTarget n hn r hr] at hreindex
    change ((List.finRange (n - 1)).flatMap
      (fun q => Completion.portPath r final q.val ++ completionWalk rest final (portTarget r q.val))).Perm
        (Completion.completeRows r final ++ rest.flatMap (fun r => Completion.completeRows r final))
    exact (List.flatMap_append_perm _ _ _).symm.trans
      ((completion_port_inventory r final n hn hr hk).append (hreindex.trans ht))

/-- Transported local rows remain full or deficit two and increase the
ordinary base length by one. -/
theorem transportPath_metadata (r : Row α) (newOrd : α) (p : Nat)
    (hn : 3 ≤ r.base.length)
    (hkind : r.visible = r.base.length ∨ r.visible = r.base.length - 2) :
    ∀ s ∈ Transport.portPath r newOrd p,
      s.base.length = r.base.length + 1 ∧
        (s.visible = s.base.length ∨ s.visible = s.base.length - 2) := by
  rcases hkind with hf | hs
  · simp only [Transport.portPath, if_pos hf, fullPathAt]
    split <;> simp [fullAt]
  · have hf : r.visible ≠ r.base.length := by omega
    simp only [Transport.portPath, if_neg hf, shortPathAt]
    have he : r.base.length + 1 - 2 = r.base.length - 1 := by omega
    split <;> simp [shortAt, shortLast, he]

/-- Propagating completion ports through actual full/short rows sums their
signed displacements, regardless of repeated literal endpoints. -/
theorem completionExit_eq_shift (rs : List (Row α)) (h : Nat) (hn : 3 ≤ h + 2)
    (hbase : ∀ r ∈ rs, r.base.length = h + 2)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (q : Fin (h + 1)) :
    completionExit rs q.val = (shiftPort h (rs.map delta).sum q).val := by
  induction rs generalizing q with
  | nil => simp [completionExit]
  | cons r rest ih =>
    have hr := hbase r (by simp)
    have hk := hkind r (by simp)
    let q' : Fin (h + 1) := portPerm (h + 2) hn r q
    have hv : q'.val = portTarget r q.val := portPerm_val_eq_portTarget (h + 2) hn r hr q
    have he := ih (fun r hr => hbase r (List.mem_cons_of_mem _ hr))
      (fun r hr => hkind r (List.mem_cons_of_mem _ hr)) q'
    change completionExit rest (portTarget r q.val) = _
    rw [← hv, he]
    have hq' : q' = shiftPort h (delta r) q := portPerm_eq_shiftPort_delta h hn r hr hk q
    rw [hq', shiftPort_add, List.map_cons, List.sum_cons]

/-- All pair-input paths together exhaust every actual completed transport
row, with occurrence multiplicity preserved. -/
theorem pairPath_inventory (r : Row α) (newOrd final : α) (n : Nat)
    (hn : 3 ≤ n) (hbase : r.base.length = n)
    (hkind : r.visible = r.base.length ∨ r.visible = r.base.length - 2) :
    ((List.finRange (n - 1)).flatMap (fun p => (List.finRange n).flatMap
      (fun q => pairPath r newOrd final p.val q.val))).Perm
      ((Transport.rows r newOrd).flatMap (fun s => Completion.completeRows s final)) := by
  have hinner : ∀ p : Fin (n - 1),
      ((List.finRange n).flatMap (fun q => pairPath r newOrd final p.val q.val)).Perm
        ((Transport.portPath r newOrd p.val).flatMap (fun s => Completion.completeRows s final)) := by
    intro p
    have hm := transportPath_metadata r newOrd p.val (by omega) hkind
    have he := completionWalk_inventory (Transport.portPath r newOrd p.val) final (n + 1)
      (by omega) (fun s hs => (hm s hs).1.trans (congrArg (fun a => a + 1) hbase))
      (fun s hs => (hm s hs).2)
    exact he
  have hp := flatMap_perm_of_pointwise (List.finRange (n - 1)) _ _ (fun p _ => hinner p)
  have hinv := Transport.portPaths_flatten_perm r newOrd (by omega)
  rw [hbase] at hinv
  have hrewrite : (List.finRange (n - 1)).flatMap (fun p => Transport.portPath r newOrd p.val) =
      ((List.range (n - 1)).map (Transport.portPath r newOrd)).flatten := by
    rw [← map_val_finRange (n - 1), List.map_map]
    rfl
  rw [← hrewrite] at hinv
  have he := hinv.flatMap_right (fun s => Completion.completeRows s final)
  rw [List.flatMap_assoc] at he
  exact hp.trans he

theorem pairPath_internal (r : Row α) (newOrd final : α) (n p q : Nat)
    (hn : 3 ≤ n) (hbase : r.base.length = n)
    (hkind : r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (hq : q < n) :
    RowTrailCompatible
      ((pairPath r newOrd final p q).head (pairPath_nonempty r newOrd final p q))
      (pairPath r newOrd final p q).tail := by
  have hm := transportPath_metadata r newOrd p (by omega) hkind
  exact completionWalk_internal _ (Transport.portPath_nonempty r newOrd p) final (n + 1) q
    (by omega) (by omega)
    (fun s hs => (hm s hs).1.trans (congrArg (fun a => a + 1) hbase))
    (fun s hs => (hm s hs).2) (Transport.portPath_internal r newOrd p (by omega))

/-- Literal pair-path endpoints before identifying the algebraic pair map. -/
theorem pairPath_endpoints (r : Row α) (newOrd final : α) (n p q : Nat)
    (hn : 3 ≤ n) (hbase : r.base.length = n)
    (hkind : r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (hp : p < n - 1) (hq : q < n) :
    ((pairPath r newOrd final p q).head (pairPath_nonempty r newOrd final p q)).head =
        insertLetter (insertLetter r.head newOrd p) final q ∧
    ((pairPath r newOrd final p q).getLast (pairPath_nonempty r newOrd final p q)).tail =
        insertLetter (insertLetter r.tail newOrd (portTarget r p)) final
          (completionExit (Transport.portPath r newOrd p) q) := by
  have hm := transportPath_metadata r newOrd p (by omega) hkind
  have hb := fun s hs => (hm s hs).1.trans (congrArg (fun a => a + 1) hbase)
  have hk := fun s hs => (hm s hs).2
  constructor
  · have he := completionWalk_head _ (Transport.portPath_nonempty r newOrd p) final (n + 1) q
      (by omega) (by omega) hb hk
    rw [Transport.portPath_head newOrd (by omega) hkind (by omega)] at he
    exact he
  · have he := completionWalk_last_tail _ (Transport.portPath_nonempty r newOrd p) final (n + 1) q
      (by omega) (by omega) hb hk
    rw [Transport.portPath_last_tail newOrd (by omega) hkind (by omega)] at he
    exact he

/-- The first insertion port of a full row follows the first coordinate of T. -/
theorem full_pair_first (r : Row α) (h : Nat) (hn : 3 ≤ h + 1)
    (hbase : r.base.length = h + 1) (hf : r.visible = r.base.length) (p : Fin h) :
    portTarget r p.val = (decrement h (by omega) p).val := by
  rw [decrement_val]
  by_cases hp : p.val = 0
  · rw [hp, portTarget_full_zero (by omega) hf]
    simp [hbase]
  · rw [portTarget_full_pos (by omega) hf (by omega) (by omega), if_neg hp]

/-- The first insertion port of a short row follows the first coordinate of T⁻¹. -/
theorem short_pair_first (r : Row α) (h : Nat) (hn : 3 ≤ h + 1)
    (hbase : r.base.length = h + 1) (hs : r.visible = r.base.length - 2) (p : Fin h) :
    portTarget r p.val = (rowIndexPerm h (by omega) p).val := by
  have hf : r.visible ≠ r.base.length := by omega
  have hf' : r.visible ≠ h + 1 := by omega
  simp [portTarget, hbase, hf', rowIndexPerm_val]

/-- Completing the actual full transport path gives exactly T's second
coordinate, including its doubled wraparound step. -/
theorem full_pair_second (r : Row α) (newOrd : α) (h : Nat) (hn : 3 ≤ h + 1)
    (hbase : r.base.length = h + 1) (hf : r.visible = r.base.length)
    (pq : Fin h × Fin (h + 1)) :
    completionExit (Transport.portPath r newOrd pq.1.val) pq.2.val =
      (twoInsertion h (by omega) pq).2.val := by
  have hm := transportPath_metadata r newOrd pq.1.val (by omega) (Or.inl hf)
  have he := completionExit_eq_shift (Transport.portPath r newOrd pq.1.val) h (by omega)
    (fun s hs => by have hl := (hm s hs).1; omega) (fun s hs => (hm s hs).2) pq.2
  have hd : delta r = -1 := delta_full (by simp [Row.charge, hf])
  rw [portPath_sum_delta r newOrd pq.1.val (by omega) (Or.inl hf), hd] at he
  rw [twoInsertion_snd]
  have hsum : ((Transport.portPath r newOrd pq.1.val).length : Int) * (-1) =
      if pq.1.val = 0 then -2 else -1 := by
    simp only [Transport.portPath, if_pos hf, fullPathAt]
    split <;> simp
  rw [hsum] at he
  exact he

/-- Completing the actual short transport path gives exactly T⁻¹'s second
coordinate, including its doubled last-port step. -/
theorem short_pair_second (r : Row α) (newOrd : α) (h : Nat) (hn : 3 ≤ h + 1)
    (hbase : r.base.length = h + 1) (hs : r.visible = r.base.length - 2)
    (pq : Fin h × Fin (h + 1)) :
    completionExit (Transport.portPath r newOrd pq.1.val) pq.2.val =
      ((twoInsertion h (by omega)).symm pq).2.val := by
  have hm := transportPath_metadata r newOrd pq.1.val (by omega) (Or.inr hs)
  have he := completionExit_eq_shift (Transport.portPath r newOrd pq.1.val) h (by omega)
    (fun s hs => by have hl := (hm s hs).1; omega) (fun s hs => (hm s hs).2) pq.2
  have hf : r.visible ≠ r.base.length := by omega
  have hc : r.charge = 2 := by unfold Row.charge; omega
  rw [portPath_sum_delta r newOrd pq.1.val (by omega) (Or.inr hs), delta_short hc] at he
  rw [twoInsertion_symm_snd]
  have hsum : ((Transport.portPath r newOrd pq.1.val).length : Int) * 1 =
      if pq.1.val = h - 1 then 2 else 1 := by
    simp only [Transport.portPath, if_neg hf, shortPathAt]
    by_cases hp : pq.1.val < r.base.length - 2
    · have hp' : pq.1.val ≠ h - 1 := by omega
      rw [if_pos hp]
      simp [hp']
    · have hp' : pq.1.val = h - 1 := by omega
      rw [if_neg hp]
      simp [hp']
  rw [hsum] at he
  exact he

/-- The combined local port permutation: full rows act by T and short rows
by its explicit inverse. -/
def pairRowPerm (r : Row α) (h : Nat) (hh : 0 < h) : Equiv.Perm (Fin h × Fin (h + 1)) :=
  if r.visible = r.base.length then twoInsertion h hh else (twoInsertion h hh).symm

/-- Actual pair paths have the literal double-insertion endpoints prescribed
by the algebraic pair-port permutation. -/
theorem pairPath_literal_endpoints (r : Row α) (newOrd final : α) (h : Nat)
    (hn : 3 ≤ h + 1) (hbase : r.base.length = h + 1)
    (hkind : r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (pq : Fin h × Fin (h + 1)) :
    ((pairPath r newOrd final pq.1.val pq.2.val).head
      (pairPath_nonempty r newOrd final pq.1.val pq.2.val)).head =
        insertLetter (insertLetter r.head newOrd pq.1.val) final pq.2.val ∧
    ((pairPath r newOrd final pq.1.val pq.2.val).getLast
      (pairPath_nonempty r newOrd final pq.1.val pq.2.val)).tail =
        insertLetter
          (insertLetter r.tail newOrd (pairRowPerm r h (by omega) pq).1.val)
          final (pairRowPerm r h (by omega) pq).2.val := by
  have he := pairPath_endpoints r newOrd final (h + 1) pq.1.val pq.2.val hn hbase hkind
    (by omega) pq.2.isLt
  refine ⟨he.1, ?_⟩
  rcases hkind with hf | hs
  · rw [full_pair_first r h hn hbase hf,
      full_pair_second r newOrd h hn hbase hf] at he
    simpa only [pairRowPerm, if_pos hf, twoInsertion_fst] using he.2
  · have hf : r.visible ≠ r.base.length := by omega
    rw [short_pair_first r h hn hbase hs,
      short_pair_second r newOrd h hn hbase hs] at he
    simpa only [pairRowPerm, if_neg hf, twoInsertion_symm_fst] using he.2

/-- Product indexing is equivalent to the nested inventory and makes every
pair of tagged insertion ports an explicit occurrence label. -/
theorem pairPath_product_inventory (r : Row α) (newOrd final : α) (n : Nat)
    (hn : 3 ≤ n) (hbase : r.base.length = n)
    (hkind : r.visible = r.base.length ∨ r.visible = r.base.length - 2) :
    (((List.finRange (n - 1)).product (List.finRange n)).flatMap
      (fun pq => pairPath r newOrd final pq.1.val pq.2.val)).Perm
      ((Transport.rows r newOrd).flatMap (fun s => Completion.completeRows s final)) := by
  simpa only [List.product, List.flatMap_assoc, List.flatMap_map, Function.comp_def]
    using pairPath_inventory r newOrd final n hn hbase hkind

end SuperpermutationUpperBound.CircleTransport
