import SuperpermutationUpperBound.CircleTransport.Tracks
import SuperpermutationUpperBound.Assembly.TrailWords

/-! Occurrence inventory, closure, and signed winding for the prescribed
single-lap transport tracks used in the circle-cover induction. -/
namespace SuperpermutationUpperBound.CircleTransport
open Transport
variable {α : Type}

/-- All source ports use each local replacement row occurrence exactly once. -/
theorem transport_port_inventory (r : Row α) (newOrd : α) (h : Nat)
    (hn : 3 ≤ h + 1) (hbase : r.base.length = h + 1) :
    ((List.finRange h).flatMap (fun p => Transport.portPath r newOrd p.val)).Perm
      (Transport.rows r newOrd) := by
  have he := Transport.portPaths_flatten_perm r newOrd (by omega)
  rw [hbase] at he
  have hrewrite : (List.finRange h).flatMap (fun p => Transport.portPath r newOrd p.val) =
      ((List.range h).map (Transport.portPath r newOrd)).flatten := by
    rw [← map_val_finRange h, List.map_map]
    rfl
  rw [hrewrite]
  exact he

/-- Inventory of one transport track per initial port, retaining repeated values. -/
theorem transportWalk_inventory (rs : List (Row α)) (newOrd : α) (h : Nat)
    (hn : 3 ≤ h + 1) (hlen : ∀ r ∈ rs, r.base.length = h + 1) :
    ((List.finRange h).flatMap (fun p => transportWalk rs newOrd p.val)).Perm
      (Transport.packingRows rs newOrd) := by
  induction rs with
  | nil => simp [transportWalk, Transport.packingRows]
  | cons r rs ih =>
    have hr := hlen r (by simp)
    have ht := ih (fun r hr => hlen r (List.mem_cons_of_mem _ hr))
    have hreindex := (finRange_map_perm (portPerm (h + 1) hn r)).flatMap_right
      (fun p => transportWalk rs newOrd p.val)
    simp only [List.flatMap_map, portPerm_val_eq_portTarget (h + 1) hn r hr] at hreindex
    change ((List.finRange h).flatMap (fun p => Transport.portPath r newOrd p.val ++
      transportWalk rs newOrd (portTarget r p.val))).Perm
      (Transport.rows r newOrd ++ Transport.packingRows rs newOrd)
    exact (List.flatMap_append_perm _ _ _).symm.trans
      ((transport_port_inventory r newOrd h hn hr).append (hreindex.trans ht))

/-- Winding divisibility gives identity monodromy on every old transport port. -/
theorem completionExit_eq_self_of_winding (rs : List (Row α)) (h : Nat)
    (hn : 3 ≤ h + 1) (hlen : ∀ r ∈ rs, r.base.length = h + 1)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (hw : (h : Int) ∣ signedExcess rs) (p : Nat) (hp : p < h) :
    completionExit rs p = p := by
  have hh : 0 < h := by omega
  have hret := pairWalkPerm_eq_self_of_winding rs h hh hlen hkind hw (⟨p, hp⟩, ⟨0, by omega⟩)
  have he := congrArg Prod.fst (pairChart_pairWalkPerm rs h hh (⟨p, hp⟩, ⟨0, by omega⟩))
  rw [hret] at he
  have he' : (oldWalkPerm h hh rs ⟨p, hp⟩).val = p := (congrArg Fin.val he).symm
  exact (completionExit_eq_oldWalk rs h hn hlen hkind ⟨p, hp⟩).trans he'

/-- The local port representative corrections telescope along one literal track. -/
theorem transportWalk_winding_ledger (rs : List (Row α)) (newOrd : α) (h : Nat)
    (hn : 3 ≤ h + 1) (hlen : ∀ r ∈ rs, r.base.length = h + 1)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (p : Nat) (hp : p < h) :
    (h : Int) * ((transportWalk rs newOrd p).map delta).sum =
      ((h + 1 : Nat) : Int) * (rs.map delta).sum - ((completionExit rs p : Int) - (p : Int)) := by
  induction rs generalizing p with
  | nil => simp [transportWalk, completionExit]
  | cons r rs ih =>
    have hr := hlen r (by simp)
    have hk := hkind r (by simp)
    have hlocal := portPath_local_winding r newOrd p (by omega) hk (by omega)
    rw [hr] at hlocal
    have hp' : portTarget r p < h := by
      have hp' := portTarget_lt (r := r) (by omega) p
      simpa only [hr, Nat.add_sub_cancel] using hp'
    have ht := ih (fun r hr => hlen r (by simp [hr])) (fun r hr => hkind r (by simp [hr])) _ hp'
    simp only [transportWalk, List.map_append, List.sum_append, List.map_cons,
      List.sum_cons, completionExit, mul_add]
    rw [show h + 1 - 1 = h by omega] at hlocal
    rw [hlocal, ht]
    ring

/-- The signed excess of each prescribed track is (h+1)/h times the old excess. -/
theorem transportWalk_signedExcess_mul (rs : List (Row α)) (newOrd : α) (h : Nat)
    (hn : 3 ≤ h + 1) (hlen : ∀ r ∈ rs, r.base.length = h + 1)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (hw : (h : Int) ∣ signedExcess rs) (p : Nat) (hp : p < h) :
    (h : Int) * signedExcess (transportWalk rs newOrd p) =
      ((h + 1 : Nat) : Int) * signedExcess rs := by
  have he := transportWalk_winding_ledger rs newOrd h hn hlen hkind p hp
  rw [completionExit_eq_self_of_winding rs h hn hlen hkind hw p hp, sub_self, sub_zero] at he
  rw [signedExcess_eq_neg_sum_delta, signedExcess_eq_neg_sum_delta]
  rw [mul_neg, mul_neg, he]

/-- Each next-stage literal track has the winding divisibility required to
split again at every initial port. The old signed excess may have either sign. -/
theorem transportWalk_winding_divisible (rs : List (Row α)) (newOrd : α) (h : Nat)
    (hn : 3 ≤ h + 1) (hlen : ∀ r ∈ rs, r.base.length = h + 1)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (hw : (h : Int) ∣ signedExcess rs) (p : Nat) (hp : p < h) :
    ((h + 1 : Nat) : Int) ∣ signedExcess (transportWalk rs newOrd p) := by
  have he := transportWalk_signedExcess_mul rs newOrd h hn hlen hkind hw p hp
  obtain ⟨a, ha⟩ := hw
  refine ⟨a, ?_⟩
  apply mul_left_cancel₀ (a := (h : Int)) (by omega)
  rw [he, ha]
  ring

theorem transportWalk_nonempty (rs : List (Row α)) (final : α) (q : Nat) (hne : rs ≠ []) :
    transportWalk rs final q ≠ [] := by
  cases rs with
  | nil => exact False.elim (hne rfl)
  | cons r rest =>
    intro heq
    exact Transport.portPath_nonempty r final q (List.append_eq_nil_iff.mp heq).1

theorem transportWalk_head (rs : List (Row α)) (hne : rs ≠ []) (final : α) (n q : Nat)
    (hn : 3 ≤ n) (hq : q < n - 1)
    (hbase : ∀ r ∈ rs, r.base.length = n)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2) :
    ((transportWalk rs final q).head (transportWalk_nonempty rs final q hne)).head =
      insertLetter (rs.head hne).head final q := by
  cases rs with
  | nil => exact False.elim (hne rfl)
  | cons r rest =>
    have hr := hbase r (by simp)
    simp only [transportWalk, List.head_append_of_ne_nil
      (Transport.portPath_nonempty r final q), List.head_cons]
    exact Transport.portPath_head final (by omega) (hkind r (by simp)) (by omega)

theorem transportWalk_last_tail (rs : List (Row α)) (hne : rs ≠ []) (final : α) (n q : Nat)
    (hn : 3 ≤ n) (hq : q < n - 1)
    (hbase : ∀ r ∈ rs, r.base.length = n)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2) :
    ((transportWalk rs final q).getLast (transportWalk_nonempty rs final q hne)).tail =
      insertLetter (rs.getLast hne).tail final (completionExit rs q) := by
  cases rs with
  | nil => exact False.elim (hne rfl)
  | cons r rest =>
    induction rest generalizing r q with
    | nil =>
      have hr := hbase r (by simp)
      simp only [transportWalk, List.append_nil, completionExit, List.getLast_singleton]
      exact Transport.portPath_last_tail final (by omega) (hkind r (by simp)) (by omega)
    | cons a rest ih =>
      have hr := hbase r (by simp)
      have hq' : portTarget r q < n - 1 := by
        rw [← hr]
        exact portTarget_lt (by omega) q
      have hne' : a :: rest ≠ [] := by simp
      have hlast := ih (portTarget r q) hq' a hne'
        (fun b hb => hbase b (by simp [hb])) (fun b hb => hkind b (by simp [hb]))
      change ((Transport.portPath r final q ++ transportWalk (a :: rest) final (portTarget r q)).getLast _).tail =
        insertLetter ((a :: rest).getLast hne').tail final (completionExit (a :: rest) (portTarget r q))
      rw [List.getLast_append_of_ne_nil _ (transportWalk_nonempty (a :: rest) final (portTarget r q) hne')]
      exact hlast

theorem transportWalk_internal (rs : List (Row α)) (hne : rs ≠ []) (final : α) (n q : Nat)
    (hn : 3 ≤ n) (hq : q < n - 1)
    (hbase : ∀ r ∈ rs, r.base.length = n)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (hchain : RowTrailCompatible (rs.head hne) rs.tail) :
    RowTrailCompatible
      ((transportWalk rs final q).head (transportWalk_nonempty rs final q hne))
      (transportWalk rs final q).tail := by
  cases rs with
  | nil => exact False.elim (hne rfl)
  | cons r rest =>
    induction rest generalizing r q with
    | nil =>
      have hr := hbase r (by simp)
      simpa only [transportWalk, List.append_nil] using
        Transport.portPath_internal r final q (by omega)
    | cons a rest ih =>
      have hr := hbase r (by simp)
      have hq' : portTarget r q < n - 1 := by
        rw [← hr]
        exact portTarget_lt (by omega) q
      have hne' : a :: rest ≠ [] := by simp
      have hb' := fun b (hb : b ∈ a :: rest) => hbase b (List.mem_cons_of_mem _ hb)
      have hk' := fun b (hb : b ∈ a :: rest) => hkind b (List.mem_cons_of_mem _ hb)
      have hi := ih (portTarget r q) hq' a hne' hb' hk' hchain.2
      apply compatible_nonempty_append _ _ (Transport.portPath_nonempty r final q)
        (transportWalk_nonempty (a :: rest) final (portTarget r q) hne')
        (Transport.portPath_internal r final q (by omega)) hi
      change ((Transport.portPath r final q).getLast _).tail =
        ((transportWalk (a :: rest) final (portTarget r q)).head _).head
      rw [Transport.portPath_last_tail final (by omega) (hkind r (by simp)) (by omega),
        transportWalk_head _ hne' final n (portTarget r q) hn hq' hb' hk']
      exact congrArg (fun u => insertLetter u final (portTarget r q)) hchain.1


theorem closedTrail_last_compatible_head {rs : List (Row α)} (hc : ClosedTrail rs) :
    (rs.getLast hc.1).Compatible (rs.head hc.1) := by
  have hlen : 0 < rs.length := List.length_pos_iff.mpr hc.1
  have he := closedTrail_getElem_compatible hc ⟨rs.length - 1, by omega⟩
  simp only [Nat.sub_add_cancel (by omega : 1 ≤ rs.length), Nat.mod_self] at he
  rw [List.getLast_eq_getElem, List.head_eq_getElem]
  exact he

/-- Each prescribed single-lap track is closed when the old winding is divisible
by the number of source ports. The proof uses literal heads and tails. -/
theorem transportWalk_closedTrail {rs : List (Row α)} (hc : ClosedTrail rs)
    (newOrd : α) (h : Nat) (hn : 3 ≤ h + 1)
    (hlen : ∀ r ∈ rs, r.base.length = h + 1)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (hw : (h : Int) ∣ signedExcess rs) (p : Nat) (hp : p < h) :
    ClosedTrail (transportWalk rs newOrd p) := by
  have hne := transportWalk_nonempty rs newOrd p hc.1
  have hchain : RowTrailCompatible (rs.head hc.1) rs.tail := by
    cases rs with
    | nil => exact False.elim (hc.1 rfl)
    | cons r rs => exact closedTrail_internal hc
  have hi := transportWalk_internal rs hc.1 newOrd (h + 1) p hn (by omega) hlen hkind hchain
  have hb : ((transportWalk rs newOrd p).getLast hne).Compatible
      ((transportWalk rs newOrd p).head hne) := by
    change _ = _
    rw [transportWalk_last_tail rs hc.1 newOrd (h + 1) p hn (by omega) hlen hkind,
      transportWalk_head rs hc.1 newOrd (h + 1) p hn (by omega) hlen hkind,
      completionExit_eq_self_of_winding rs h hn hlen hkind hw p hp,
      closedTrail_last_compatible_head hc]
  have hr := pathRunsTo_of_path_spec _ _ hne hi hb
  obtain ⟨a, as, he⟩ := List.exists_cons_of_ne_nil hne
  simp only [he, List.head_cons] at hr
  rw [he]
  exact closedTrail_of_pathRunsTo hr

/-- The complete literal-track step needed by the circle induction. -/
theorem transportWalk_family_step {rs : List (Row α)} (hc : ClosedTrail rs)
    (newOrd : α) (h : Nat) (hn : 3 ≤ h + 1)
    (hlen : ∀ r ∈ rs, r.base.length = h + 1)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (hw : (h : Int) ∣ signedExcess rs) :
    let tracks := (List.finRange h).map (fun p => transportWalk rs newOrd p.val)
    (∀ t ∈ tracks, ClosedTrail t ∧ ((h + 1 : Nat) : Int) ∣ signedExcess t) ∧
      tracks.flatten.Perm (Transport.packingRows rs newOrd) ∧ tracks.length = h := by
  refine ⟨?_, transportWalk_inventory rs newOrd h hn hlen, ?_⟩
  · intro t ht
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp ht
    exact ⟨transportWalk_closedTrail hc newOrd h hn hlen hkind hw p.val p.isLt,
      transportWalk_winding_divisible rs newOrd h hn hlen hkind hw p.val p.isLt⟩
  · simp

/-- A row occurrence in any validly indexed track belongs to the prescribed
transport replacement list, allowing the existing alphabet/validity lemmas to apply. -/
theorem transportWalk_subset_packingRows (rs : List (Row α)) (newOrd : α) (h : Nat)
    (hn : 3 ≤ h + 1) (hlen : ∀ r ∈ rs, r.base.length = h + 1)
    (p : Nat) (hp : p < h) {t : Row α} (ht : t ∈ transportWalk rs newOrd p) :
    t ∈ Transport.packingRows rs newOrd := by
  apply (transportWalk_inventory rs newOrd h hn hlen).mem_iff.mp
  exact List.mem_flatMap.mpr ⟨⟨p, hp⟩, List.mem_finRange _, ht⟩

end SuperpermutationUpperBound.CircleTransport
