import SuperpermutationUpperBound.CyclicBlocks

/-!
The insertion blocks partition satellite-containing permutations by the cyclic
class obtained after deleting the satellite. The proofs concern arbitrary
literal lists; they do not rely on finite enumeration or external counts.
-/

namespace SuperpermutationUpperBound

variable {α : Type u}

/-- A full insertion block includes every gap of a cyclic base and every
literal rotation of each resulting satellite-containing cyclic class.
-/
def InInsertionBlock (s : α) (x p : List α) : Prop :=
  ∃ j : Fin x.length, CyclicEq (rot x j.val ++ [s]) p

theorem InInsertionBlock.congr_base {s : α} {x y p : List α}
    (hxy : CyclicEq x y) : InInsertionBlock s x p ↔ InInsertionBlock s y p :=
  cyclicEq_insertion_exists_iff hxy s

theorem InInsertionBlock.perm {s : α} {x p : List α}
    (h : InInsertionBlock s x p) : p.Perm (x ++ [s]) := by
  obtain ⟨j, hj⟩ := h
  exact hj.perm.symm.trans ((rot_perm x j.val).append_right [s])

theorem InInsertionBlock.length_eq {s : α} {x p : List α}
    (h : InInsertionBlock s x p) : p.length = x.length + 1 := by
  simpa using h.perm.length_eq

theorem InInsertionBlock.cyclicEq_eraseSatellite [DecidableEq α]
    {s : α} {x p : List α} (h : InInsertionBlock s x p)
    (hs : s ∉ x) : CyclicEq x (eraseSatellite s p) := by
  obtain ⟨j, hj⟩ := h
  have hx : x ≠ [] := List.length_pos_iff.mp (Nat.zero_lt_of_lt j.isLt)
  have hsr : s ∉ rot x j.val := fun hm => hs ((rot_perm x j.val).mem_iff.mp hm)
  have hr : rot x j.val ≠ [] := by
    apply List.length_pos_iff.mp
    simpa only [rot_length] using List.length_pos_iff.mpr hx
  have he : eraseSatellite s (rot x j.val ++ [s]) ≠ [] := by
    simpa [hsr] using hr
  have hd : CyclicEq (rot x j.val) (eraseSatellite s p) := by
    simpa [hsr] using hj.eraseSatellite s he
  exact (CyclicEq.of_rot hx j.val).trans hd

/-- Constructive first-occurrence splitting, using the available decidable
equality instead of the classical splitter from the standard library.
-/
private theorem split_satellite [DecidableEq α] {s : α} {p : List α}
    (hs : s ∈ p) : ∃ a b, p = a ++ s :: b ∧ s ∉ a := by
  induction p with
  | nil => cases hs
  | cons t p ih =>
      by_cases ht : t = s
      · subst t
        exact ⟨[], p, rfl, by simp⟩
      · have hsp : s ∈ p := (List.mem_cons.mp hs).resolve_left (Ne.symm ht)
        obtain ⟨a, b, he, hn⟩ := ih hsp
        refine ⟨t :: a, b, by simp only [List.cons_append, he], ?_⟩
        intro hm
        rcases List.mem_cons.mp hm with heq | hm
        · exact ht heq.symm
        · exact hn hm

/-- Once a satellite is unique, cutting immediately after it gives an entry
whose base is a literal rotation of the deleted word.
-/
theorem inInsertionBlock_of_cyclicEq_eraseSatellite [DecidableEq α]
    {s : α} {x p : List α} (hp : p.Nodup) (hsp : s ∈ p)
    (h : CyclicEq x (eraseSatellite s p)) : InInsertionBlock s x p := by
  obtain ⟨a, b, rfl, hsa⟩ := split_satellite hsp
  have hsb : s ∉ b := (List.nodup_cons.mp (List.nodup_append.mp hp).2.1).1
  have he : eraseSatellite s (a ++ s :: b) = a ++ b := by
    change (a ++ s :: b).filter (fun z => decide (z ≠ s)) = a ++ b
    rw [List.filter_append]
    simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
      ↓reduceIte]
    change eraseSatellite s a ++ eraseSatellite s b = a ++ b
    rw [eraseSatellite_eq_self hsa, eraseSatellite_eq_self hsb]
  rw [he] at h
  obtain ⟨j, hj⟩ := h.rot_reindex a.length
  rw [rot_append_length] at hj
  refine ⟨j, ?_⟩
  have hn : (a ++ [s]) ++ b ≠ [] := by simp
  have hc := CyclicEq.of_rot hn (a ++ [s]).length
  rw [rot_append_length] at hc
  have ht : CyclicEq ((b ++ a) ++ [s]) (a ++ s :: b) := by
    simpa only [List.append_assoc, List.singleton_append] using hc.symm
  exact Eq.mp (congrArg (fun z => CyclicEq (z ++ [s]) (a ++ s :: b)) hj) ht

/-- Exact semantic deletion characterization of an insertion block. -/
theorem inInsertionBlock_iff_cyclicEq_eraseSatellite [DecidableEq α]
    {s : α} {x p : List α} (hp : p.Nodup) (hsp : s ∈ p) (hsx : s ∉ x) :
    InInsertionBlock s x p ↔ CyclicEq x (eraseSatellite s p) :=
  ⟨fun h => h.cyclicEq_eraseSatellite hsx,
    inInsertionBlock_of_cyclicEq_eraseSatellite hp hsp⟩

/-- Two insertion blocks sharing a word have the same cyclic base block. -/
theorem InInsertionBlock.unique_base [DecidableEq α] {s : α} {x y p : List α}
    (hx : InInsertionBlock s x p) (hy : InInsertionBlock s y p)
    (hsx : s ∉ x) (hsy : s ∉ y) : CyclicEq x y :=
  (hx.cyclicEq_eraseSatellite hsx).trans (hy.cyclicEq_eraseSatellite hsy).symm

theorem eraseSatellite_perm_of_perm_append_satellite [DecidableEq α]
    {s : α} {alphabet p : List α} (hp : p.Perm (alphabet ++ [s]))
    (hs : s ∉ alphabet) : (eraseSatellite s p).Perm alphabet := by
  have he := hp.filter (fun a => decide (a ≠ s))
  change (eraseSatellite s p).Perm (eraseSatellite s (alphabet ++ [s])) at he
  simpa [hs] using he

/-- Every permutation over a nonempty ordinary alphabet plus a fresh satellite
belongs to a block with an ordinary permutation as its base.
-/
theorem exists_inInsertionBlock_of_perm_append_satellite [DecidableEq α]
    {s : α} {alphabet p : List α} (ha : alphabet.Nodup) (hne : alphabet ≠ [])
    (hs : s ∉ alphabet) (hp : p.Perm (alphabet ++ [s])) :
    ∃ x : List α, x.Perm alphabet ∧ InInsertionBlock s x p := by
  have hpa : (alphabet ++ [s]).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨ha, by simp, ?_⟩
    intro a ham b hbm hab
    have hb : b = s := List.mem_singleton.mp hbm
    subst b
    subst a
    exact hs ham
  have hpn : p.Nodup := hp.symm.nodup hpa
  have hsp : s ∈ p := hp.mem_iff.mpr (by simp)
  have he := eraseSatellite_perm_of_perm_append_satellite hp hs
  have hen : eraseSatellite s p ≠ [] := by
    apply List.length_pos_iff.mp
    rw [he.length_eq]
    exact List.length_pos_iff.mpr hne
  exact ⟨eraseSatellite s p, he,
    inInsertionBlock_of_cyclicEq_eraseSatellite hpn hsp (CyclicEq.refl hen)⟩

/-- Every permutation assigned to a valid row belongs to its full insertion
block, including when the row leaves some entries for later completion.
-/
theorem Row.Assigned.inInsertionBlock {α : Type} {r : Row α} {p : List α}
    (hp : r.Assigned p) (hr : r.Valid) : InInsertionBlock r.satellite r.base p := by
  obtain ⟨j, hj, i, hi, rfl⟩ := hp
  refine ⟨⟨j, Nat.lt_of_lt_of_le hj hr.2.2.2⟩, ⟨⟨i, ?_⟩, rfl⟩⟩
  simpa [rot_length] using hi

/-- A full row assigns exactly every permutation in its insertion block. -/
theorem Row.assigned_iff_inInsertionBlock_of_full {α : Type} {r : Row α}
    {p : List α} (hr : r.Valid) (hfull : r.visible = r.base.length) :
    r.Assigned p ↔ InInsertionBlock r.satellite r.base p := by
  constructor
  · intro hp
    exact hp.inInsertionBlock hr
  · intro ⟨j, i, hi⟩
    refine ⟨j.val, ?_, i.val, ?_, hi.symm⟩
    · simpa only [hfull] using j.isLt
    · simpa [rot_length] using i.isLt

end SuperpermutationUpperBound
