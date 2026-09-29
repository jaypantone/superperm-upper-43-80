import SuperpermutationUpperBound.Foundation.Words

/-!
Literal overlap assembly. Equality of actual suffix and prefix lists, rather
than equality of cyclic classes, is what preserves both words under a join.
-/

namespace SuperpermutationUpperBound

variable {α : Type u}

/-- Join two literal words, retaining one copy of the specified overlap. -/
def overlapJoin (u v : List α) (h : Nat) : List α :=
  u ++ v.drop h

/-- The complete literal compatibility condition for an overlap of length `h`. -/
def OverlapCompatible (h : Nat) (u v : List α) : Prop :=
  h ≤ u.length ∧ h ≤ v.length ∧ u.drop (u.length - h) = v.take h

theorem overlapJoin_eq_take_append {u v : List α} {h : Nat}
    (hm : u.drop (u.length - h) = v.take h) :
    overlapJoin u v h = u.take (u.length - h) ++ v := by
  calc
    overlapJoin u v h =
        (u.take (u.length - h) ++ u.drop (u.length - h)) ++ v.drop h := by
      rw [List.take_append_drop]
      rfl
    _ = u.take (u.length - h) ++ (v.take h ++ v.drop h) := by
      rw [hm, List.append_assoc]
    _ = u.take (u.length - h) ++ v := by rw [List.take_append_drop]

theorem prefix_overlapJoin (u v : List α) (h : Nat) :
    u.IsPrefix (overlapJoin u v h) :=
  List.prefix_append u (v.drop h)

theorem suffix_overlapJoin {u v : List α} {h : Nat}
    (hm : u.drop (u.length - h) = v.take h) :
    v.IsSuffix (overlapJoin u v h) := by
  rw [overlapJoin_eq_take_append hm]
  exact List.suffix_append _ _

theorem infix_overlapJoin_left (u v : List α) (h : Nat) :
    u.IsInfix (overlapJoin u v h) :=
  (prefix_overlapJoin u v h).isInfix

theorem infix_overlapJoin_right {u v : List α} {h : Nat}
    (hm : u.drop (u.length - h) = v.take h) :
    v.IsInfix (overlapJoin u v h) :=
  (suffix_overlapJoin hm).isInfix

theorem infix_overlapJoin_of_left {p u v : List α} {h : Nat}
    (hp : p.IsInfix u) : p.IsInfix (overlapJoin u v h) :=
  hp.trans (infix_overlapJoin_left u v h)

theorem infix_overlapJoin_of_right {p u v : List α} {h : Nat}
    (hm : u.drop (u.length - h) = v.take h) (hp : p.IsInfix v) :
    p.IsInfix (overlapJoin u v h) :=
  hp.trans (infix_overlapJoin_right hm)

theorem length_overlapJoin_add {u v : List α} {h : Nat}
    (hv : h ≤ v.length) :
    (overlapJoin u v h).length + h = u.length + v.length := by
  simp only [overlapJoin, List.length_append, List.length_drop]
  omega

theorem length_overlapJoin {u v : List α} {h : Nat}
    (hv : h ≤ v.length) :
    (overlapJoin u v h).length = u.length + v.length - h := by
  have := length_overlapJoin_add (u := u) hv
  omega

/-- A convenient packaged two-word assembly theorem. -/
theorem overlapJoin_spec {u v : List α} {h : Nat}
    (hc : OverlapCompatible h u v) :
    u.IsInfix (overlapJoin u v h) ∧
    v.IsInfix (overlapJoin u v h) ∧
    (overlapJoin u v h).length + h = u.length + v.length :=
  ⟨infix_overlapJoin_left u v h, infix_overlapJoin_right hc.2.2,
    length_overlapJoin_add hc.2.1⟩

theorem take_overlapJoin {u v : List α} {h k : Nat} (hk : k ≤ u.length) :
    (overlapJoin u v h).take k = u.take k :=
  List.take_append_of_le_length hk

/-- A literal final tuple is unchanged when its containing word is a suffix. -/
theorem drop_length_sub_of_suffix {v w : List α} {k : Nat}
    (hs : v.IsSuffix w) (hk : k ≤ v.length) :
    w.drop (w.length - k) = v.drop (v.length - k) := by
  obtain ⟨a, rfl⟩ := hs
  rw [List.length_append]
  have he : a.length + v.length - k = a.length + (v.length - k) := by omega
  rw [he, List.drop_length_add_append]

theorem drop_length_sub_overlapJoin {u v : List α} {h k : Nat}
    (hm : u.drop (u.length - h) = v.take h) (hk : k ≤ v.length) :
    (overlapJoin u v h).drop ((overlapJoin u v h).length - k) =
      v.drop (v.length - k) :=
  drop_length_sub_of_suffix (suffix_overlapJoin hm) hk

/-- Literal compatibility of a nonempty trail, including endpoint-size bounds. -/
def CompatibleTrail (h : Nat) (first : List α) : List (List α) → Prop
  | [] => h ≤ first.length
  | next :: rest => OverlapCompatible h first next ∧ CompatibleTrail h next rest

/-- Spell a nonempty trail, retaining one copy of each common endpoint. -/
def overlapTrail (h : Nat) (first : List α) : List (List α) → List α
  | [] => first
  | next :: rest => overlapJoin first (overlapTrail h next rest) h

theorem prefix_overlapTrail (h : Nat) (first : List α) (rest : List (List α)) :
    first.IsPrefix (overlapTrail h first rest) := by
  cases rest with
  | nil => exact List.prefix_refl _
  | cons next rest => exact prefix_overlapJoin _ _ _

theorem take_overlapTrail {h k : Nat} {first : List α} (rest : List (List α))
    (hk : k ≤ first.length) :
    (overlapTrail h first rest).take k = first.take k := by
  cases rest with
  | nil => rfl
  | cons next rest => exact take_overlapJoin hk

theorem suffix_overlapTrail {h : Nat} {first : List α} {rest : List (List α)}
    (hc : CompatibleTrail h first rest) :
    (rest.getLastD first).IsSuffix (overlapTrail h first rest) := by
  induction rest generalizing first with
  | nil => exact List.suffix_refl _
  | cons next rest ih =>
      rw [List.getLastD_cons]
      apply (ih hc.2).trans
      apply suffix_overlapJoin
      rw [take_overlapTrail rest hc.1.2.1]
      exact hc.1.2.2

theorem drop_length_sub_overlapTrail {h k : Nat} {first : List α}
    {rest : List (List α)} (hc : CompatibleTrail h first rest)
    (hk : k ≤ (rest.getLastD first).length) :
    (overlapTrail h first rest).drop ((overlapTrail h first rest).length - k) =
      (rest.getLastD first).drop ((rest.getLastD first).length - k) :=
  drop_length_sub_of_suffix (suffix_overlapTrail hc) hk

theorem CompatibleTrail.length_first {h : Nat} {first : List α}
    {rest : List (List α)} (hc : CompatibleTrail h first rest) :
    h ≤ first.length := by
  cases rest with
  | nil => exact hc
  | cons next rest => exact hc.1.1

theorem length_overlapTrail_ge {h : Nat} {first : List α}
    {rest : List (List α)} (hc : CompatibleTrail h first rest) :
    h ≤ (overlapTrail h first rest).length :=
  Nat.le_trans hc.length_first (prefix_overlapTrail h first rest).length_le

/-- Every piece of a compatible trail is an actual infix of its assembled word. -/
theorem infix_overlapTrail_of_mem {h : Nat} {first piece : List α}
    {rest : List (List α)} (hc : CompatibleTrail h first rest)
    (hp : piece ∈ first :: rest) : piece.IsInfix (overlapTrail h first rest) := by
  induction rest generalizing first with
  | nil =>
      simp only [List.mem_singleton] at hp
      subst piece
      exact List.infix_refl _
  | cons next rest ih =>
      rcases List.mem_cons.mp hp with hp | hp
      · subst piece
        exact (prefix_overlapTrail h first (next :: rest)).isInfix
      · apply infix_overlapJoin_of_right (u := first) (v := overlapTrail h next rest)
        · rw [take_overlapTrail rest hc.1.2.1]
          exact hc.1.2.2
        · exact ih hc.2 hp

/-- The length ledger charges each join exactly once. -/
theorem length_overlapTrail_add {h : Nat} {first : List α}
    {rest : List (List α)} (hc : CompatibleTrail h first rest) :
    (overlapTrail h first rest).length + h * rest.length =
      first.length + (rest.map List.length).sum := by
  induction rest generalizing first with
  | nil => simp [overlapTrail]
  | cons next rest ih =>
      have hj := length_overlapJoin_add (u := first) (length_overlapTrail_ge hc.2)
      have ht := ih hc.2
      simp only [overlapTrail, List.length_cons, List.map_cons, List.sum_cons]
      rw [Nat.mul_succ]
      omega

/-- Row or macro costs of the form `scale * weight + extra + h` add literally.
For prescribed rows, use `scale = K+1`, `extra = 1`, and `h = K-3`.
-/
theorem length_overlapTrail_affine {β : Type v} (spell : β → List α)
    (weight : β → Nat) {h scale extra : Nat} {first : β} {rest : List β}
    (hc : CompatibleTrail h (spell first) (rest.map spell))
    (hl : ∀ piece ∈ first :: rest,
      (spell piece).length = scale * weight piece + extra + h) :
    (overlapTrail h (spell first) (rest.map spell)).length =
      scale * ((first :: rest).map weight).sum +
        extra * (first :: rest).length + h := by
  induction rest generalizing first with
  | nil =>
      simpa [overlapTrail] using hl first (by simp)
  | cons next rest ih =>
      have hfirst := hl first (by simp)
      have htail : ∀ piece ∈ next :: rest,
          (spell piece).length = scale * weight piece + extra + h := by
        intro piece hm
        exact hl piece (List.mem_cons_of_mem first hm)
      have ht := ih hc.2 htail
      have hj := length_overlapJoin_add (u := spell first) (length_overlapTrail_ge hc.2)
      simp only [List.map_cons, overlapTrail, List.sum_cons, List.length_cons,
        Nat.mul_add, Nat.mul_succ] at ht ⊢
      omega

theorem infix_overlapTrail_of_factor {h : Nat} {first p : List α}
    {rest : List (List α)} (hc : CompatibleTrail h first rest)
    (hp : ∃ piece ∈ first :: rest, p.IsInfix piece) :
    p.IsInfix (overlapTrail h first rest) := by
  obtain ⟨piece, hm, hf⟩ := hp
  exact hf.trans (infix_overlapTrail_of_mem hc hm)

theorem isSuperpermutation_overlapTrail {n h : Nat} {first : Word n}
    {rest : List (Word n)} (hc : CompatibleTrail h first rest)
    (hp : ∀ p : Word n, IsPermutation p →
      ∃ piece ∈ first :: rest, p.IsInfix piece) :
    IsSuperpermutation (overlapTrail h first rest) := by
  intro p hperm
  exact infix_overlapTrail_of_factor hc (hp p hperm)

end SuperpermutationUpperBound
