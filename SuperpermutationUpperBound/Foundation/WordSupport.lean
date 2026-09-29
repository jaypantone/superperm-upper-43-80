import SuperpermutationUpperBound.RowSpelling
import SuperpermutationUpperBound.Foundation.Overlap

/-! Row spellings and literal overlap joins introduce no new letters.
These support statements do not require endpoint compatibility. -/
namespace SuperpermutationUpperBound

variable {α : Type}

theorem mem_rowSpellingAux_iff {x : List α} {s a : α} (t : Nat) :
    a ∈ rowSpellingAux x s t ↔ a ∈ x ∨ a = s := by
  induction t with
  | zero => simp [rowSpellingAux, cycleSpelling, or_left_comm, or_comm]
  | succ t ih =>
    rw [rowSpellingAux]
    simp only [List.mem_append, List.mem_singleton]
    constructor
    · intro ha
      rcases ha with ((ha | ha) | ha) | ha
      · exact ih.mp ha
      · exact Or.inl ((rot_perm x t).mem_iff.mp (List.mem_of_mem_take ha))
      · exact Or.inr ha
      · exact Or.inl ((rot_perm x (t + 1)).mem_iff.mp ha)
    · intro ha
      exact Or.inl (Or.inl (Or.inl (ih.mpr ha)))

theorem Row.mem_word_iff {r : Row α} {a : α} :
    a ∈ r.word ↔ a ∈ r.base ∨ a = r.satellite :=
  mem_rowSpellingAux_iff (r.visible - 1)

theorem Row.word_support (r : Row α) (P : α → Prop)
    (hb : ∀ a ∈ r.base, P a) (hs : P r.satellite) : ∀ a ∈ r.word, P a := by
  intro a ha
  rcases Row.mem_word_iff.mp ha with ha | rfl
  · exact hb a ha
  · exact hs

theorem mem_overlapJoin {u v : List α} {h : Nat} {a : α}
    (ha : a ∈ overlapJoin u v h) : a ∈ u ∨ a ∈ v := by
  rcases List.mem_append.mp ha with ha | ha
  · exact Or.inl ha
  · exact Or.inr (List.mem_of_mem_drop ha)

theorem mem_overlapTrail {h : Nat} {first : List α} {rest : List (List α)} {a : α}
    (ha : a ∈ overlapTrail h first rest) : ∃ w ∈ first :: rest, a ∈ w := by
  induction rest generalizing first with
  | nil => exact ⟨first, by simp, ha⟩
  | cons next rest ih =>
    rcases mem_overlapJoin ha with ha | ha
    · exact ⟨first, by simp, ha⟩
    · obtain ⟨w, hw, haw⟩ := ih ha
      exact ⟨w, List.mem_cons_of_mem _ hw, haw⟩

theorem overlapTrail_support (P : α → Prop) {h : Nat} {first : List α}
    {rest : List (List α)} (hs : ∀ w ∈ first :: rest, ∀ a ∈ w, P a) :
    ∀ a ∈ overlapTrail h first rest, P a := by
  intro a ha
  obtain ⟨w, hw, haw⟩ := mem_overlapTrail ha
  exact hs w hw a haw

theorem overlapTrail_map_support {β : Type} (spell : β → List α) (P : α → Prop)
    {h : Nat} {first : β} {rest : List β}
    (hs : ∀ b ∈ first :: rest, ∀ a ∈ spell b, P a) :
    ∀ a ∈ overlapTrail h (spell first) (rest.map spell), P a := by
  apply overlapTrail_support P
  intro w hw a ha
  rcases List.mem_cons.mp hw with rfl | hw
  · exact hs first (by simp) a ha
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hw
    exact hs b (List.mem_cons_of_mem _ hb) a ha

end SuperpermutationUpperBound
