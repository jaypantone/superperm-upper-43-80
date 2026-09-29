import SuperpermutationUpperBound.Assembly.TrailWords
import SuperpermutationUpperBound.Foundation.WordSupport

namespace SuperpermutationUpperBound
variable {α : Type}

theorem trailWord_support (K : Nat) (rs : List (Row α)) (P : α → Prop)
    (h : ∀ r ∈ rs, ∀ a ∈ r.word, P a) : ∀ a ∈ trailWord K rs, P a := by
  cases rs with
  | nil => simp [trailWord]
  | cons first rest => exact overlapTrail_map_support Row.word P h

theorem familyWord_support (K : Nat) (trails : List (List (Row α))) (P : α → Prop)
    (h : ∀ r ∈ trails.flatten, ∀ a ∈ r.word, P a) : ∀ a ∈ familyWord K trails, P a := by
  intro a ha
  obtain ⟨w, hw, ha⟩ := List.mem_flatten.mp ha
  obtain ⟨trail, ht, rfl⟩ := List.mem_map.mp hw
  exact trailWord_support K trail P
    (fun r hr => h r (List.mem_flatten.mpr ⟨trail, ht, hr⟩)) a ha

/-- Exact finite-alphabet word existence from closed rows, literal assignment
coverage and bounded letter support. The number of closed trails remains explicit. -/
theorem exists_word_of_closed_rows {K : Nat} {rs : List (Row Nat)} (hK : 4 ≤ K)
    (hc : HasClosedDecomposition rs)
    (hv : ∀ r ∈ rs, 1 ≤ r.visible ∧ r.base.length + 1 = K)
    (hs : ∀ r ∈ rs, ∀ a ∈ r.word, a < K)
    (hcover : ∀ p : List Nat, p.Perm (List.range K) → ∃ r ∈ rs, r.Assigned p) :
    ∃ trails : List (List (Row Nat)), ∃ w : Word K,
      (∀ trail ∈ trails, ClosedTrail trail) ∧ trails.flatten.Perm rs ∧
      IsSuperpermutation w ∧
      w.length = (K + 1) * (rs.map Row.visible).sum + rs.length + (K - 3) * trails.length ∧
      trails.length ≤ rs.length := by
  obtain ⟨trails, u, ht, hp, rfl, hl, hn, ha⟩ := closed_rows_word_spec hK hc hv
  have hsupport := familyWord_support K trails (fun a => a < K)
    (fun r hr => hs r (hp.mem_iff.mp hr))
  refine ⟨trails, liftWord (familyWord K trails) hsupport, ht, hp, ?_, ?_, hn⟩
  · apply isSuperpermutation_liftWord_of_covers
    intro p hp
    obtain ⟨r, hr, hassign⟩ := hcover p hp
    exact ha r hr p hassign
  · simpa only [liftWord_length] using hl

end SuperpermutationUpperBound
