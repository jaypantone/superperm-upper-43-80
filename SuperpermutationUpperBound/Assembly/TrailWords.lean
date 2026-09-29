import SuperpermutationUpperBound.Partition.ClosedFamily

namespace SuperpermutationUpperBound
variable {α : Type}

/-- Spell a possibly empty list of rows. -/
def trailWord (K : Nat) : List (Row α) → List α
  | [] => []
  | first :: rest => rowTrailWord K first rest

def familyWord (K : Nat) (trails : List (List (Row α))) : List α :=
  (trails.map (trailWord K)).flatten

theorem rowTrailCompatible_prefix (first : Row α) (rest more : List (Row α))
    (h : RowTrailCompatible first (rest ++ more)) : RowTrailCompatible first rest := by
  induction rest generalizing first with
  | nil => trivial
  | cons a rest ih => exact ⟨h.1, ih a h.2⟩

theorem closedTrail_internal {first : Row α} {rest : List (Row α)}
    (hc : ClosedTrail (first :: rest)) : RowTrailCompatible first rest := by
  have hh := hc.2
  change ∀ pair ∈ (first :: rest).zip (rot (first :: rest) 1), _ at hh
  rw [Transport.rot_cons_one] at hh
  have h := (Transport.rowTrailCompatible_loop_iff_zip first first rest).mpr hh
  exact rowTrailCompatible_prefix first rest [first] h

theorem trailWord_spec {K : Nat} {rs : List (Row α)} (hK : 4 ≤ K)
    (hc : ClosedTrail rs)
    (hv : ∀ r ∈ rs, 1 ≤ r.visible ∧ r.base.length + 1 = K) :
    (trailWord K rs).length = (K + 1) * (rs.map Row.visible).sum + rs.length + (K - 3) ∧
      (∀ r ∈ rs, ∀ p, r.Assigned p → p.IsInfix (trailWord K rs)) := by
  obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil hc.1
  have h := rowTrail_spelling_spec hK (closedTrail_internal hc) hv
  exact ⟨by change (rowTrailWord K first rest).length = _; omega, h.2⟩

/-- Concatenating the closed-trail words preserves every assigned factor and
has the exact cost of one endpoint per trail. -/
theorem familyWord_spec {K : Nat} {trails : List (List (Row α))} (hK : 4 ≤ K)
    (hc : ∀ trail ∈ trails, ClosedTrail trail)
    (hv : ∀ r ∈ trails.flatten, 1 ≤ r.visible ∧ r.base.length + 1 = K) :
    (familyWord K trails).length =
      (K + 1) * (trails.flatten.map Row.visible).sum + trails.flatten.length +
        (K - 3) * trails.length ∧
      (∀ r ∈ trails.flatten, ∀ p, r.Assigned p → p.IsInfix (familyWord K trails)) := by
  constructor
  · induction trails with
    | nil => simp [familyWord]
    | cons trail trails ih =>
      have ht := (trailWord_spec hK (hc trail (by simp))
        (fun r hr => hv r (List.mem_flatten.mpr ⟨trail, by simp, hr⟩))).1
      have hi := ih (fun t ht => hc t (by simp [ht]))
        (fun r hr => hv r (by simp [hr]))
      change ((trailWord K trail) ++ familyWord K trails).length = _
      simp only [List.length_append, ht, hi, List.flatten_cons, List.map_append,
        List.sum_append, List.length_cons, Nat.mul_add, Nat.mul_succ]
      omega
  · intro r hr p hp
    obtain ⟨trail, ht, hr⟩ := List.mem_flatten.mp hr
    have h := (trailWord_spec hK (hc trail ht)
      (fun r hr => hv r (List.mem_flatten.mpr ⟨trail, ht, hr⟩))).2 r hr p hp
    exact h.trans (List.infix_of_mem_flatten (List.mem_map.mpr ⟨trail, ht, rfl⟩))

/-- Every closed component is nonempty, so its count is at most the row count.
This elementary estimate is useful before sharper connector bounds are proved. -/
theorem closed_family_length_le_rows {trails : List (List (Row α))}
    (hc : ∀ trail ∈ trails, ClosedTrail trail) : trails.length ≤ trails.flatten.length := by
  induction trails with
  | nil => simp
  | cons trail trails ih =>
    have hp := List.length_pos_iff.mpr (hc trail (by simp)).1
    have hi := ih (fun t ht => hc t (by simp [ht]))
    simp only [List.length_cons, List.flatten_cons, List.length_append]
    omega

/-- Existence of a literal word from any closed decomposition, with the
component count retained in the exact length formula. -/
theorem closed_rows_word_spec {K : Nat} {rs : List (Row α)} (hK : 4 ≤ K)
    (hc : HasClosedDecomposition rs)
    (hv : ∀ r ∈ rs, 1 ≤ r.visible ∧ r.base.length + 1 = K) :
    ∃ trails : List (List (Row α)), ∃ w : List α,
      (∀ trail ∈ trails, ClosedTrail trail) ∧ trails.flatten.Perm rs ∧
      w = familyWord K trails ∧
      w.length = (K + 1) * (rs.map Row.visible).sum + rs.length + (K - 3) * trails.length ∧
      trails.length ≤ rs.length ∧
      (∀ r ∈ rs, ∀ p, r.Assigned p → p.IsInfix w) := by
  obtain ⟨trails, ht, hp⟩ := hc
  have hw := familyWord_spec hK ht (fun r hr => hv r (hp.mem_iff.mp hr))
  refine ⟨trails, familyWord K trails, ht, hp, rfl, ?_, ?_, ?_⟩
  · rw [hw.1, (hp.map Row.visible).sum_eq, hp.length_eq]
  · simpa only [hp.length_eq] using closed_family_length_le_rows ht
  · intro r hr p ha
    exact hw.2 r (hp.mem_iff.mpr hr) p ha

end SuperpermutationUpperBound
