import SuperpermutationUpperBound.RowSpelling
import SuperpermutationUpperBound.Foundation.Overlap

/-! Compatible row occurrences spell literal words with the exact trail ledger.
No endpoint-disjointness assumption is made. -/
namespace SuperpermutationUpperBound

variable {α : Type}

def RowTrailCompatible (first : Row α) : List (Row α) → Prop
  | [] => True
  | next :: rest => first.Compatible next ∧ RowTrailCompatible next rest

instance instDecidableRowTrailCompatible [DecidableEq α] (first : Row α)
    (rest : List (Row α)) : Decidable (RowTrailCompatible first rest) :=
  match rest with
  | [] => isTrue True.intro
  | next :: rest => by
    haveI := instDecidableRowTrailCompatible next rest
    unfold RowTrailCompatible Row.Compatible
    infer_instance

def rowTrailWord (K : Nat) (first : Row α) (rest : List (Row α)) : List α :=
  overlapTrail (K - 3) first.word (rest.map Row.word)

theorem Row.word_length_affine (r : Row α) {K : Nat}
    (hK : r.base.length + 1 = K) (hsize : 4 ≤ K) (hv : 1 ≤ r.visible) :
    r.word.length = (K + 1) * r.visible + 1 + (K - 3) := by
  have h := (r.spelling_spec hK hsize hv).2.1
  omega

theorem Row.word_length_ge_endpoint (r : Row α) {K : Nat}
    (hK : r.base.length + 1 = K) : K - 3 ≤ r.word.length := by
  have h := r.head_prefix_word.length_le
  have hl : r.head.length = r.base.length - 2 := by simp [Row.head]
  rw [hl] at h
  omega

theorem Row.overlapCompatible_word {r t : Row α} {K : Nat}
    (hr : r.base.length + 1 = K) (ht : t.base.length + 1 = K)
    (hsize : 4 ≤ K) (hv : 1 ≤ r.visible) (hc : r.Compatible t) :
    OverlapCompatible (K - 3) r.word t.word := by
  refine ⟨r.word_length_ge_endpoint hr, t.word_length_ge_endpoint ht, ?_⟩
  have hk : K - 3 = r.base.length - 2 := by omega
  have hk' : K - 3 = t.base.length - 2 := by omega
  have hd := r.word_drop_tail hv (by omega)
  have hp := t.word_take_head
  rw [← hk] at hd
  rw [← hk'] at hp
  rw [hd, hp]
  exact hc

theorem rowTrail_overlapCompatible {K : Nat} {first : Row α} {rest : List (Row α)}
    (hsize : 4 ≤ K) (hc : RowTrailCompatible first rest)
    (hv : ∀ r ∈ first :: rest, 1 ≤ r.visible ∧ r.base.length + 1 = K) :
    CompatibleTrail (K - 3) first.word (rest.map Row.word) := by
  induction rest generalizing first with
  | nil => exact first.word_length_ge_endpoint (hv first (by simp)).2
  | cons next rest ih =>
    have hf := hv first (by simp)
    have hn := hv next (by simp)
    refine ⟨Row.overlapCompatible_word hf.2 hn.2 hsize hf.1 hc.1, ?_⟩
    exact ih hc.2 (fun r hr => hv r (List.mem_cons_of_mem _ hr))

/-- Exact length and literal permutation coverage for a nonempty row trail. -/
theorem rowTrail_spelling_spec {K : Nat} {first : Row α} {rest : List (Row α)}
    (hsize : 4 ≤ K) (hc : RowTrailCompatible first rest)
    (hv : ∀ r ∈ first :: rest, 1 ≤ r.visible ∧ r.base.length + 1 = K) :
    (rowTrailWord K first rest).length =
      (K + 1) * ((first :: rest).map Row.visible).sum + (first :: rest).length + K - 3 ∧
    (∀ r ∈ first :: rest, ∀ p, r.Assigned p → p.IsInfix (rowTrailWord K first rest)) := by
  have hw := rowTrail_overlapCompatible hsize hc hv
  refine ⟨?_, ?_⟩
  · have hl := length_overlapTrail_affine Row.word Row.visible (extra := 1) hw
      (fun r hr => r.word_length_affine (hv r hr).2 hsize (hv r hr).1)
    simp only [Nat.one_mul] at hl
    unfold rowTrailWord
    rw [hl]
    omega
  · intro r hr p hp
    apply (r.assigned_infix_word hp).trans
    apply infix_overlapTrail_of_mem hw
    simpa only [List.map_cons] using List.mem_map_of_mem (f := Row.word) hr

theorem isSuperpermutation_rowTrail {K : Nat} {first : Row (Fin K)}
    {rest : List (Row (Fin K))} (hsize : 4 ≤ K) (hc : RowTrailCompatible first rest)
    (hv : ∀ r ∈ first :: rest, 1 ≤ r.visible ∧ r.base.length + 1 = K)
    (hcover : ∀ p : Word K, IsPermutation p → ∃ r ∈ first :: rest, r.Assigned p) :
    IsSuperpermutation (rowTrailWord K first rest) := by
  intro p hp
  obtain ⟨r, hr, ha⟩ := hcover p hp
  exact (rowTrail_spelling_spec hsize hc hv).2 r hr p ha

end SuperpermutationUpperBound
