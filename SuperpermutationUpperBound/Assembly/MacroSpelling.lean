import SuperpermutationUpperBound.Assembly.MacroWords
import SuperpermutationUpperBound.Assembly.CycleSplicing

namespace SuperpermutationUpperBound
variable {α : Type} {h : Nat}

/-- Literal spelling of a directed macro-edge path, including an empty path. -/
def macroPathWord (start : List α) : List (MacroEdge α h) → List α
  | [] => start
  | e :: es => overlapJoin e.word (macroPathWord e.target es) h

/-- A directed traversal contains every edge word and has the exact sum of
edge costs plus one initial endpoint. -/
theorem macroPathWord_spec {start finish : List α} {es : List (MacroEdge α h)}
    (hp : EdgePath MacroEdge.source MacroEdge.target start es finish)
    (hstart : start.length = h) :
    (macroPathWord start es).length = (es.map MacroEdge.cost).sum + h ∧
      (macroPathWord start es).take h = start ∧
      (macroPathWord start es).drop ((macroPathWord start es).length - h) = finish ∧
      (∀ e ∈ es, e.word.IsInfix (macroPathWord start es)) := by
  revert hstart
  induction hp with
  | nil v =>
    intro hv
    simp [macroPathWord, ← hv]
  | @cons start finish e es he hp ih =>
    intro _
    have ht := ih e.target_length
    have hlen : h ≤ (macroPathWord e.target es).length := by omega
    have hm : e.word.drop (e.word.length - h) = (macroPathWord e.target es).take h :=
      ht.2.1.symm
    refine ⟨?_, ?_, ?_, ?_⟩
    · change (overlapJoin e.word (macroPathWord e.target es) h).length = _
      rw [length_overlapJoin hlen, e.word_length, ht.1, List.map_cons, List.sum_cons]
      omega
    · change (overlapJoin e.word (macroPathWord e.target es) h).take h = start
      rw [take_overlapJoin e.length_ge]
      exact he
    · change (overlapJoin e.word (macroPathWord e.target es) h).drop
        ((overlapJoin e.word (macroPathWord e.target es) h).length - h) = finish
      rw [drop_length_sub_overlapJoin hm hlen]
      exact ht.2.2.1
    · intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact infix_overlapJoin_left _ _ _
      · exact (ht.2.2.2 f hf).trans (infix_overlapJoin_right hm)

theorem macroPathWord_support (start : List α) (es : List (MacroEdge α h)) (P : α → Prop)
    (hs : ∀ a ∈ start, P a) (he : ∀ e ∈ es, ∀ a ∈ e.word, P a) :
    ∀ a ∈ macroPathWord start es, P a := by
  induction es generalizing start with
  | nil => exact hs
  | cons e es ih =>
    intro a ha
    rcases mem_overlapJoin ha with ha | ha
    · exact he e (by simp) a ha
    · exact ih e.target (fun a ha => he e (by simp) a (List.mem_of_mem_drop ha))
        (fun f hf => he f (by simp [hf])) a ha

end SuperpermutationUpperBound
