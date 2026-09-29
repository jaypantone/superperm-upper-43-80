import SuperpermutationUpperBound.Assembly.DisjointCycles
import SuperpermutationUpperBound.Assembly.OpenCycles

namespace SuperpermutationUpperBound
variable {E V : Type}

def DirectedTrails (src dst : E → V) (trails : List (List E)) : Prop :=
  ∀ es ∈ trails, es ≠ [] ∧ ∃ a b, EdgePath src dst a es b

namespace EdgePath
variable {src dst : E → V}

/-- Removing selected edges from a directed path leaves a first, possibly
empty run and at most one further nonempty run per removed edge. -/
theorem retained_runs (keep : E → Bool) {a b : V} {es : List E}
    (hp : EdgePath src dst a es b) :
    ∃ first rest finish, EdgePath src dst a first finish ∧ DirectedTrails src dst rest ∧
      first ++ rest.flatten = es.filter keep ∧
      rest.length ≤ es.countP (fun e => !(keep e)) := by
  induction hp with
  | nil a => exact ⟨[], [], a, .nil a, by simp [DirectedTrails], by simp, by simp⟩
  | @cons a b e es he ht ih =>
    obtain ⟨first, rest, finish, hfirst, hrest, hinv, hlen⟩ := ih
    by_cases hk : keep e = true
    · refine ⟨e :: first, rest, finish, .cons he hfirst, hrest, ?_, ?_⟩
      · simpa only [List.cons_append, List.filter_cons, hk, ↓reduceIte] using congrArg (List.cons e) hinv
      · simpa [List.countP_cons, hk] using hlen
    · by_cases hf : first = []
      · refine ⟨[], rest, a, .nil a, hrest, ?_, ?_⟩
        · simpa [List.filter_cons, hk, hf] using hinv
        · simp only [List.countP_cons, hk, Bool.not_eq_true, Bool.not_true] at *
          simpa [hk] using Nat.le_succ_of_le hlen
      · refine ⟨[], first :: rest, a, .nil a, ?_, ?_, ?_⟩
        · intro xs hxs
          rcases List.mem_cons.mp hxs with rfl | hxs
          · exact ⟨hf, dst e, finish, hfirst⟩
          · exact hrest xs hxs
        · simpa [List.filter_cons, hk] using hinv
        · simpa [List.countP_cons, hk] using Nat.add_le_add_right hlen 1

/-- Cutting a path at marked edges produces at most one more trail than the
number of cuts, and preserves all retained occurrences. -/
theorem remove_edges (keep : E → Bool) {a b : V} {es : List E}
    (hp : EdgePath src dst a es b) :
    ∃ trails, DirectedTrails src dst trails ∧ trails.flatten = es.filter keep ∧
      trails.length ≤ es.countP (fun e => !(keep e)) + 1 := by
  obtain ⟨first, rest, finish, hf, hr, hi, hl⟩ := hp.retained_runs keep
  by_cases hfirst : first = []
  · exact ⟨rest, hr, by simpa [hfirst] using hi, Nat.le_succ_of_le hl⟩
  · refine ⟨first :: rest, ?_, hi, ?_⟩
    · intro xs hxs
      rcases List.mem_cons.mp hxs with rfl | hxs
      · exact ⟨hfirst, a, finish, hf⟩
      · exact hr xs hxs
    · simpa using Nat.add_le_add_right hl 1

/-- On a closed cycle containing a marked edge, the first cut opens the
cycle. Consequently no extra trail is charged beyond the number of cuts. -/
theorem remove_edges_closed (keep : E → Bool) {a : V} {es : List E}
    (hp : EdgePath src dst a es a) {e : E} (he : e ∈ es) (hk : keep e = false) :
    ∃ trails, DirectedTrails src dst trails ∧ (trails.flatten).Perm (es.filter keep) ∧
      trails.length ≤ es.countP (fun e => !(keep e)) := by
  obtain ⟨rest, hr, hi⟩ := hp.remove_edge he
  obtain ⟨trails, ht, hti, htl⟩ := hr.remove_edges keep
  refine ⟨trails, ht, ?_, ?_⟩
  · rw [hti]
    simpa [List.filter_cons, hk] using hi.filter keep
  · have hcount := hi.countP_eq (fun e => !(keep e))
    simp [List.countP_cons, hk] at hcount
    omega

end EdgePath
end SuperpermutationUpperBound
