import SuperpermutationUpperBound.Assembly.MacroWords
import SuperpermutationUpperBound.Transport.Closed
import SuperpermutationUpperBound.Assembly.WordTrails

namespace SuperpermutationUpperBound
variable {α : Type}

/-- A row trail ending compatibly at a specified next row is a literal
macro-edge path to that row's head. -/
theorem rowTrail_loop_edgePath (first : Row α) (rest : List (Row α)) (last : Row α)
    (hc : RowTrailCompatible first (rest ++ [last])) :
    EdgePath Row.head Row.tail first.head (first :: rest) last.head := by
  induction rest generalizing first with
  | nil =>
    refine EdgePath.cons rfl ?_
    have h := hc.1
    change first.tail = last.head at h
    rw [h]
    exact .nil _
  | cons next rest ih =>
    refine EdgePath.cons rfl ?_
    have h := hc.1
    change first.tail = next.head at h
    rw [h]
    exact ih next hc.2

/-- Closed row trails give closed directed paths at their literal row heads
and tails. Distinctness of endpoint values is not required. -/
theorem ClosedTrail.edgePath {rs : List (Row α)} (hc : ClosedTrail rs) :
    ∃ a, EdgePath Row.head Row.tail a rs a := by
  obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil hc.1
  refine ⟨first.head, rowTrail_loop_edgePath first rest first ?_⟩
  apply (Transport.rowTrailCompatible_loop_iff_zip first first rest).mpr
  have h := hc.2
  change ∀ pair ∈ (first :: rest).zip (rot (first :: rest) 1), _ at h
  rwa [Transport.rot_cons_one] at h

/-- Mapping a closed row list to actual row words preserves its directed
closed path and every labelled occurrence. -/
theorem ClosedTrail.macroEdgePath {K : Nat} (hK : 4 ≤ K) {rs : List (Row α)}
    (hc : ClosedTrail rs) (hlen : ∀ r ∈ rs, r.base.length + 1 = K)
    (hv : ∀ r ∈ rs, 1 ≤ r.visible) :
    ∃ a, EdgePath MacroEdge.source MacroEdge.target a
      (rs.attach.map (fun r => MacroEdge.ofRow K r.val (hlen r.val r.property))) a := by
  obtain ⟨a, hp⟩ := hc.edgePath
  have hmap : ∀ {es : List (Row α)} {b c : List α},
      EdgePath Row.head Row.tail b es c → (hsub : ∀ r ∈ es, r ∈ rs) →
      EdgePath MacroEdge.source MacroEdge.target b
        (es.attach.map (fun r => MacroEdge.ofRow K r.val (hlen r.val (hsub r.val r.property)))) c := by
    intro es b c ht
    induction ht with
    | nil b => intro _; exact .nil b
    | @cons b c r es hr ht ih =>
      intro hsub
      simp only [List.attach_cons, List.map_cons, List.map_map, Function.comp_def]
      refine EdgePath.cons ?_ ?_
      · exact (MacroEdge.ofRow_source K r _).trans hr
      · rw [MacroEdge.ofRow_target K r _ hK (hv r (hsub r (by simp)))]
        exact ih (fun t ht => hsub t (List.mem_cons_of_mem _ ht))
  exact ⟨a, hmap hp (fun _ h => h)⟩

end SuperpermutationUpperBound
