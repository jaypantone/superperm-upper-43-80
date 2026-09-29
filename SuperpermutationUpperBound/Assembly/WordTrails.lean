import SuperpermutationUpperBound.Assembly.RemoveEdges

namespace SuperpermutationUpperBound

variable {E V W α : Type} {h : Nat}

/-- A vertex map transports the incidence equations while retaining every
label and its position in the path. Injectivity is not needed. -/
theorem EdgePath.map_vertices {src dst : E → V} (f : V → W)
    {a b : V} {es : List E} (hp : EdgePath src dst a es b) :
    EdgePath (fun e => f (src e)) (fun e => f (dst e)) (f a) es (f b) := by
  induction hp with
  | nil a => exact .nil _
  | @cons a b e es he ht ih => exact .cons (congrArg f he) ih

/-- A nonempty labelled trail starts at the literal source of its first
payload. The empty list spells the empty word. -/
def macroTrailWord (payload : E → MacroEdge α h) : List E → List α
  | [] => []
  | e :: es => macroPathWord (payload e).source ((e :: es).map payload)

def macroFamilyWord (payload : E → MacroEdge α h) (trails : List (List E)) : List α :=
  (trails.map (macroTrailWord payload)).flatten

theorem macroTrailWord_spec (payload : E → MacroEdge α h)
    {es : List E} (hne : es ≠ []) {a b : List α}
    (hp : EdgePath (fun e => (payload e).source) (fun e => (payload e).target) a es b) :
    (macroTrailWord payload es).length = (es.map (fun e => (payload e).cost)).sum + h ∧
      ∀ e ∈ es, (payload e).word.IsInfix (macroTrailWord payload es) := by
  obtain ⟨e, es, rfl⟩ := List.exists_cons_of_ne_nil hne
  have he := hp.source_eq_of_cons
  change (payload e).source = a at he
  subst a
  have hm := hp.map_edges payload (fun _ => rfl) (fun _ => rfl)
  have hw := macroPathWord_spec hm (payload e).source_length
  refine ⟨?_, fun f hf => ?_⟩
  · simpa only [macroTrailWord, List.map_map, Function.comp_def] using hw.1
  · exact hw.2.2.2 (payload f) (List.mem_map_of_mem (f := payload) hf)

theorem macroTrailWord_support (payload : E → MacroEdge α h) (P : α → Prop)
    (es : List E) (hs : ∀ e ∈ es, ∀ a ∈ (payload e).word, P a) :
    ∀ a ∈ macroTrailWord payload es, P a := by
  cases es with
  | nil => simp [macroTrailWord]
  | cons e es =>
    apply macroPathWord_support _ _ P
    · intro a ha
      exact hs e (by simp) a (List.mem_of_mem_take ha)
    · intro edge hm a ha
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hm
      exact hs f hf a ha

/-- Spelling each nonempty directed trail and concatenating the results
preserves every payload word and pays one literal endpoint per trail. -/
theorem macroFamilyWord_spec (payload : E → MacroEdge α h)
    {trails : List (List E)}
    (ht : DirectedTrails (fun e => (payload e).source) (fun e => (payload e).target) trails) :
    (macroFamilyWord payload trails).length =
      (trails.flatten.map (fun e => (payload e).cost)).sum + h * trails.length ∧
      ∀ e ∈ trails.flatten, (payload e).word.IsInfix (macroFamilyWord payload trails) := by
  constructor
  · induction trails with
    | nil => simp [macroFamilyWord]
    | cons es trails ih =>
      obtain ⟨hne, a, b, hp⟩ := ht es (by simp)
      have hw := (macroTrailWord_spec payload hne hp).1
      have hi := ih (fun fs hf => ht fs (by simp [hf]))
      change ((macroTrailWord payload es) ++ macroFamilyWord payload trails).length = _
      simp only [List.length_append, hw, hi, List.flatten_cons, List.map_append,
        List.sum_append, List.length_cons, Nat.mul_succ]
      omega
  · intro e he
    obtain ⟨es, hes, he⟩ := List.mem_flatten.mp he
    obtain ⟨hne, a, b, hp⟩ := ht es hes
    exact ((macroTrailWord_spec payload hne hp).2 e he).trans
      (List.infix_of_mem_flatten (List.mem_map.mpr ⟨es, hes, rfl⟩))

theorem macroFamilyWord_support (payload : E → MacroEdge α h) (P : α → Prop)
    (trails : List (List E))
    (hs : ∀ e ∈ trails.flatten, ∀ a ∈ (payload e).word, P a) :
    ∀ a ∈ macroFamilyWord payload trails, P a := by
  intro a ha
  obtain ⟨w, hw, ha⟩ := List.mem_flatten.mp ha
  obtain ⟨es, hes, rfl⟩ := List.mem_map.mp hw
  exact macroTrailWord_support payload P es
    (fun e he => hs e (List.mem_flatten.mpr ⟨es, hes, he⟩)) a ha

/-- The finite inventory version retains arbitrary labels until all trail
spellings are established, then replaces the list cost sum by a finite sum. -/
theorem exists_word_of_directed_trails [Fintype E] (payload : E → MacroEdge α h)
    (trails : List (List E))
    (ht : DirectedTrails (fun e => (payload e).source) (fun e => (payload e).target) trails)
    (hi : trails.flatten.Perm Finset.univ.toList) (P : α → Prop)
    (hs : ∀ e, ∀ a ∈ (payload e).word, P a) :
    ∃ w : List α, w.length = (∑ e, (payload e).cost) + h * trails.length ∧
      (∀ e, (payload e).word.IsInfix w) ∧ ∀ a ∈ w, P a := by
  have hw := macroFamilyWord_spec payload ht
  refine ⟨macroFamilyWord payload trails, ?_, ?_,
    macroFamilyWord_support payload P trails (fun e _ => hs e)⟩
  · rw [hw.1, (hi.map (fun e => (payload e).cost)).sum_nat]
    simp only [Finset.sum_map_toList]
  · intro e
    exact hw.2 e (hi.mem_iff.mpr (by simp))

end SuperpermutationUpperBound
