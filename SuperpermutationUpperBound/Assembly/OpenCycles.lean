import SuperpermutationUpperBound.Assembly.MacroSpelling

/-! Cut one designated labelled edge from a closed path before mapping labels
to word payloads. The remaining path retains the exact occurrence inventory. -/
namespace SuperpermutationUpperBound

variable {β : Type u} {γ : Type v} {V : Type w}

namespace EdgePath

theorem map_edges {src dst : β → V} {src' dst' : γ → V}
    (f : β → γ) (hsrc : ∀ e, src' (f e) = src e) (hdst : ∀ e, dst' (f e) = dst e)
    {a b : V} {es : List β} (hp : EdgePath src dst a es b) :
    EdgePath src' dst' a (es.map f) b := by
  induction hp with
  | nil v => exact .nil v
  | @cons a b e es he ht ih =>
    apply EdgePath.cons ((hsrc e).trans he)
    simpa only [hdst e] using ih

/-- Remove one occurrence of the designated edge after rotating the closed
path to start at that occurrence. The rest runs from its destination to source. -/
theorem remove_edge {src dst : β → V} {a : V} {es : List β}
    (hp : EdgePath src dst a es a) {e : β} (he : e ∈ es) :
    ∃ rest, EdgePath src dst (dst e) rest (src e) ∧ (e :: rest).Perm es := by
  obtain ⟨j, _, hhead, hpath, hperm⟩ := hp.exists_rotation_at_source he
  cases hrot : rot es j with
  | nil => simp only [hrot, List.head?_nil, reduceCtorEq] at hhead
  | cons f rest =>
    have hfe : f = e := by simpa only [hrot, List.head?_cons, Option.some.injEq] using hhead
    subst f
    rw [hrot] at hpath hperm
    exact ⟨rest, hpath.tail_of_cons, hperm⟩

end EdgePath

theorem mem_after_cut_of_ne {es rest : List β} {e f : β}
    (hp : (e :: rest).Perm es) (hf : f ∈ es) (hne : f ≠ e) : f ∈ rest :=
  (List.mem_cons.mp (hp.mem_iff.mpr hf)).resolve_left hne

theorem cut_cost_ledger (cost : β → Nat) {es rest : List β} {e : β}
    (hp : (e :: rest).Perm es) :
    (rest.map cost).sum + cost e = (es.map cost).sum := by
  have hsum := (hp.map cost).sum_nat
  simpa only [List.map_cons, List.sum_cons, Nat.add_comm] using hsum

theorem cut_cost_one_ledger (cost : β → Nat) {es rest : List β} {e : β}
    (hp : (e :: rest).Perm es) (he : cost e = 1) :
    (rest.map cost).sum = (es.map cost).sum - 1 := by
  have hs := cut_cost_ledger cost hp
  rw [he] at hs
  omega

variable {α : Type} {h : Nat}

/-- Cutting a cost-one connector gives an actual literal word with the exact
cost saving. Every differently labelled edge retains its entire payload word,
even if distinct labels carry equal payloads. The rest may be empty. -/
theorem exists_open_macro_word (payload : β → MacroEdge α h)
    {start : List α} {es : List β}
    (hp : EdgePath (fun e => (payload e).source) (fun e => (payload e).target) start es start)
    {e : β} (he : e ∈ es) (hcost : (payload e).cost = 1) :
    ∃ rest : List β, ∃ w : List α,
      EdgePath (fun f => (payload f).source) (fun f => (payload f).target)
        (payload e).target rest (payload e).source ∧
      (e :: rest).Perm es ∧
      w = macroPathWord (payload e).target (rest.map payload) ∧
      w.length = (es.map (fun f => (payload f).cost)).sum - 1 + h ∧
      w.take h = (payload e).target ∧
      w.drop (w.length - h) = (payload e).source ∧
      (∀ f ∈ es, f ≠ e → (payload f).word.IsInfix w) := by
  obtain ⟨rest, hr, hi⟩ := hp.remove_edge he
  have hm := hr.map_edges payload (fun _ => rfl) (fun _ => rfl)
  have hw := macroPathWord_spec hm (payload e).target_length
  refine ⟨rest, macroPathWord (payload e).target (rest.map payload), hr, hi, rfl,
    ?_, hw.2.1, hw.2.2.1, ?_⟩
  · rw [hw.1]
    simp only [List.map_map, Function.comp_def]
    rw [cut_cost_one_ledger (fun f => (payload f).cost) hi hcost]
  · intro f hf hne
    exact hw.2.2.2 (payload f)
      (List.mem_map_of_mem (f := payload) (mem_after_cut_of_ne hi hf hne))

/-- The initial tuple left by a cut is a suffix of the removed edge word, so
support of all original payload words also supports the cut word. -/
theorem macroPathWord_after_cut_support (payload : β → MacroEdge α h) (P : α → Prop)
    {es rest : List β} {e : β} (hp : (e :: rest).Perm es)
    (hs : ∀ f ∈ es, ∀ a ∈ (payload f).word, P a) :
    ∀ a ∈ macroPathWord (payload e).target (rest.map payload), P a := by
  apply macroPathWord_support _ _ P
  · intro a ha
    exact hs e (hp.mem_iff.mp (by simp)) a (List.mem_of_mem_drop ha)
  · intro edge hm a ha
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hm
    exact hs f (hp.mem_iff.mp (List.mem_cons_of_mem _ hf)) a ha

end SuperpermutationUpperBound
