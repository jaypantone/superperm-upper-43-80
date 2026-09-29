import SuperpermutationUpperBound.Assembly.OpenCycles
import SuperpermutationUpperBound.Assembly.BalancedChoices
import Mathlib.Tactic.Choose

namespace SuperpermutationUpperBound
variable {E α : Type} {h : Nat}

/-- Cut a designated ordinary circle edge anywhere on a closed module.
All required macro words survive because their labels differ from the
ordinary cut-edge labels. -/
theorem circle_module_cut_words (payload : E → MacroEdge α h)
    (es : List E) (x : List α) (cut : Nat → E) (required : E → Prop) (P : α → Prop)
    (hx : x.length = h) (hh : 0 < h)
    (hp : ∃ a, EdgePath (fun e => (payload e).source) (fun e => (payload e).target) a es a)
    (hcut : ∀ j, j < h → cut j ∈ es ∧ (payload (cut j)).cost = 1 ∧
      (payload (cut j)).source = rot x j ∧ (payload (cut j)).target = rot x (j + 1))
    (hrequired : ∀ e, required e → ∀ j, j < h → e ≠ cut j)
    (hs : ∀ e ∈ es, ∀ a ∈ (payload e).word, P a) :
    ∃ words : Nat → List α,
      (∀ j, j < h → (words j).length = (es.map (fun e => (payload e).cost)).sum - 1 + h ∧
        (words j).take h = rot x (j + 1) ∧
        (words j).drop ((words j).length - h) = rot x j ∧
        (∀ e ∈ es, required e → (payload e).word.IsInfix (words j)) ∧
        (∀ a ∈ words j, P a)) ∧
      ∀ ell, ell ≤ h →
        ((List.range h).map (fun j => (words j).take ell)).Perm
          ((List.range h).map (fun j => (words j).drop ((words j).length - ell))) := by
  classical
  obtain ⟨a, hpath⟩ := hp
  have hex : ∀ j : Fin h, ∃ w : List α,
      w.length = (es.map (fun e => (payload e).cost)).sum - 1 + h ∧
      w.take h = rot x (j.val + 1) ∧ w.drop (w.length - h) = rot x j.val ∧
      (∀ e ∈ es, required e → (payload e).word.IsInfix w) ∧ (∀ a ∈ w, P a) := by
    intro j
    obtain ⟨hj, hc, hsource, htarget⟩ := hcut j.val j.isLt
    obtain ⟨rest, w, hr, hi, hw, hlen, hpre, hsuf, hcover⟩ :=
      exists_open_macro_word payload hpath hj hc
    refine ⟨w, hlen, hpre.trans htarget, hsuf.trans hsource, ?_, ?_⟩
    · intro e he heq
      exact hcover e he (hrequired e heq j.val j.isLt)
    · rw [hw]
      exact macroPathWord_after_cut_support payload P hi hs
  choose word hword using hex
  let words : Nat → List α := fun j => if hj : j < h then word ⟨j, hj⟩ else []
  have spec : ∀ j, j < h → (words j).length = (es.map (fun e => (payload e).cost)).sum - 1 + h ∧
        (words j).take h = rot x (j + 1) ∧
        (words j).drop ((words j).length - h) = rot x j ∧
        (∀ e ∈ es, required e → (payload e).word.IsInfix (words j)) ∧
        (∀ a ∈ words j, P a) := by
    intro j hj
    simpa only [words, dif_pos hj] using hword ⟨j, hj⟩
  refine ⟨words, spec, ?_⟩
  intro ell hell
  have hpos : 0 < x.length := by omega
  have hlen : ∀ j, j < x.length → x.length ≤ (words j).length := by
    intro j hj
    have hj' : j < h := by omega
    rw [(spec j hj').1, hx]
    omega
  have hpre : ∀ j, j < x.length → (words j).take x.length = rot x (j + 1) := by
    intro j hj
    rw [hx]
    exact (spec j (by omega)).2.1
  have hsuf : ∀ j, j < x.length →
      (words j).drop ((words j).length - x.length) = rot x j := by
    intro j hj
    rw [hx]
    exact (spec j (by omega)).2.2.1
  simpa only [hx] using balanced_choices_of_rotation_endpoints x words hpos hlen hpre hsuf ell
    (by omega)

end SuperpermutationUpperBound
