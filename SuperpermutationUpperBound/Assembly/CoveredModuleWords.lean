import SuperpermutationUpperBound.Assembly.CoveredComponents
import SuperpermutationUpperBound.Assembly.CircleModules

namespace SuperpermutationUpperBound
variable {E C α : Type} [Fintype E] [Fintype C] {h : Nat}

/-- A finite connector cover supplies at most one closed module per selected
circle, with all rotations available as equally long cut-word choices. -/
theorem covered_circle_module_words (payload : E → MacroEdge α h)
    (cycles : List (List E)) (circle : C → List α) (cut : C → Nat → E)
    (required : E → Prop) (P : α → Prop) (hh : 0 < h)
    (hc : ClosedCycles (fun e => (payload e).source) (fun e => (payload e).target) cycles)
    (hi : cycles.flatten.Perm Finset.univ.toList)
    (hlen : ∀ c, (circle c).length = h)
    (hcut : ∀ c j, j < h → (payload (cut c j)).cost = 1 ∧
      (payload (cut c j)).source = rot (circle c) j ∧
      (payload (cut c j)).target = rot (circle c) (j + 1))
    (hconnected : ∀ c j, j < h → EdgeConnected
      (fun e => (payload e).source) (fun e => (payload e).target) (cut c 0) (cut c j))
    (hcover : ∀ e, ∃ c, EdgeConnected
      (fun e => (payload e).source) (fun e => (payload e).target) e (cut c 0))
    (hrequired : ∀ e, required e → ∀ c j, j < h → e ≠ cut c j)
    (hs : ∀ e, ∀ a ∈ (payload e).word, P a) :
    ∃ modules : List (List E), ∃ chosenCircle : Fin modules.length → C,
      ∃ words : Fin modules.length → Nat → List α,
      ClosedCycles (fun e => (payload e).source) (fun e => (payload e).target) modules ∧
      modules.flatten.Perm Finset.univ.toList ∧ modules.length ≤ Fintype.card C ∧
      (∀ i j, j < h →
        (words i j).length = (modules[i.val].map (fun e => (payload e).cost)).sum - 1 + h ∧
        (words i j).take h = rot (circle (chosenCircle i)) (j + 1) ∧
        (words i j).drop ((words i j).length - h) = rot (circle (chosenCircle i)) j ∧
        (∀ e ∈ modules[i.val], required e → (payload e).word.IsInfix (words i j)) ∧
        (∀ a ∈ words i j, P a)) ∧
      (∀ i ell, ell ≤ h →
        ((List.range h).map (fun j => (words i j).take ell)).Perm
          ((List.range h).map (fun j => (words i j).drop ((words i j).length - ell)))) ∧
      ∀ i : Fin modules.length, cut (chosenCircle i) 0 ∈ modules[i.val] := by
  classical
  obtain ⟨modules, hm, hmi, hd, hmarker, hbound⟩ :=
    covered_closed_components (fun e => (payload e).source) (fun e => (payload e).target)
      cycles (fun c => cut c 0) hc hi hcover
  have hall : ∀ e, ∃ es ∈ modules, e ∈ es :=
    fun e => List.mem_flatten.mp (hmi.mem_iff.mpr (by simp))
  have hcchoice : ∀ i : Fin modules.length, ∃ c, cut c 0 ∈ modules[i.val] :=
    fun i => hmarker _ (List.getElem_mem i.isLt)
  choose chosenCircle hchosen using hcchoice
  have hcuts : ∀ i : Fin modules.length, ∀ j, j < h → cut (chosenCircle i) j ∈ modules[i.val] := by
    intro i j hj
    exact (hconnected (chosenCircle i) j hj).same_cycle hd hall
      (List.getElem_mem i.isLt) (hchosen i)
  have hw : ∀ i : Fin modules.length, ∃ words : Nat → List α,
      (∀ j, j < h → (words j).length = (modules[i.val].map (fun e => (payload e).cost)).sum - 1 + h ∧
        (words j).take h = rot (circle (chosenCircle i)) (j + 1) ∧
        (words j).drop ((words j).length - h) = rot (circle (chosenCircle i)) j ∧
        (∀ e ∈ modules[i.val], required e → (payload e).word.IsInfix (words j)) ∧
        (∀ a ∈ words j, P a)) ∧
      ∀ ell, ell ≤ h →
        ((List.range h).map (fun j => (words j).take ell)).Perm
          ((List.range h).map (fun j => (words j).drop ((words j).length - ell))) := by
    intro i
    exact circle_module_cut_words payload modules[i.val] (circle (chosenCircle i))
      (cut (chosenCircle i)) required P (hlen _) hh (hm _ (List.getElem_mem i.isLt)).2
      (fun j hj => ⟨hcuts i j hj, hcut _ j hj⟩)
      (fun e he j hj => hrequired e he _ j hj) (fun e _ => hs e)
  choose words hwords using hw
  exact ⟨modules, chosenCircle, words, hm, hmi, hbound, fun i => (hwords i).1,
    (fun i => (hwords i).2), hchosen⟩

end SuperpermutationUpperBound
