import SuperpermutationUpperBound.Assembly.ModuleCosts
import SuperpermutationUpperBound.BalancedCuts.SupportedCutWords

/-! The actual circle cut words, rounded and assembled with a literal endpoint
state count. Occurrence labels survive both module assembly and cutting. -/
namespace SuperpermutationUpperBound
variable {E C α : Type} [Fintype E] [Fintype C] [DecidableEq α] {h ell : Nat}

omit [DecidableEq α] in
theorem take_short_of_take_eq {w u : List α} (he : w.take h = u) (hl : ell ≤ h) :
    w.take ell = u.take ell := by
  rw [← he, List.take_take, Nat.min_eq_left hl]

omit [DecidableEq α] in
theorem drop_short_of_drop_eq {w u : List α} (he : w.drop (w.length - h) = u)
    (hh : h ≤ w.length) (hl : ell ≤ h) :
    w.drop (w.length - ell) = u.drop (h - ell) := by
  rw [← he, List.drop_drop]
  congr 1
  omega

/-- A connector-covered finite edge inventory yields a literal word with the
sharp module ledger and the injective overlap-state bound. -/
theorem balanced_covered_circle_words (payload : E → MacroEdge α h)
    (cycles : List (List E)) (circle : C → List α) (cut : C → Nat → E)
    (required : E → Prop) (P : α → Prop) (A : Finset α)
    (hh : 0 < h) (hell : ell ≤ h)
    (hc : ClosedCycles (fun e => (payload e).source) (fun e => (payload e).target) cycles)
    (hi : cycles.flatten.Perm Finset.univ.toList)
    (hlen : ∀ c, (circle c).length = h)
    (hnd : ∀ c, (circle c).Nodup)
    (hA : ∀ c, ∀ a ∈ circle c, a ∈ A)
    (hcut : ∀ c j, j < h → (payload (cut c j)).cost = 1 ∧
      (payload (cut c j)).source = rot (circle c) j ∧
      (payload (cut c j)).target = rot (circle c) (j + 1))
    (hconnected : ∀ c j, j < h → EdgeConnected
      (fun e => (payload e).source) (fun e => (payload e).target) (cut c 0) (cut c j))
    (hcover : ∀ e, ∃ c, EdgeConnected
      (fun e => (payload e).source) (fun e => (payload e).target) e (cut c 0))
    (hrequired : ∀ e, required e → ∀ c j, j < h → e ≠ cut c j)
    (hs : ∀ e, ∀ a ∈ (payload e).word, P a) :
    ∃ modules : List (List E), ∃ J : Nat, ∃ w : List α,
      modules.flatten.Perm Finset.univ.toList ∧
      modules.length ≤ Fintype.card C ∧
      J ≤ min modules.length (A.card.descFactorial ell) ∧
      w.length = (Finset.univ.toList.map (fun e => (payload e).cost)).sum +
        (h - 1) * modules.length - ell * (modules.length - J) ∧
      (∀ e, required e → (payload e).word.IsInfix w) ∧ ∀ a ∈ w, P a := by
  classical
  obtain ⟨modules, chosen, words, _hm, hmi, hmcount, hw, hbal, hmarker⟩ :=
    covered_circle_module_words payload cycles circle cut required P hh hc hi hlen
      hcut hconnected hcover hrequired hs
  let lengths : Fin modules.length → Nat :=
    fun i => (modules[i.val].map (fun e => (payload e).cost)).sum - 1 + h
  have hcost : ∀ i : Fin modules.length,
      1 ≤ (modules[i.val].map (fun e => (payload e).cost)).sum := by
    intro i
    exact cost_sum_pos_of_one _ (hmarker i) (hcut (chosen i) 0 hh).1
  have hwordlen : ∀ i j, j < h → (words i j).length = lengths i :=
    fun i j hj => (hw i j hj).1
  have hlong : ∀ i, h ≤ lengths i := by
    intro i
    simp only [lengths]
    omega
  have hprefix : ∀ c : Fin modules.length × Fin h,
      (words c.1 c.2.val).take ell = (rot (circle (chosen c.1)) (c.2.val + 1)).take ell :=
    fun c => take_short_of_take_eq (hw c.1 c.2.val c.2.isLt).2.1 hell
  have hsuffix : ∀ c : Fin modules.length × Fin h,
      (words c.1 c.2.val).drop ((words c.1 c.2.val).length - ell) =
        (rot (circle (chosen c.1)) c.2.val).drop (h - ell) := by
    intro c
    exact drop_short_of_drop_eq (hw c.1 c.2.val c.2.isLt).2.2.1
      (by rw [hwordlen _ _ c.2.isLt]; exact hlong c.1) hell
  have hp : ∀ c : Fin modules.length × Fin h,
      ((words c.1 c.2.val).take ell).Nodup ∧
        ∀ a ∈ (words c.1 c.2.val).take ell, a ∈ A := by
    intro c
    rw [hprefix]
    refine ⟨((rot_perm _ _).nodup_iff.mpr (hnd _ )).take, ?_⟩
    intro a ha
    exact hA _ a ((rot_perm _ _).mem_iff.mp (List.mem_of_mem_take ha))
  have ht : ∀ c : Fin modules.length × Fin h,
      ((words c.1 c.2.val).drop ((words c.1 c.2.val).length - ell)).Nodup ∧
        ∀ a ∈ (words c.1 c.2.val).drop ((words c.1 c.2.val).length - ell), a ∈ A := by
    intro c
    rw [hsuffix]
    refine ⟨((rot_perm _ _).nodup_iff.mpr (hnd _ )).drop, ?_⟩
    intro a ha
    exact hA _ a ((rot_perm _ _).mem_iff.mp (List.mem_of_mem_drop ha))
  have hb : ∀ i : Fin modules.length,
      ((List.finRange h).map (fun j => (words i j.val).take ell)).Perm
        ((List.finRange h).map (fun j => (words i j.val).drop ((words i j.val).length - ell))) := by
    intro i
    simpa only [← map_val_finRange h, List.map_map, Function.comp_def] using hbal i ell hell
  obtain ⟨selected, J, w, hJ, hwlen, hocc, hsupport⟩ :=
    BalancedCuts.balanced_supported_cut_words (fun c => words c.1 c.2.val) lengths A hh
      (fun c => hwordlen _ _ c.2.isLt) (fun i => hell.trans (hlong i)) hp ht hb P
      (fun c => (hw c.1 c.2.val c.2.isLt).2.2.2.2)
  have hsum := sum_cut_module_lengths modules (fun e => (payload e).cost) lengths h hh hcost
    (fun _ => rfl)
  have htotal := (hmi.map (fun e => (payload e).cost)).sum_eq
  refine ⟨modules, J, w, hmi, hmcount, by simpa using hJ, ?_, ?_, hsupport⟩
  · simpa only [Fintype.card_fin, hsum, htotal] using hwlen
  · intro e he
    obtain ⟨es, hes, hees⟩ := List.mem_flatten.mp (hmi.mem_iff.mpr (by simp : e ∈ Finset.univ.toList))
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hes
    let ix : Fin modules.length := ⟨i, hi⟩
    exact ((hw ix (selected ix).val (selected ix).isLt).2.2.2.1 e hees he).trans (hocc ix)

end SuperpermutationUpperBound
