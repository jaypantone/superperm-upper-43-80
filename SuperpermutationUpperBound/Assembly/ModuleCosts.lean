import SuperpermutationUpperBound.Assembly.CoveredModuleWords
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Fin

namespace SuperpermutationUpperBound
variable {E : Type}

theorem list_index_sum (xs : List E) (f : E → Nat) :
    (∑ i : Fin xs.length, f xs[i.val]) = (xs.map f).sum := by
  have he : List.ofFn (fun i : Fin xs.length => f xs[i.val]) = xs.map f := by
    calc
      _ = (List.ofFn xs.get).map f := by rw [List.map_ofFn]; rfl
      _ = _ := by rw [List.ofFn_get]
  rw [← List.sum_ofFn, he]

theorem sum_index_module_costs (modules : List (List E)) (cost : E → Nat) :
    (∑ i : Fin modules.length, (modules[i.val].map cost).sum) =
      (modules.flatten.map cost).sum := by
  rw [list_index_sum modules (fun es => (es.map cost).sum)]
  simp only [List.map_flatten, List.sum_flatten, List.map_map, Function.comp_def]

theorem cost_sum_pos_of_one (cost : E → Nat) {es : List E} {e : E}
    (he : e ∈ es) (hc : cost e = 1) : 1 ≤ (es.map cost).sum := by
  obtain ⟨left, right, rfl, _⟩ := List.eq_append_cons_of_mem he
  simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons, hc]
  omega

/-- One cost-one edge is removed per module, then its full endpoint is
included. The resulting total charge is `(h-1)` per module. -/
theorem sum_cut_module_lengths (modules : List (List E)) (cost : E → Nat)
    (lengths : Fin modules.length → Nat) (h : Nat) (hh : 0 < h)
    (hcost : ∀ i : Fin modules.length, 1 ≤ (modules[i.val].map cost).sum)
    (hlen : ∀ i : Fin modules.length, lengths i = (modules[i.val].map cost).sum - 1 + h) :
    (∑ i, lengths i) = (modules.flatten.map cost).sum + (h - 1) * modules.length := by
  have he : ∀ i : Fin modules.length, lengths i = (modules[i.val].map cost).sum + (h - 1) := by
    intro i
    have hc := hcost i
    rw [hlen]
    omega
  simp_rw [he]
  rw [Finset.sum_add_distrib, sum_index_module_costs]
  simp [Nat.mul_comm]

end SuperpermutationUpperBound

namespace SuperpermutationUpperBound
variable {I E : Type} [Fintype I]

theorem finite_family_cost_sum (family : I → List E) (cost : E → Nat) :
    (∑ i, ((family i).map cost).sum) =
      (((Finset.univ.toList : List I).flatMap family).map cost).sum := by
  classical
  calc
    _ = (Finset.univ.toList.map (fun i => ((family i).map cost).sum)).sum := by
      simpa only [Finset.toList_toFinset] using
        List.sum_toFinset (fun i => ((family i).map cost).sum) (Finset.nodup_toList Finset.univ)
    _ = _ := by
      simp only [List.flatMap_def, List.map_flatten, List.sum_flatten, List.map_map,
        Function.comp_def]

theorem finite_family_length_sum (family : I → List E) :
    (∑ i, (family i).length) = ((Finset.univ.toList : List I).flatMap family).length := by
  simpa using finite_family_cost_sum family (fun _ => 1)

end SuperpermutationUpperBound
