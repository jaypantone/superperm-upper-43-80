import SuperpermutationUpperBound43.Certificate.Parent00
import SuperpermutationUpperBound43.Certificate.Parent01
import SuperpermutationUpperBound43.Certificate.Parent02
import SuperpermutationUpperBound43.Certificate.Parent03
import SuperpermutationUpperBound43.Certificate.Parent04
import SuperpermutationUpperBound43.Certificate.Parent05
import SuperpermutationUpperBound43.Certificate.Parent06
import SuperpermutationUpperBound43.Certificate.Parent07
import SuperpermutationUpperBound43.Certificate.Parent08
import SuperpermutationUpperBound43.Certificate.Parent09
import SuperpermutationUpperBound43.Certificate.Parent10
import SuperpermutationUpperBound43.Certificate.Parent11
import SuperpermutationUpperBound43.Certificate.Parent12
import SuperpermutationUpperBound43.Certificate.Parent13
import SuperpermutationUpperBound43.Certificate.Charts
import SuperpermutationUpperBound43.Certificate.Canonical
import SuperpermutationUpperBound.Certificates.CirclePointers
import Mathlib.Tactic.NormNum

/-! Assemble the checked ordered parents without changing their indices. -/
namespace SuperpermutationUpperBound43.Certificate

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.Certificates.CircleBase

def components : List (List (Row Nat)) :=
  [parent0, parent1, parent2, parent3, parent4, parent5, parent6,
   parent7, parent8, parent9, parent10, parent11, parent12, parent13] ++ charts

def rows : List (Row Nat) := components.flatten

def family (i : Fin 350) : List (Row Nat) := componentAt components i.val

abbrev familyFin350 := family

theorem components_count : components.length = 350 := by
  simp [components, charts_count]

theorem components_basedOn : ∀ rs ∈ components, BasedOn baseAlphabet 9 rs := by
  intro rs hrs
  rcases List.mem_append.mp hrs with hm | hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact parent0_basedOn
    · exact parent1_basedOn
    · exact parent2_basedOn
    · exact parent3_basedOn
    · exact parent4_basedOn
    · exact parent5_basedOn
    · exact parent6_basedOn
    · exact parent7_basedOn
    · exact parent8_basedOn
    · exact parent9_basedOn
    · exact parent10_basedOn
    · exact parent11_basedOn
    · exact parent12_basedOn
    · exact parent13_basedOn
  · exact charts_basedOn rs hc

theorem components_shape : ∀ rs ∈ components, ∀ r ∈ rs,
    r.base.length = 9 ∧ r.satellite = 9 ∧
      (r.visible = r.base.length ∨ r.visible = r.base.length - 2) := by
  intro rs hrs r hr
  have hb := components_basedOn rs hrs r hr
  exact ⟨hb.2.1.length_eq, hb.2.2⟩

theorem components_closed : ∀ rs ∈ components, ClosedTrail rs := by
  intro rs hrs
  rcases List.mem_append.mp hrs with hm | hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact parent0_closed
    · exact parent1_closed
    · exact parent2_closed
    · exact parent3_closed
    · exact parent4_closed
    · exact parent5_closed
    · exact parent6_closed
    · exact parent7_closed
    · exact parent8_closed
    · exact parent9_closed
    · exact parent10_closed
    · exact parent11_closed
    · exact parent12_closed
    · exact parent13_closed
  · exact charts_closed rs hc

theorem components_winding : ∀ rs ∈ components, (8 : Int) ∣ signedExcess rs := by
  intro rs hrs
  rcases List.mem_append.mp hrs with hm | hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact parent0_winding
    · exact parent1_winding
    · exact parent2_winding
    · exact parent3_winding
    · exact parent4_winding
    · exact parent5_winding
    · exact parent6_winding
    · exact parent7_winding
    · exact parent8_winding
    · exact parent9_winding
    · exact parent10_winding
    · exact parent11_winding
    · exact parent12_winding
    · exact parent13_winding
  · exact charts_winding rs hc

theorem components_closed_winding : ∀ rs ∈ components,
    ClosedTrail rs ∧ (8 : Int) ∣ signedExcess rs :=
  fun rs hrs => ⟨components_closed rs hrs, components_winding rs hrs⟩

theorem rows_basedOn : BasedOn baseAlphabet 9 rows := by
  intro r hr
  obtain ⟨rs, hrs, hr⟩ := List.mem_flatten.mp hr
  exact components_basedOn rs hrs r hr

theorem rows_count : rows.length = 40320 := by
  simp only [rows, components, List.flatten_append, List.flatten_cons,
    List.flatten_nil, List.length_append, List.length_nil,
    parent0_counts.1, parent1_counts.1, parent2_counts.1, parent3_counts.1,
    parent4_counts.1, parent5_counts.1, parent6_counts.1, parent7_counts.1,
    parent8_counts.1, parent9_counts.1, parent10_counts.1, parent11_counts.1,
    parent12_counts.1, parent13_counts.1, charts_counts.1] <;> norm_num

theorem rows_charge : (rows.map Row.charge).sum = 18816 := by
  simp only [rows, components, List.flatten_append, List.flatten_cons,
    List.flatten_nil, List.map_append, List.map_nil, List.sum_append, List.sum_nil,
    parent0_counts.2, parent1_counts.2, parent2_counts.2, parent3_counts.2,
    parent4_counts.2, parent5_counts.2, parent6_counts.2, parent7_counts.2,
    parent8_counts.2, parent9_counts.2, parent10_counts.2, parent11_counts.2,
    parent12_counts.2, parent13_counts.2, charts_counts.2] <;> norm_num

theorem rows_counts : rows.length = 40320 ∧ (rows.map Row.charge).sum = 18816 :=
  ⟨rows_count, rows_charge⟩

theorem family_list : (List.finRange 350).map family = components := by
  apply List.ext_getElem
  · simp [components_count]
  · intro i hi hj
    simp [family, componentAt, List.getElem?_eq_getElem hj]

theorem family_rows : (List.finRange 350).flatMap family = rows := by
  simp only [List.flatMap_def, family_list, rows]

theorem family_inventory : ((List.finRange 350).flatMap family).Perm rows :=
  List.Perm.of_eq family_rows

theorem family_basedOn (i : Fin 350) : BasedOn baseAlphabet 9 (family i) :=
  components_basedOn _ (componentAt_mem _ i.val (by
    rw [components_count]
    exact i.isLt))

theorem family_closed_winding (i : Fin 350) :
    ClosedTrail (family i) ∧ (8 : Int) ∣ signedExcess (family i) :=
  components_closed_winding _ (componentAt_mem _ i.val (by
    rw [components_count]
    exact i.isLt))

end SuperpermutationUpperBound43.Certificate
