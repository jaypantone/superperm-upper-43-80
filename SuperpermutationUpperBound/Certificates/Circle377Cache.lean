import SuperpermutationUpperBound.Certificates.Circle377Rows
import Mathlib.Tactic.FinCases

namespace SuperpermutationUpperBound.Certificates.Circle377Cache
open CircleBase Circle377Rows

def literalPrefix : List (List (Row Nat)) := [data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17, data18, data19, data20, data21, data22, data23, data24, data25, data26, data27]

theorem literalPrefix_length : literalPrefix.length = 28 := by rfl

theorem literalPrefix_get (i : Fin 28) : componentAt components9 i.val = literalPrefix[i.val] := by
  fin_cases i
  · exact component_0
  · exact component_1
  · exact component_2
  · exact component_3
  · exact component_4
  · exact component_5
  · exact component_6
  · exact component_7
  · exact component_8
  · exact component_9
  · exact component_10
  · exact component_11
  · exact component_12
  · exact component_13
  · exact component_14
  · exact component_15
  · exact component_16
  · exact component_17
  · exact component_18
  · exact component_19
  · exact component_20
  · exact component_21
  · exact component_22
  · exact component_23
  · exact component_24
  · exact component_25
  · exact component_26
  · exact component_27

theorem literalPrefix_eq : literalPrefix = components9.take 28 := by
  apply List.ext_getElem
  · simp [literalPrefix_length, components9_count]
  · intro i hi hj
    have hi28 : i < 28 := by simpa only [literalPrefix_length] using hi
    have he := literalPrefix_get ⟨i, hi28⟩
    rw [componentAt_eq_getElem components9 i (by rw [components9_count]; omega)] at he
    simpa only [List.getElem_take] using he.symm

def family : List (List (Row Nat)) := literalPrefix ++ components9.drop 28

theorem family_eq : family = components9 := by
  rw [family, literalPrefix_eq, List.take_append_drop]

theorem family_count : family.length = 364 := by rw [family_eq, components9_count]

end SuperpermutationUpperBound.Certificates.Circle377Cache
