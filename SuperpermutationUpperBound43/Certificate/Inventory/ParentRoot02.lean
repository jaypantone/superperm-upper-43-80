import SuperpermutationUpperBound43.Certificate.Inventory.Merge012
import Mathlib.Tactic.NormNum

namespace SuperpermutationUpperBound43.Certificate.Inventory.ParentRoot02
open SuperpermutationUpperBound
open SuperpermutationUpperBound.Certificates.NineRecipe

set_option maxRecDepth 500000
set_option maxHeartbeats 512000000

def input : List Nat := parent2.map (fun r => key (canonical r.base))
def data : List Nat := Merge012.data

theorem chunk_shape (rs : List (Row Nat)) :
    ((((((rs.drop 0).take 512).map (fun r => key (canonical r.base))) ++ (((rs.drop 512).take 512).map (fun r => key (canonical r.base)))) ++ ((((rs.drop 1024).take 512).map (fun r => key (canonical r.base))) ++ (((rs.drop 1536).take 512).map (fun r => key (canonical r.base))))) ++ ((((rs.drop 2048).take 512).map (fun r => key (canonical r.base))) ++ (((rs.drop 2560).take 512).map (fun r => key (canonical r.base))))) =
      (rs.take 3072).map (fun r => key (canonical r.base)) := by
  have h := mapped_chunkRows rs 512 6 (fun r => key (canonical r.base))
  norm_num [List.range_succ, List.flatMap_append, List.append_assoc] at h
  simpa only [List.drop_zero, List.append_assoc, List.map_take, List.map_drop] using h

theorem input_eq : Merge012.input = input := by
  have ht : parent2.length ≤ 3072 := by
    rw [parent2_counts.1]
    decide
  have he : Merge012.input =
      (parent2.take 3072).map (fun r => key (canonical r.base)) := by
    change ((((((parent2.drop 0).take 512).map (fun r => key (canonical r.base))) ++ (((parent2.drop 512).take 512).map (fun r => key (canonical r.base)))) ++ ((((parent2.drop 1024).take 512).map (fun r => key (canonical r.base))) ++ (((parent2.drop 1536).take 512).map (fun r => key (canonical r.base))))) ++ ((((parent2.drop 2048).take 512).map (fun r => key (canonical r.base))) ++ (((parent2.drop 2560).take 512).map (fun r => key (canonical r.base))))) = _
    exact chunk_shape parent2
  rw [List.take_of_length_le ht] at he
  exact he

theorem perm : data.Perm input :=
  Merge012.perm.trans (List.Perm.of_eq input_eq)

end SuperpermutationUpperBound43.Certificate.Inventory.ParentRoot02
