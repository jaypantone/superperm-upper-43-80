import SuperpermutationUpperBound43.Certificate.Inventory.Merge084
import SuperpermutationUpperBound43.Certificate.BaseFacts

namespace SuperpermutationUpperBound43.Certificate.Inventory.Result
open SuperpermutationUpperBound
open SuperpermutationUpperBound.Certificates.NineRecipe

set_option maxRecDepth 500000
set_option maxHeartbeats 512000000

theorem input_eq : Merge084.input =
    rows.map (fun r => key (canonical r.base)) := by
  simp only [Merge071.input, Merge072.input, Merge073.input, Merge074.input, Merge075.input, Merge076.input, Merge077.input, Merge078.input, Merge079.input, Merge080.input, Merge081.input, Merge082.input, Merge083.input, Merge084.input, ParentRoot00.input, ParentRoot01.input, ParentRoot02.input, ParentRoot03.input, ParentRoot04.input, ParentRoot05.input, ParentRoot06.input, ParentRoot07.input, ParentRoot08.input, ParentRoot09.input, ParentRoot10.input, ParentRoot11.input, ParentRoot12.input, ParentRoot13.input, ParentRoot14.input,
    rows, components, List.flatten_append, List.flatten_cons, List.flatten_nil,
    List.map_append, List.map_nil, List.append_nil, List.append_assoc]

theorem sorted_strict : Merge084.data.IsChain (· < ·) := by decide +kernel

theorem keys_perm : Merge084.data.Perm
    (rows.map (fun r => key (canonical r.base))) :=
  Merge084.perm.trans (List.Perm.of_eq input_eq)

theorem keys_nodup : (rows.map (fun r => key (canonical r.base))).Nodup :=
  keys_perm.nodup_iff.mp (List.isChain_iff_pairwise.mp sorted_strict).nodup

theorem normalized_rows_nodup : (rows.map (fun r => canonical r.base)).Nodup :=
  normalized_nodup_of_keys keys_nodup

end SuperpermutationUpperBound43.Certificate.Inventory.Result
