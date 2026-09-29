import SuperpermutationUpperBound.Assembly.RowEdges
import Mathlib.Data.Fintype.BigOperators

namespace SuperpermutationUpperBound
variable {E F V I : Type}

theorem EdgePath.of_map {src dst : E → V} (f : F → E) {a b : V} {es : List F}
    (hp : EdgePath src dst a (es.map f) b) :
    EdgePath (fun e => src (f e)) (fun e => dst (f e)) a es b := by
  induction es generalizing a with
  | nil =>
    have he := hp.eq_of_nil
    subst b
    exact .nil _
  | cons e es ih =>
    exact .cons hp.source_eq_of_cons (ih hp.tail_of_cons)

/-- Replace every occurrence of a path by its index. Equal edge values
therefore receive different labels without changing endpoint equations. -/
theorem EdgePath.indexed {src dst : E → V} {a b : V} {es : List E}
    (hp : EdgePath src dst a es b) :
    EdgePath (fun i : Fin es.length => src es[i.val]) (fun i : Fin es.length => dst es[i.val])
      a (List.finRange es.length) b := by
  apply EdgePath.of_map (fun i : Fin es.length => es[i.val])
  rw [← List.ofFn_eq_map]
  change EdgePath src dst a (List.ofFn es.get) b
  rwa [List.ofFn_get]

/-- Separate row occurrences by their family label and position. -/
abbrev FamilyOccurrence (family : I → List E) := Σ i, Fin (family i).length

def familyOccurrenceValue (family : I → List E) (e : FamilyOccurrence family) : E :=
  (family e.1)[e.2.val]

def familyOccurrenceCycle (family : I → List E) (i : I) : List (FamilyOccurrence family) :=
  (List.finRange (family i).length).map (fun j => ⟨i, j⟩)

theorem familyOccurrenceCycle_values (family : I → List E) (i : I) :
    (familyOccurrenceCycle family i).map (familyOccurrenceValue family) = family i := by
  unfold familyOccurrenceCycle
  rw [List.map_map, ← List.ofFn_eq_map]
  exact List.ofFn_get (family i)

theorem familyOccurrenceCycle_path (family : I → List E) {src dst : E → V}
    (i : I) {a b : V} (hp : EdgePath src dst a (family i) b) :
    EdgePath (fun e => src (familyOccurrenceValue family e))
      (fun e => dst (familyOccurrenceValue family e)) a (familyOccurrenceCycle family i) b := by
  apply EdgePath.of_map
  rwa [familyOccurrenceCycle_values]

end SuperpermutationUpperBound

namespace SuperpermutationUpperBound
variable {E I : Type}

theorem familyOccurrence_inventory [Fintype I] (family : I → List E) :
    ((Finset.univ.toList : List I).flatMap (familyOccurrenceCycle family)).Perm
      (Finset.univ.toList : List (FamilyOccurrence family)) := by
  classical
  have hnd : ((Finset.univ.toList : List I).flatMap (familyOccurrenceCycle family)).Nodup := by
    apply List.nodup_flatMap.mpr
    constructor
    · intro i _
      apply (List.nodup_finRange _).map
      intro a b hab
      exact Sigma.mk.inj_iff.mp hab |>.2 |> eq_of_heq
    · apply (Finset.nodup_toList _).imp
      intro i j hij
      apply List.disjoint_left.mpr
      intro e hei hej
      obtain ⟨p, _, hp⟩ := List.mem_map.mp hei
      obtain ⟨q, _, hq⟩ := List.mem_map.mp hej
      exact hij (congrArg Sigma.fst (hp.trans hq.symm))
  apply (List.perm_ext_iff_of_nodup hnd (Finset.nodup_toList _)).mpr
  intro e
  constructor
  · intro _; simp
  · intro _
    exact List.mem_flatMap.mpr ⟨e.1, by simp,
      List.mem_map.mpr ⟨e.2, List.mem_finRange _, by cases e; rfl⟩⟩

end SuperpermutationUpperBound
