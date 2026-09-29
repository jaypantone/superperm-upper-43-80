import SuperpermutationUpperBound.Assembly.CoveredComponents
import SuperpermutationUpperBound.Assembly.CircleModules

namespace SuperpermutationUpperBound
variable {α : Type}

/-- The ordinary edge from one rotation vertex to the next appends the
current first letter. -/
def rotationEdge (x : List α) (hx : 0 < x.length) (j : Nat) : MacroEdge α x.length :=
  MacroEdge.ordinary (rot x j) (rot_length x j) ((rot x j)[0]'(by simpa using hx))

@[simp] theorem rotationEdge_source (x : List α) (hx : 0 < x.length) (j : Nat) :
    (rotationEdge x hx j).source = rot x j := MacroEdge.ordinary_source ..

@[simp] theorem rotationEdge_cost (x : List α) (hx : 0 < x.length) (j : Nat) :
    (rotationEdge x hx j).cost = 1 := MacroEdge.ordinary_cost ..

@[simp] theorem rotationEdge_target (x : List α) (hx : 0 < x.length) (j : Nat) :
    (rotationEdge x hx j).target = rot x (j + 1) := by
  rw [rotationEdge, MacroEdge.ordinary_target _ _ hx]
  rw [← rot_add, rot_eq_drop_append_take_of_le _ 1 (by simpa only [rot_length] using Nat.succ_le_of_lt hx)]
  congr 1
  rw [List.take_succ_eq_append_getElem (i := 0) (by simpa only [rot_length] using hx)]
  simp

theorem rotationEdge_support (x : List α) (hx : 0 < x.length) (j : Nat) :
    ∀ a ∈ (rotationEdge x hx j).word, a ∈ x := by
  intro a ha
  change a ∈ rot x j ++ [_] at ha
  rcases List.mem_append.mp ha with ha | ha
  · exact (rot_perm x j).mem_iff.mp ha
  · have he : a = (rot x j)[0]'(by simpa using hx) := List.mem_singleton.mp ha
    rw [he]
    exact (rot_perm x j).mem_iff.mp (List.getElem_mem (by simpa using hx))

/-- Consecutive rotation edge labels form a literal directed path. -/
theorem rotationEdge_path (x : List α) (hx : 0 < x.length) (j k : Nat) :
    EdgePath (fun i => (rotationEdge x hx i).source) (fun i => (rotationEdge x hx i).target)
      (rot x j) (List.range' j k) (rot x (j + k)) := by
  induction k generalizing j with
  | zero =>
    simpa only [List.range'_zero, Nat.add_zero] using
      (EdgePath.nil (src := fun i => (rotationEdge x hx i).source)
        (dst := fun i => (rotationEdge x hx i).target) (rot x j))
  | succ k ih =>
    rw [List.range'_succ]
    refine EdgePath.cons (src := fun i => (rotationEdge x hx i).source)
      (dst := fun i => (rotationEdge x hx i).target) (e := j) (rotationEdge_source x hx j) ?_
    simpa only [rotationEdge_target, Nat.add_assoc, Nat.add_comm 1 k] using ih (j + 1)

/-- One complete rotation circle, with a separate edge occurrence for each
position even if endpoint values repeat. -/
theorem rotationEdge_closed (x : List α) (hx : 0 < x.length) :
    EdgePath (fun i => (rotationEdge x hx i).source) (fun i => (rotationEdge x hx i).target)
      x (List.range x.length) x := by
  simpa [← List.range_eq_range'] using rotationEdge_path x hx 0 x.length

end SuperpermutationUpperBound

namespace SuperpermutationUpperBound
variable {α : Type} {h : Nat}

/-- A rotation circle as literal macro edges at a specified common length. -/
def rotationMacro (x : List α) (hx : x.length = h) (hh : 0 < h) (j : Nat) : MacroEdge α h :=
  MacroEdge.ordinary (rot x j) ((rot_length x j).trans hx)
    ((rot x j)[0]'(by simp only [rot_length, hx]; exact hh))

@[simp] theorem rotationMacro_source (x : List α) (hx : x.length = h) (hh : 0 < h) (j : Nat) :
    (rotationMacro x hx hh j).source = rot x j := MacroEdge.ordinary_source ..

@[simp] theorem rotationMacro_target (x : List α) (hx : x.length = h) (hh : 0 < h) (j : Nat) :
    (rotationMacro x hx hh j).target = rot x (j + 1) := by
  subst h
  exact rotationEdge_target x hh j

@[simp] theorem rotationMacro_cost (x : List α) (hx : x.length = h) (hh : 0 < h) (j : Nat) :
    (rotationMacro x hx hh j).cost = 1 := MacroEdge.ordinary_cost ..

def rotationMacroCycle (x : List α) (hx : x.length = h) (hh : 0 < h) : List (MacroEdge α h) :=
  (List.range h).map (rotationMacro x hx hh)

theorem rotationMacroCycle_closed (x : List α) (hx : x.length = h) (hh : 0 < h) :
    EdgePath MacroEdge.source MacroEdge.target x (rotationMacroCycle x hx hh) x := by
  subst h
  exact (rotationEdge_closed x hh).map_edges (rotationEdge x hh) (fun _ => rfl) (fun _ => rfl)

@[simp] theorem rotationMacroCycle_length (x : List α) (hx : x.length = h) (hh : 0 < h) :
    (rotationMacroCycle x hx hh).length = h := by simp [rotationMacroCycle]

@[simp] theorem rotationMacroCycle_get (x : List α) (hx : x.length = h) (hh : 0 < h)
    (j : Nat) (hj : j < (rotationMacroCycle x hx hh).length) :
    (rotationMacroCycle x hx hh)[j] = rotationMacro x hx hh j := by
  simp [rotationMacroCycle]

theorem rotationMacroCycle_support (x : List α) (hx : x.length = h) (hh : 0 < h) :
    ∀ e ∈ rotationMacroCycle x hx hh, ∀ a ∈ e.word, a ∈ x := by
  subst h
  intro e he
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp he
  exact rotationEdge_support x hh j

end SuperpermutationUpperBound
