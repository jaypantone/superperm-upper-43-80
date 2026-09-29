import SuperpermutationUpperBound.TrailSpelling

/-! Literal relabeling of row data and occurrence lists. Compatibility and
closure need no injectivity assumption; validity does. -/
namespace SuperpermutationUpperBound

variable {α β γ : Type}

/-- Relabeling commutes with literal left rotation at the same distance. -/
theorem rot_map (f : α → β) (x : List α) (j : Nat) :
    rot (x.map f) j = (rot x j).map f := by
  simp only [rot_eq_drop_append_take, List.length_map, List.map_append,
    List.map_drop, List.map_take]

/-- Relabel every letter while retaining the row occurrence and visible length. -/
def Row.map (f : α → β) (r : Row α) : Row β :=
  ⟨r.base.map f, f r.satellite, r.visible⟩

@[simp] theorem Row.map_base (f : α → β) (r : Row α) :
    (r.map f).base = r.base.map f := rfl

@[simp] theorem Row.map_satellite (f : α → β) (r : Row α) :
    (r.map f).satellite = f r.satellite := rfl

@[simp] theorem Row.map_visible (f : α → β) (r : Row α) :
    (r.map f).visible = r.visible := rfl

@[simp] theorem Row.map_base_length (f : α → β) (r : Row α) :
    (r.map f).base.length = r.base.length := List.length_map f

@[simp] theorem Row.map_charge (f : α → β) (r : Row α) :
    (r.map f).charge = r.charge := by simp only [Row.charge, Row.map_base_length, Row.map_visible]

@[simp] theorem Row.map_head (f : α → β) (r : Row α) :
    (r.map f).head = r.head.map f := by
  simp only [Row.head, Row.map_base, List.length_map, List.map_take]

@[simp] theorem Row.map_tail (f : α → β) (r : Row α) :
    (r.map f).tail = r.tail.map f := by
  change (rot (r.base.map f) (r.visible + 1)).take ((r.base.map f).length - 2) = _
  simp only [rot_map, List.length_map, Row.tail, List.map_take]

@[simp] theorem Row.map_entry (f : α → β) (r : Row α) (j : Nat) :
    (r.map f).entry j = (r.entry j).map f := by
  change rot (r.base.map f) j ++ [f r.satellite] = _
  simp only [rot_map, Row.entry, List.map_append, List.map_cons, List.map_nil]

theorem Row.map_valid (f : α → β) (hf : ∀ a b, f a = f b → a = b)
    {r : Row α} (hr : r.Valid) : (r.map f).Valid := by
  refine ⟨?_, ?_, hr.2.2.1, ?_⟩
  · apply List.pairwise_map.mpr
    exact List.Pairwise.imp (fun {a b} hab he => hab (hf a b he)) hr.1
  · intro hmem
    obtain ⟨a, ha, he⟩ := List.mem_map.mp hmem
    have heq : a = r.satellite := hf a r.satellite he
    exact hr.2.1 (heq ▸ ha)
  · simpa only [Row.map_visible, Row.map_base_length] using hr.2.2.2

theorem Row.assigned_map (f : α → β) {r : Row α} {p : List α}
    (hp : r.Assigned p) : (r.map f).Assigned (p.map f) := by
  obtain ⟨j, hj, i, hi, rfl⟩ := hp
  refine ⟨j, hj, i, by simpa using hi, ?_⟩
  rw [Row.map_entry]
  exact (rot_map f (r.entry j) i).symm

theorem rowSpellingAux_map (f : α → β) (x : List α) (s : α) (t : Nat) :
    rowSpellingAux (x.map f) (f s) t = (rowSpellingAux x s t).map f := by
  induction t with
  | zero => simp only [rowSpellingAux, cycleSpelling, List.map_append, List.map_cons, List.map_nil]
  | succ t ih =>
    simp only [rowSpellingAux, ih, rot_map, List.map_append, List.map_take,
      List.map_cons, List.map_nil]

@[simp] theorem Row.map_word (f : α → β) (r : Row α) :
    (r.map f).word = r.word.map f := rowSpellingAux_map f r.base r.satellite _

theorem Row.compatible_map (f : α → β) {r t : Row α} (h : r.Compatible t) :
    (r.map f).Compatible (t.map f) := by
  unfold Row.Compatible at h ⊢
  rw [Row.map_tail, Row.map_head, h]

theorem rowTrailCompatible_map (f : α → β) {first : Row α} {rest : List (Row α)}
    (hc : RowTrailCompatible first rest) :
    RowTrailCompatible (first.map f) (rest.map (Row.map f)) := by
  induction rest generalizing first with
  | nil => trivial
  | cons next rest ih => exact ⟨Row.compatible_map f hc.1, ih hc.2⟩

/-- Every adjacent equality, including the closing boundary, survives relabeling. -/
theorem cyclicallyCompatible_map (f : α → β) {rs : List (Row α)}
    (hc : CyclicallyCompatible rs) : CyclicallyCompatible (rs.map (Row.map f)) := by
  intro pair hp
  change pair ∈ (rs.map (Row.map f)).zip (rot (rs.map (Row.map f)) 1) at hp
  rw [rot_map, List.zip_map] at hp
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hp
  exact Row.compatible_map f (hc old hold)

/-- Row occurrence lists remain closed without any endpoint-disjointness premise. -/
theorem closedTrail_map (f : α → β) {rs : List (Row α)} (hc : ClosedTrail rs) :
    ClosedTrail (rs.map (Row.map f)) := by
  refine ⟨?_, cyclicallyCompatible_map f hc.2⟩
  intro hnil
  exact hc.1 (List.map_eq_nil_iff.mp hnil)

#print axioms rot_map
#print axioms Row.map_valid
#print axioms Row.assigned_map
#print axioms Row.map_word
#print axioms rowTrailCompatible_map
#print axioms cyclicallyCompatible_map
#print axioms closedTrail_map

end SuperpermutationUpperBound
