import SuperpermutationUpperBound.TrailSpelling
import SuperpermutationUpperBound.Foundation.WordSupport

namespace SuperpermutationUpperBound

/-- A directed edge carrying an actual word and an overlap length. Endpoints
are its literal prefix and suffix, and cost is the number of appended letters. -/
structure MacroEdge (α : Type) (h : Nat) where
  word : List α
  length_ge : h ≤ word.length

namespace MacroEdge
variable {α : Type} {h : Nat}

def source (e : MacroEdge α h) : List α := e.word.take h

def target (e : MacroEdge α h) : List α := e.word.drop (e.word.length - h)

def cost (e : MacroEdge α h) : Nat := e.word.length - h

@[simp] theorem source_length (e : MacroEdge α h) : e.source.length = h := by
  simp [source, Nat.min_eq_left e.length_ge]

@[simp] theorem target_length (e : MacroEdge α h) : e.target.length = h := by
  simp only [target, List.length_drop]
  have := e.length_ge
  omega

theorem word_length (e : MacroEdge α h) : e.word.length = e.cost + h := by
  unfold cost
  have := e.length_ge
  omega

theorem overlapCompatible {e f : MacroEdge α h} (hc : e.target = f.source) :
    OverlapCompatible h e.word f.word := ⟨e.length_ge, f.length_ge, hc⟩

/-- A row word as a macro edge. -/
def ofRow (K : Nat) (r : Row α) (hlen : r.base.length + 1 = K) : MacroEdge α (K - 3) :=
  ⟨r.word, r.word_length_ge_endpoint hlen⟩

theorem ofRow_source (K : Nat) (r : Row α) (hlen : r.base.length + 1 = K) :
    (ofRow K r hlen).source = r.head := by
  change r.word.take (K - 3) = _
  rw [show K - 3 = r.base.length - 2 by omega]
  exact r.word_take_head

theorem ofRow_target (K : Nat) (r : Row α) (hlen : r.base.length + 1 = K)
    (hK : 4 ≤ K) (hv : 1 ≤ r.visible) : (ofRow K r hlen).target = r.tail := by
  change r.word.drop (r.word.length - (K - 3)) = _
  rw [show K - 3 = r.base.length - 2 by omega]
  exact r.word_drop_tail hv (by omega)

theorem ofRow_cost (K : Nat) (r : Row α) (hlen : r.base.length + 1 = K)
    (hK : 4 ≤ K) (hv : 1 ≤ r.visible) : (ofRow K r hlen).cost = (K + 1) * r.visible + 1 := by
  have hl := r.word_length_affine hlen hK hv
  change r.word.length - (K - 3) = _
  omega

/-- One ordinary shift edge appends exactly one letter. -/
def ordinary (x : List α) (hx : x.length = h) (a : α) : MacroEdge α h :=
  ⟨x ++ [a], by simp [hx]⟩

theorem ordinary_source (x : List α) (hx : x.length = h) (a : α) :
    (ordinary x hx a).source = x := by
  change (x ++ [a]).take h = x
  rw [← hx, List.take_append_length]

theorem ordinary_target (x : List α) (hx : x.length = h) (hpos : 0 < h) (a : α) :
    (ordinary x hx a).target = x.drop 1 ++ [a] := by
  change (x ++ [a]).drop ((x ++ [a]).length - h) = _
  simp only [List.length_append, List.length_singleton, hx, Nat.add_sub_cancel_left]
  rw [List.drop_append]
  simp [Nat.sub_eq_zero_of_le (by omega : 1 ≤ x.length)]

@[simp] theorem ordinary_cost (x : List α) (hx : x.length = h) (a : α) :
    (ordinary x hx a).cost = 1 := by
  simp [cost, ordinary, hx]

end MacroEdge
end SuperpermutationUpperBound
