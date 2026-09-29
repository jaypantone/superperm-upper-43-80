import SuperpermutationUpperBound.Rows
import SuperpermutationUpperBound.Foundation.Rotation

/-! The prescribed literal row spelling. The recursion counts additional
visible classes after the first. Each additional class appends the former
first base letter, the satellite, and the new rotated base. -/
namespace SuperpermutationUpperBound

variable {α : Type}

def cycleSpelling (x : List α) (s : α) : List α := x ++ [s] ++ x

def rowSpellingAux (x : List α) (s : α) : Nat → List α
  | 0 => cycleSpelling x s
  | t + 1 => rowSpellingAux x s t ++ (rot x t).take 1 ++ [s] ++ rot x (t + 1)

def Row.word (r : Row α) : List α := rowSpellingAux r.base r.satellite (r.visible - 1)

theorem cycleSpelling_length (x : List α) (s : α) :
    (cycleSpelling x s).length = 2 * x.length + 1 := by
  simp [cycleSpelling]
  omega

theorem rowSpellingAux_length (x : List α) (s : α) (hx : 0 < x.length) (t : Nat) :
    (rowSpellingAux x s t).length = (x.length + 2) * t + 2 * x.length + 1 := by
  induction t with
  | zero => simp [rowSpellingAux, cycleSpelling_length]
  | succ t ih =>
    simp only [rowSpellingAux, List.length_append, List.length_take,
      rot_length, List.length_singleton, ih]
    have hm : min 1 x.length = 1 := Nat.min_eq_left (by omega)
    rw [hm, Nat.mul_succ]
    omega

theorem base_prefix_rowSpellingAux (x : List α) (s : α) (t : Nat) :
    x.IsPrefix (rowSpellingAux x s t) := by
  induction t with
  | zero => exact ⟨[s] ++ x, by simp [rowSpellingAux, cycleSpelling, List.append_assoc]⟩
  | succ t ih =>
    exact ih.trans ⟨(rot x t).take 1 ++ [s] ++ rot x (t+1),
      by simp [rowSpellingAux, List.append_assoc]⟩

theorem rotatedBase_suffix_rowSpellingAux (x : List α) (s : α) (t : Nat) :
    (rot x t).IsSuffix (rowSpellingAux x s t) := by
  cases t with
  | zero => exact ⟨x ++ [s], by simp [rowSpellingAux, cycleSpelling]⟩
  | succ t => exact ⟨rowSpellingAux x s t ++ (rot x t).take 1 ++ [s], rfl⟩

theorem Row.word_length (r : Row α) (hv : 1 ≤ r.visible) (hn : 1 ≤ r.base.length) :
    r.word.length = (r.base.length + 2) * r.visible + r.base.length - 1 := by
  have h := rowSpellingAux_length r.base r.satellite (by omega) (r.visible - 1)
  have heq : r.visible = (r.visible - 1) + 1 := by omega
  change (rowSpellingAux r.base r.satellite (r.visible - 1)).length = _
  rw [h]
  have hm := congrArg (fun v => (r.base.length + 2) * v) heq
  simp only [Nat.mul_succ] at hm
  omega

theorem Row.head_prefix_word (r : Row α) : r.head.IsPrefix r.word := by
  exact (List.take_prefix _ _).trans (base_prefix_rowSpellingAux _ _ _)

theorem Row.word_take_head (r : Row α) :
    r.word.take (r.base.length - 2) = r.head := by
  have h := List.prefix_iff_eq_take.mp r.head_prefix_word
  have hl : r.head.length = r.base.length - 2 := by simp [Row.head]
  simpa only [hl] using h.symm

theorem cycleSpelling_suffix_rowSpellingAux (x : List α) (s : α) (t : Nat) :
    (cycleSpelling (rot x t) s).IsSuffix (rowSpellingAux x s t) := by
  cases t with
  | zero => exact ⟨[], by simp [rowSpellingAux]⟩
  | succ t =>
    obtain ⟨u, hu⟩ := rotatedBase_suffix_rowSpellingAux x s t
    refine ⟨u ++ (rot x t).take 1, ?_⟩
    rw [rowSpellingAux, ← hu]
    unfold cycleSpelling
    rw [rot_add_one x t]
    have heq := append_take_one_eq_take_one_append_rot (rot x t)
    have hh := congrArg (fun q => u ++ q ++ [s] ++ rot (rot x t) 1) heq.symm
    simpa only [List.append_assoc] using hh

theorem cycleSpelling_infix_rowSpellingAux (x : List α) (s : α) (t j : Nat)
    (hj : j ≤ t) :
    (cycleSpelling (rot x j) s).IsInfix (rowSpellingAux x s t) := by
  induction t with
  | zero =>
    have : j = 0 := by omega
    subst j
    exact (cycleSpelling_suffix_rowSpellingAux x s 0).isInfix
  | succ t ih =>
    by_cases h : j ≤ t
    · exact (ih h).trans (List.IsPrefix.isInfix ⟨(rot x t).take 1 ++ [s] ++ rot x (t+1),
        by simp [rowSpellingAux, List.append_assoc]⟩)
    · have : j = t + 1 := by omega
      subst j
      exact (cycleSpelling_suffix_rowSpellingAux x s (t+1)).isInfix

theorem rot_entry_infix_cycleSpelling (x : List α) (s : α) (i : Nat)
    (hi : i < x.length + 1) :
    (rot (x ++ [s]) i).IsInfix (cycleSpelling x s) := by
  have h := rot_isInfix_cycleWord (x ++ [s]) i (by simpa using hi)
  have ht : (x ++ [s]).take ((x ++ [s]).length - 1) = x := by simp
  simpa only [ht, cycleSpelling] using h

/-- Every assigned permutation is a contiguous factor of the prescribed word. -/
theorem Row.assigned_infix_word (r : Row α) {p : List α} (hp : r.Assigned p) :
    p.IsInfix r.word := by
  obtain ⟨j, hj, i, hi, rfl⟩ := hp
  have hc := rot_entry_infix_cycleSpelling (rot r.base j) r.satellite i (by simpa using hi)
  exact hc.trans (cycleSpelling_infix_rowSpellingAux _ _ _ _ (by omega))

theorem Row.tail_suffix_word (r : Row α) (hv : 1 ≤ r.visible)
    (hn : 2 ≤ r.base.length) : r.tail.IsSuffix r.word := by
  have hrot : rot r.base (r.visible + 1) = rot (rot r.base (r.visible - 1)) 2 := by
    rw [rot_add]
    congr 1
    omega
  have he : r.tail = (rot r.base (r.visible - 1)).drop 2 := by
    change (rot r.base (r.visible + 1)).take (r.base.length - 2) = _
    rw [hrot]
    have ht := take_rot_two (rot r.base (r.visible - 1)) (by simpa using hn)
    simpa using ht
  rw [he]
  exact (List.drop_suffix _ _).trans (rotatedBase_suffix_rowSpellingAux _ _ _)

theorem Row.word_drop_tail (r : Row α) (hv : 1 ≤ r.visible)
    (hn : 2 ≤ r.base.length) :
    r.word.drop (r.word.length - (r.base.length - 2)) = r.tail := by
  have h := List.suffix_iff_eq_drop.mp (r.tail_suffix_word hv hn)
  have hl : r.tail.length = r.base.length - 2 := by simp [Row.tail]
  simpa only [hl] using h.symm

/-- Row spelling in the final-alphabet notation of the theorem contract. -/
theorem Row.spelling_spec (r : Row α) {K : Nat} (hK : r.base.length + 1 = K)
    (hsize : 4 ≤ K) (hv : 1 ≤ r.visible) :
    (∀ p, r.Assigned p → p.IsInfix r.word) ∧
    r.word.length = (K + 1) * r.visible + K - 2 ∧
    r.word.take (K - 3) = r.head ∧
    r.word.drop (r.word.length - (K - 3)) = r.tail := by
  refine ⟨fun _ hp => r.assigned_infix_word hp, ?_, ?_, ?_⟩
  · have hl := r.word_length hv (by omega)
    have hk : r.base.length + 2 = K + 1 := by omega
    rw [hk] at hl
    omega
  · have hk : K - 3 = r.base.length - 2 := by omega
    simpa only [hk] using r.word_take_head
  · have hk : K - 3 = r.base.length - 2 := by omega
    simpa only [hk] using r.word_drop_tail hv (by omega)

end SuperpermutationUpperBound
