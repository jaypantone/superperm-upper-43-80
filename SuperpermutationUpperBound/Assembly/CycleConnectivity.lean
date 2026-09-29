import SuperpermutationUpperBound.Assembly.CycleSplicing
import SuperpermutationUpperBound.Foundation.Relabeling
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic

/-! Finite connectivity stated on cycle labels. The no-separation condition
constructs an attachment order, then cycle splicing preserves every labelled
cycle's complete edge inventory, including repeated values. -/
namespace SuperpermutationUpperBound

variable {β : Type u} {V : Type v} {ι : Type w}

def EdgeIncident (src dst : β → V) (es : List β) (v : V) : Prop :=
  ∃ e ∈ es, src e = v ∨ dst e = v

def CycleNoSeparation [Fintype ι] (src dst : β → V) (cycles : ι → List β) : Prop :=
  ∀ S : Finset ι, S.Nonempty → S ≠ Finset.univ →
    ∃ i ∈ S, ∃ j ∉ S, ∃ v, EdgeIncident src dst (cycles i) v ∧
      EdgeIncident src dst (cycles j) v

private theorem cons_erase_toList_perm [DecidableEq ι] {S : Finset ι} {j : ι}
    (hj : j ∈ S) : (j :: (S.erase j).toList).Perm S.toList := by
  have h := Finset.toList_insert (s := S.erase j) (a := j) (by simp)
  rw [Finset.insert_erase hj] at h
  exact h.symm

private theorem attachment_extension [Fintype ι] [DecidableEq ι]
    {src dst : β → V} {cycles : ι → List β} (hc : CycleNoSeparation src dst cycles)
    (remaining : Finset ι) :
    ∀ first : List β, (∃ i, i ∉ remaining) →
      (∀ i, i ∉ remaining → ∀ v, EdgeIncident src dst (cycles i) v →
        EdgeIncident src dst first v) →
      ∃ rest : List ι, rest.Perm remaining.toList ∧
        CycleAttachmentOrder src dst first (rest.map cycles) := by
  refine Finset.strongInductionOn remaining ?_
  intro remaining ih first hselected hsupport
  by_cases hremaining : remaining.Nonempty
  · let selected : Finset ι := Finset.univ \ remaining
    have hsel : selected.Nonempty := by
      obtain ⟨i, hi⟩ := hselected
      exact ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩⟩
    have hproper : selected ≠ Finset.univ := by
      intro heq
      obtain ⟨j, hj⟩ := hremaining
      have hs : j ∈ selected := heq.symm ▸ Finset.mem_univ j
      exact (Finset.mem_sdiff.mp hs).2 hj
    obtain ⟨i, hi, j, hj, v, hiv, hjv⟩ := hc selected hsel hproper
    have hir : i ∉ remaining := (Finset.mem_sdiff.mp hi).2
    have hjr : j ∈ remaining := by
      by_contra hnot
      exact hj (Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hnot⟩)
    have hfirst : EdgeIncident src dst first v := hsupport i hir v hiv
    have hselected' : ∃ i, i ∉ remaining.erase j := by
      obtain ⟨i, hi⟩ := hselected
      exact ⟨i, fun hm => hi (Finset.mem_of_mem_erase hm)⟩
    have hsupport' : ∀ i, i ∉ remaining.erase j → ∀ v,
        EdgeIncident src dst (cycles i) v → EdgeIncident src dst (first ++ cycles j) v := by
      intro i hi w hw
      by_cases hij : i = j
      · subst i
        obtain ⟨e, he, hev⟩ := hw
        exact ⟨e, List.mem_append.mpr (Or.inr he), hev⟩
      · have hir : i ∉ remaining := fun hm => hi (Finset.mem_erase.mpr ⟨hij, hm⟩)
        obtain ⟨e, he, hev⟩ := hsupport i hir w hw
        exact ⟨e, List.mem_append.mpr (Or.inl he), hev⟩
    obtain ⟨rest, hp, ha⟩ := ih (remaining.erase j) (Finset.erase_ssubset hjr)
      (first ++ cycles j) hselected' hsupport'
    exact ⟨j :: rest, (hp.cons j).trans (cons_erase_toList_perm hjr),
      ⟨⟨v, hfirst, hjv⟩, ha⟩⟩
  · have he : remaining = ∅ := Finset.not_nonempty_iff_eq_empty.mp hremaining
    subst remaining
    exact ⟨[], by simp, True.intro⟩

/-- Starting at any label, finite no-separation produces a complete attachment
order of the other labels. Labels, rather than edge values, are enumerated. -/
theorem CycleNoSeparation.exists_attachment_order [Fintype ι] [DecidableEq ι]
    {src dst : β → V} {cycles : ι → List β} (hc : CycleNoSeparation src dst cycles)
    (seed : ι) :
    ∃ rest : List ι, (seed :: rest).Perm Finset.univ.toList ∧
      CycleAttachmentOrder src dst (cycles seed) (rest.map cycles) := by
  have hs : ∃ i, i ∉ Finset.univ.erase seed := ⟨seed, by simp⟩
  have hb : ∀ i, i ∉ Finset.univ.erase seed → ∀ v,
      EdgeIncident src dst (cycles i) v → EdgeIncident src dst (cycles seed) v := by
    intro i hi v hv
    have he : i = seed := by simpa using hi
    simpa only [he] using hv
  obtain ⟨rest, hp, ha⟩ := attachment_extension hc (Finset.univ.erase seed) (cycles seed) hs hb
  exact ⟨rest, (hp.cons seed).trans (cons_erase_toList_perm (Finset.mem_univ seed)), ha⟩

/-- A finite cycle family satisfying no-separation splices to one closed
path, retaining all cycle inventories with their multiplicities. -/
theorem EdgePath.splice_connected_family [Fintype ι] [DecidableEq ι]
    {src dst : β → V} {cycles : ι → List β} (seed : ι)
    (hcycles : ∀ i, ∃ v, EdgePath src dst v (cycles i) v)
    (hc : CycleNoSeparation src dst cycles) :
    ∃ v es, EdgePath src dst v es v ∧ es.Perm (Finset.univ.toList.flatMap cycles) := by
  obtain ⟨rest, horder, hattach⟩ := hc.exists_attachment_order seed
  obtain ⟨a, hfirst⟩ := hcycles seed
  have hrest : ∀ cycle ∈ rest.map cycles, ∃ v, EdgePath src dst v cycle v := by
    intro cycle hm
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hm
    exact hcycles i
  obtain ⟨v, es, hp, hi⟩ := hfirst.splice_family hrest hattach
  refine ⟨v, es, hp, hi.trans ?_⟩
  simpa only [List.flatMap, List.map_cons, List.flatten_cons] using horder.flatMap_right cycles

/-- The finite-occurrence specialization matches a list of separately labelled
cycles, even if different labels carry identical edge lists. -/
theorem EdgePath.splice_connected_fin_family {N : Nat} {src dst : β → V}
    {cycles : Fin N → List β} (hN : 0 < N)
    (hcycles : ∀ i, ∃ v, EdgePath src dst v (cycles i) v)
    (hc : CycleNoSeparation src dst cycles) :
    ∃ v es, EdgePath src dst v es v ∧ es.Perm ((List.finRange N).flatMap cycles) := by
  obtain ⟨v, es, hp, hi⟩ := EdgePath.splice_connected_family ⟨0, hN⟩ hcycles hc
  have he : Finset.univ.toList.Perm (List.finRange N) := by
    apply (List.perm_ext_iff_of_nodup Finset.univ.nodup_toList (nodup_finRange N)).mpr
    intro i
    simp [List.mem_finRange]
  exact ⟨v, es, hp, hi.trans (he.flatMap_right cycles)⟩

end SuperpermutationUpperBound
