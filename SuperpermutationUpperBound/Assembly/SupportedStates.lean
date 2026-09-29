import SuperpermutationUpperBound.Assembly.OverlapStates
import SuperpermutationUpperBound.Partition.SprintFamily

namespace SuperpermutationUpperBound
variable {α : Type}

/-- Literal injective states supported on an arbitrary finite alphabet. -/
def supportedOverlapState (A : Finset α) (ell : Nat) :=
  {v : List α // v.length = ell ∧ v.Nodup ∧ ∀ a ∈ v, a ∈ A}

def embeddingSupportedState (A : Finset α) (ell : Nat) (f : Fin ell ↪ A) :
    supportedOverlapState A ell := by
  refine ⟨List.ofFn (fun i => (f i).val), List.length_ofFn, ?_, ?_⟩
  · apply List.nodup_ofFn_ofInjective
    intro i j hij
    exact f.injective (Subtype.ext hij)
  · intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact (f i).property

theorem embeddingSupportedState_bijective (A : Finset α) (ell : Nat) :
    Function.Bijective (embeddingSupportedState A ell) := by
  constructor
  · intro f g he
    have hval := List.ofFn_injective (congrArg Subtype.val he)
    apply DFunLike.ext
    intro i
    exact Subtype.ext (congrFun hval i)
  · rintro ⟨v, hv, hn, hs⟩
    subst ell
    let f : Fin v.length ↪ A :=
      ⟨fun i => ⟨v.get i, hs _ (List.get_mem v i)⟩,
        fun i j hij => hn.get_inj_iff.mp (congrArg Subtype.val hij)⟩
    refine ⟨f, Subtype.ext ?_⟩
    exact List.ofFn_get v

noncomputable def supportedStateEquivEmbedding (A : Finset α) (ell : Nat) :
    supportedOverlapState A ell ≃ (Fin ell ↪ A) :=
  (Equiv.ofBijective (embeddingSupportedState A ell) (embeddingSupportedState_bijective A ell)).symm

noncomputable instance (A : Finset α) (ell : Nat) : Fintype (supportedOverlapState A ell) :=
  Fintype.ofEquiv (Fin ell ↪ A) (supportedStateEquivEmbedding A ell).symm

instance [DecidableEq α] (A : Finset α) (ell : Nat) : DecidableEq (supportedOverlapState A ell) :=
  inferInstanceAs (DecidableEq {v : List α // v.length = ell ∧ v.Nodup ∧ ∀ a ∈ v, a ∈ A})

theorem supportedOverlapState_card (A : Finset α) (ell : Nat) :
    Fintype.card (supportedOverlapState A ell) = A.card.descFactorial ell := by
  rw [Fintype.card_congr (supportedStateEquivEmbedding A ell)]
  simp only [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_coe]

theorem supportedOverlapState_card_factorial (A : Finset α) (ell : Nat) (hl : ell ≤ A.card) :
    (A.card - ell).factorial * Fintype.card (supportedOverlapState A ell) = A.card.factorial := by
  rw [supportedOverlapState_card]
  exact Nat.factorial_mul_descFactorial hl

namespace Partition.SprintFamily

def stateAlphabet (k : Nat) : Finset Nat := (10 :: alphabet k).toFinset

theorem stateAlphabet_card (k : Nat) : (stateAlphabet k).card = k + 10 := by
  have hn : (10 :: alphabet k).Nodup := List.nodup_cons.mpr ⟨alphabet_final k, alphabet_nodup k⟩
  rw [stateAlphabet, List.toFinset_card_of_nodup hn]
  simp [Nat.add_assoc]

theorem stateAlphabet_mem (k : Nat) (a : Nat) :
    a ∈ stateAlphabet k ↔ a < k + 11 ∧ a ≠ 9 := by
  have hp := full_alphabet_perm k
  simp only [stateAlphabet, List.mem_toFinset, List.mem_cons]
  constructor
  · intro ha
    have hm : a ∈ 10 :: (alphabet k ++ [9]) := by
      rcases ha with h | h
      · exact List.mem_cons.mpr (Or.inl h)
      · exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl h)))
    have hr : a ∈ List.range (k + 11) := hp.mem_iff.mp hm
    refine ⟨List.mem_range.mp hr, ?_⟩
    intro heq
    subst a
    simp only [show (9 : Nat) ≠ 10 by decide, false_or] at ha
    exact alphabet_satellite k ha
  · intro ⟨ha, hne⟩
    have hmem := hp.mem_iff.mpr (List.mem_range.mpr ha)
    simpa [hne] using hmem

end Partition.SprintFamily
end SuperpermutationUpperBound
