import SuperpermutationUpperBound.Assembly.ImbalanceCounts

namespace SuperpermutationUpperBound

variable {E V : Type} [Fintype E] [Fintype V] [DecidableEq V]

/-- One incoming balancing-edge slot for each unit of positive imbalance. -/
abbrev BalancingDummy (src dst : E → V) :=
  Σ v : V, Fin (degreeImbalance src dst v).toNat

/-- One outgoing balancing-edge slot for each unit of negative imbalance. -/
abbrev NegativeSlot (src dst : E → V) :=
  Σ v : V, Fin (-degreeImbalance src dst v).toNat

theorem balancingDummy_card (src dst : E → V) :
    Fintype.card (BalancingDummy src dst) = positiveImbalance src dst := by
  simp only [BalancingDummy, Fintype.card_sigma, Fintype.card_fin, positiveImbalance]

theorem balancing_slots_card_eq (src dst : E → V) :
    Fintype.card (BalancingDummy src dst) = Fintype.card (NegativeSlot src dst) := by
  simp only [BalancingDummy, NegativeSlot, Fintype.card_sigma, Fintype.card_fin]
  exact positiveImbalance_eq_negative src dst

noncomputable def balancingEquiv (src dst : E → V) :
    BalancingDummy src dst ≃ NegativeSlot src dst :=
  Fintype.equivOfCardEq (balancing_slots_card_eq src dst)

noncomputable def dummySrc (src dst : E → V) (d : BalancingDummy src dst) : V :=
  (balancingEquiv src dst d).1

def dummyDst (src dst : E → V) (d : BalancingDummy src dst) : V := d.1

noncomputable def balancedSource (src dst : E → V) : E ⊕ BalancingDummy src dst → V :=
  Sum.elim src (dummySrc src dst)

def balancedTarget (src dst : E → V) : E ⊕ BalancingDummy src dst → V :=
  Sum.elim dst (dummyDst src dst)

omit [Fintype E] in
theorem sigma_fst_fiber_card (n : V → Nat) (v : V) :
    Fintype.card {d : Σ v, Fin (n v) // d.1 = v} = n v := by
  simpa only [Fintype.card_fin] using
    Fintype.card_congr (Equiv.sigmaSubtype (β := fun v => Fin (n v)) v)

theorem dummyDst_fiber_card (src dst : E → V) (v : V) :
    Fintype.card {d : BalancingDummy src dst // dummyDst src dst d = v} =
      (degreeImbalance src dst v).toNat :=
  sigma_fst_fiber_card _ v

theorem dummySrc_fiber_card (src dst : E → V) (v : V) :
    Fintype.card {d : BalancingDummy src dst // dummySrc src dst d = v} =
      (-degreeImbalance src dst v).toNat := by
  calc
    _ = Fintype.card {d : NegativeSlot src dst // d.1 = v} :=
      Fintype.card_congr ((balancingEquiv src dst).subtypeEquiv
        (p := fun d => dummySrc src dst d = v) (q := fun d => d.1 = v)
          (fun _ => Iff.rfl))
    _ = _ := sigma_fst_fiber_card _ v

omit [Fintype V] in
theorem sum_endpoint_fiber_card {D : Type} [Fintype D] (f : E → V) (g : D → V) (v : V) :
    Fintype.card {e : E ⊕ D // Sum.elim f g e = v} =
      Fintype.card {e : E // f e = v} + Fintype.card {d : D // g d = v} := by
  calc
    _ = Fintype.card ({e : E // f e = v} ⊕ {d : D // g d = v}) :=
      Fintype.card_congr (Equiv.subtypeSum (p := fun e : E ⊕ D => Sum.elim f g e = v))
    _ = _ := Fintype.card_sum

/-- Adding the labelled dummy edges balances every vertex. Original labels
remain the left summand, so loops and parallel edges remain distinct. -/
theorem balancing_extension_balanced (src dst : E → V) :
    BalancedDegrees (balancedSource src dst) (balancedTarget src dst) := by
  intro v
  change Fintype.card {e // Sum.elim dst (dummyDst src dst) e = v} =
    Fintype.card {e // Sum.elim src (dummySrc src dst) e = v}
  rw [sum_endpoint_fiber_card, sum_endpoint_fiber_card,
    dummyDst_fiber_card, dummySrc_fiber_card]
  have h := Int.toNat_sub_toNat_neg (degreeImbalance src dst v)
  unfold degreeImbalance at h ⊢
  omega

omit [Fintype V] in
theorem dummyDst_positive (src dst : E → V) (d : BalancingDummy src dst) :
    0 < degreeImbalance src dst (dummyDst src dst d) := by
  exact Int.pos_iff_toNat_pos.mpr (Nat.zero_lt_of_lt d.2.isLt)

theorem dummySrc_negative (src dst : E → V) (d : BalancingDummy src dst) :
    degreeImbalance src dst (dummySrc src dst d) < 0 := by
  have h := Int.pos_iff_toNat_pos.mpr (Nat.zero_lt_of_lt (balancingEquiv src dst d).2.isLt)
  change 0 < -degreeImbalance src dst (dummySrc src dst d) at h
  omega

theorem dummy_endpoints_nonzero (src dst : E → V) (d : BalancingDummy src dst) :
    degreeImbalance src dst (dummySrc src dst d) ≠ 0 ∧
      degreeImbalance src dst (dummyDst src dst d) ≠ 0 :=
  ⟨ne_of_lt (dummySrc_negative src dst d), ne_of_gt (dummyDst_positive src dst d)⟩

/-- Every nonzero-imbalance vertex is incident to a balancing edge. This is
the converse needed when untouched cycles are charged to balanced vertices. -/
theorem nonzero_iff_dummy_incident (src dst : E → V) (v : V) :
    degreeImbalance src dst v ≠ 0 ↔
      ∃ d : BalancingDummy src dst, dummySrc src dst d = v ∨ dummyDst src dst d = v := by
  constructor
  · intro hv
    rcases lt_or_gt_of_ne hv with hneg | hpos
    · let a : NegativeSlot src dst :=
        ⟨v, ⟨0, Int.pos_iff_toNat_pos.mp (by omega)⟩⟩
      refine ⟨(balancingEquiv src dst).symm a, Or.inl ?_⟩
      simp only [dummySrc, Equiv.apply_symm_apply, a]
    · exact ⟨⟨v, ⟨0, Int.pos_iff_toNat_pos.mp hpos⟩⟩, Or.inr rfl⟩
  · rintro ⟨d, hs | ht⟩
    · rw [← hs]
      exact (dummy_endpoints_nonzero src dst d).1
    · rw [← ht]
      exact (dummy_endpoints_nonzero src dst d).2

theorem balancingDummy_card_le_nonzeroVertices (src dst : E → V)
    (hb : ∀ v, |degreeImbalance src dst v| ≤ 2) :
    Fintype.card (BalancingDummy src dst) ≤ (nonzeroVertices src dst).card := by
  rw [balancingDummy_card]
  exact positiveImbalance_le_nonzeroVertices src dst hb

end SuperpermutationUpperBound
