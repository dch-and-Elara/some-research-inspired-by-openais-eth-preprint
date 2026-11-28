import P9GuardedPacking

/-! Reserve two whole columns at each end of the same P9 seat chart.
This is slightly stronger physically than reserving the four OR-side
ports alone and costs at most a constant in the guard census. -/
namespace J2R47P9ZeroProbe
open scoped Classical BigOperators
open P11FullPacking P9BalancedChart GuardedPacking
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000
set_option maxRecDepth 2000
set_option linter.unusedSectionVars false
noncomputable section

variable {U C : Type} [Fintype U] [DecidableEq U] [Fintype C] [DecidableEq C]

theorem total_two_port_load (label : U→Bool→C) (s : Finset U) :
    (∑ c : C,cellLoad (GuardedPacking.multiplicity label) s c)=2*s.card := by
  classical
  unfold cellLoad
  rw [Finset.sum_comm]
  have h (u : U) : (∑ c : C,GuardedPacking.multiplicity label u c)=2 := by
    unfold GuardedPacking.multiplicity
    rw [←Fintype.card_sigma]
    exact (Fintype.card_congr (Equiv.sigmaFiberEquiv (label u))).trans Fintype.card_bool
  simp [h, Nat.mul_comm]

theorem disjoint_union_load (label : U→Bool→C) (s t : Finset U) (ht : Disjoint s t) (c : C) :
    cellLoad (GuardedPacking.multiplicity label) (s∪t) c =
      cellLoad (GuardedPacking.multiplicity label) s c+cellLoad (GuardedPacking.multiplicity label) t c := by
  exact Finset.sum_union ht

/-- Deterministic trim, against the residual capacities, on the actual
cell load functions. Taking the union after trimming forces the
reservations and maintains the original disjointness of the two ends. -/
theorem protect_reservations (label : U→Bool→C) (b : ℕ) (keep res : Bool→Finset U)
    (hk : Disjoint (keep false) (keep true)) (hr : Disjoint (res false) (res true))
    (hK : ∀ s c,cellLoad (GuardedPacking.multiplicity label) (keep s) c≤b)
    (hR : ∀ s c,cellLoad (GuardedPacking.multiplicity label) (res s) c≤b) :
    ∃ out : Bool→Finset U,
      Disjoint (out false) (out true) ∧
      ∀ s, res s⊆out s ∧ (∀ c,cellLoad (GuardedPacking.multiplicity label) (out s) c≤b) ∧
        (keep s).card≤(out s).card+(res false∪res true).card+(res s).card := by
  classical
  let ban := res false∪res true
  have hban (s : Bool) : res s⊆ban := by
    cases s
    · exact Finset.subset_union_left
    · exact Finset.subset_union_right
  have trim (s : Bool) : ∃ t : Finset U, t⊆keep s\ban ∧
      (∀ c,cellLoad (GuardedPacking.multiplicity label) t c≤b-cellLoad (GuardedPacking.multiplicity label) (res s) c) ∧
      (keep s).card≤t.card+ban.card+2*(res s).card := by
    let w := GuardedPacking.multiplicity label
    let room := fun c => b-cellLoad w (res s) c
    let clean := keep s\ban
    obtain ⟨t,sub,cap,lost⟩ := keep_within_capacity w room clean
    have ov : overflow w room clean≤2*(res s).card := by
      rw [←total_two_port_load label (res s)]
      unfold overflow
      apply Finset.sum_le_sum
      intro c _
      have hle : cellLoad w clean c≤b :=
        (cellLoad_mono Finset.sdiff_subset w c).trans (hK s c)
      have hfit := hR s c
      change cellLoad w clean c - (b-cellLoad w (res s) c)≤cellLoad w (res s) c
      omega
    have cut : (keep s).card≤clean.card+ban.card := by
      have h := Finset.card_le_card (Finset.inter_subset_right : keep s ∩ ban⊆ban)
      have hs := Finset.card_sdiff_add_card_inter (keep s) ban
      change (keep s\ban).card+(keep s∩ban).card=(keep s).card at hs
      change clean.card+(keep s∩ban).card=(keep s).card at hs
      omega
    exact ⟨t,sub,cap,by omega⟩
  choose t hsub htcap htcard using trim
  have apart (s s' : Bool) : Disjoint (t s) (res s') := by
    rw [Finset.disjoint_left]
    intro u hu ha
    exact (Finset.mem_sdiff.mp (hsub s hu)).2 (hban s' ha)
  refine ⟨fun s=>t s∪res s,?_ ,?_⟩
  · apply Finset.disjoint_left.mpr
    intro u hu hv
    rcases Finset.mem_union.mp hu with fu|fu <;> rcases Finset.mem_union.mp hv with tu|tu
    · exact Finset.disjoint_left.mp hk (Finset.mem_sdiff.mp (hsub false fu)).1
        (Finset.mem_sdiff.mp (hsub true tu)).1
    · exact Finset.disjoint_left.mp (apart false true) fu tu
    · exact Finset.disjoint_left.mp (apart true false) tu fu
    · exact Finset.disjoint_left.mp hr fu tu
  · intro s
    refine ⟨Finset.subset_union_right,?_ ,?_⟩
    · intro c
      rw [disjoint_union_load label _ _ (apart s s)]
      have h := htcap s c
      have h' := hR s c
      omega
    · rw [Finset.card_union_of_disjoint (apart s s)]
      change (keep s).card≤(t s).card+(res s).card+ban.card+(res s).card
      have h := htcard s
      omega

#print axioms total_two_port_load
#print axioms disjoint_union_load
#print axioms protect_reservations
end
end J2R47P9ZeroProbe

