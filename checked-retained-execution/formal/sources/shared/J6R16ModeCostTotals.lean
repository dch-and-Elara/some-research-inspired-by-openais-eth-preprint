import J6R16ModeCostMeter
import J6R16ModeCostBranchFold

/-! Whole-tree sum of the R15 mode stream's measured work only.
The ledger counts address occurrences, re-streaming the exponent list
at every printed probe. The input tape, child descriptions, entry
evaluation, arithmetic/recovery, and leaf work are not charged here. -/
namespace J6R16ModeCost
open scoped BigOperators Classical Polynomial
open J1PPrinted J6ActiveRun J6ActiveSchedule J6R10Reachable J6R12Blueprint J6R11Blueprint

variable {f : ℤ[X]} {ell s C : ℕ}
variable (cfg : RootBounds s C f)
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

abbrev TapeSupply (r : Call (PhysicalHost f ell)) (q : ℕ) :=
  ∀ (c : Call (PhysicalHost f ell)), NativeReach (Plan sel) r c →
    ∀ (d : Ready S (sourceDelta s) c) (t : Center S c), SiteTape sel d t q

variable {r : Call (PhysicalHost f ell)}
include cfg

theorem tape_supply_exists (hr : Stable s C r) (hzero : r.depth=0) (hroot : r.prec≤C*s) :
    Nonempty (TapeSupply sel r (uniformWidth s C)) := by
  exact ⟨fun _ hc d t=>Classical.choice (achievable_tape_width cfg sel hc hr hzero hroot d t)⟩

noncomputable def measuredCall (hr : Stable s C r)
    (T : TapeSupply sel r (uniformWidth s C)) (c : Call (PhysicalHost f ell)) : ℕ :=
  if h : NativeReach (Plan sel) r c then
    if ha : (S).cutoff<c.edges then
      let d := ready_reachable cfg sel h hr ha
      J9PrintedSchedule.probeCount c.edges (2^(S).levelBits c.depth)*
        (∑ t : Center S c,measuredSite (T c h d t))
    else 0
  else 0

theorem measured_call_cap (hr : Stable s C r) (hzero : r.depth=0) (hroot : r.prec≤C*s)
    (T : TapeSupply sel r (uniformWidth s C)) (c : Call (PhysicalHost f ell)) :
    measuredCall cfg sel hr T c ≤ uniformFee s C*
      2^(branchBits (Nat.clog 2 s)+depthExponent s C (Nat.clog 2 s) (siteConstant C) c.depth) := by
  let lam := Nat.clog 2 s
  let E := depthExponent s C lam (siteConstant C) c.depth
  unfold measuredCall
  split
  · rename_i h
    split
    · rename_i ha
      let d := ready_reachable cfg sel h hr ha
      have hs : (∑ t : Center S c,measuredSite (T c h d t))≤
          Nat.card (Center S c)*(uniformFee s C*2^E) := by
        calc
          _≤∑ _ : Center S c,uniformFee s C*2^E :=
            Finset.sum_le_sum (fun t _=>measured_site_bound cfg sel h hr hzero hroot d t (T c h d t))
          _=_ := by
            rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
            rfl
      have hC : Nat.card (Center S c)≤2^(lam+1) :=
        (centers_le S c).trans (Nat.pow_le_pow_right (by decide)
          (Nat.succ_le_succ (bits_le_lam lam c.depth)))
      have hp := d.fit
      change J9PrintedSchedule.probeCount c.edges (2^(S).levelBits c.depth)≤2^f.natDegree at hp
      rw [cfg.coefficient] at hp
      calc
        _≤2^(4*lam)*(Nat.card (Center S c)*(uniformFee s C*2^E)) := Nat.mul_le_mul hp hs
        _≤2^(4*lam)*(2^(lam+1)*(uniformFee s C*2^E)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hC)
        _=uniformFee s C*((2:ℕ)^(4*lam)*2^(lam+1)*2^E) := by ring
        _≤_ := by
          rw [← pow_add,← pow_add]
          apply Nat.mul_le_mul_left
          apply Nat.pow_le_pow_right (by decide)
          change (4*lam+(lam+1))+E≤(5*lam+7)+E
          omega
    · exact Nat.zero_le _
  · exact Nat.zero_le _

theorem no_measured_fee_past_active (hr : Stable s C r)
    (T : TapeSupply sel r (uniformWidth s C)) (c : Call (PhysicalHost f ell))
    (h : pathLimit s C≤c.depth) : measuredCall cfg sel hr T c=0 := by
  unfold measuredCall
  split
  · rename_i hc
    have hn : ¬((S).cutoff<c.edges) :=
      fun ha=> (Nat.not_lt_of_ge h) (active_strictly_before_limit cfg sel hr hc ha)
    rw [dif_neg hn]
  · rfl

theorem total_measured_mode_cost (hr : Stable s C r) (hzero : r.depth=0) (hroot : r.prec≤C*s)
    (T : TapeSupply sel r (uniformWidth s C)) :
    let lam := Nat.clog 2 s
    let H := pathLimit s C
    (∑ j∈Finset.range H,((occurrences (Plan sel) r j).map (measuredCall cfg sel hr T)).sum)≤
      H*uniformFee s C*2^(branchBits lam*H+24*depthScale s C lam (siteConstant C)) := by
  apply total_fee_bound
  · intro j c hc
    obtain ⟨hR,hD⟩ := exact_depth_occurrence sel hzero j c hc
    simpa only [hD] using live_addresses_bound cfg sel hR hr hzero hroot
  · intro j c hc
    obtain ⟨_,hD⟩ := exact_depth_occurrence sel hzero j c hc
    simpa only [hD] using measured_call_cap cfg sel hr hzero hroot T c

#print axioms tape_supply_exists
#print axioms measured_call_cap
#print axioms no_measured_fee_past_active
#print axioms total_measured_mode_cost
end J6R16ModeCost



