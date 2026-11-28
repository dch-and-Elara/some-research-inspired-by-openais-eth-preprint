import J6R17ModeTapeReach
import J6R16ModeCostCompress

/-! Whole-tree composition with R16's reachability and fee fold.
The side certificate chooses a typed interpretation of the computed
tape only; its raw fields are forced by the audited producer. -/
namespace J6R17ModeTape
open scoped Classical Polynomial BigOperators
open AOracleMachineTime J6ActiveRun J6R12Blueprint J6R10Reachable J6R11Blueprint
open J6R16ModeCost J6R15ModeCost J6ActiveSchedule J1PPrinted

variable {f : ℤ[X]} {ell s C : ℕ}
variable (cfg : RootBounds s C f)
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

abbrev LayoutSupply (r : Call (PhysicalHost f ell)) :=
  ∀ (c : Call (PhysicalHost f ell)), NativeReach (Plan sel) r c →
    ∀ d : Ready S (sourceDelta s) c,CallLayout (C:=C) sel d

variable {r : Call (PhysicalHost f ell)}
include cfg

noncomputable def paidTapeSupply (hr : Stable s C r) (hzero : r.depth=0) (hroot : r.prec≤C*s)
    (Ls : LayoutSupply (C:=C) sel r) : TapeSupply sel r (uniformWidth s C) :=
  fun c h d t=>Classical.choose (raw_site_bound cfg sel h hr hzero hroot d t (Ls c h d))

theorem paid_tape_supply_exact (hr : Stable s C r) (hzero : r.depth=0) (hroot : r.prec≤C*s)
    (Ls : LayoutSupply (C:=C) sel r) {c : Call (PhysicalHost f ell)}
    (h : NativeReach (Plan sel) r c) (d : Ready S (sourceDelta s) c) (t : Center S c) :
    let I := paidTapeSupply cfg sel hr hzero hroot Ls c h d t
    let z := rawSite sel d t (Ls c h d)
    z.result.modes=I.modes.map (encodeMode (centerIndex d t)) ∧
      z.result.weights=I.words ∧ z.result.precision=I.precision ∧ z.steps≤buildUniform s C := by
  obtain ⟨hm,_,hw,hp,hc⟩ := Classical.choose_spec
    (raw_site_bound cfg sel h hr hzero hroot d t (Ls c h d))
  exact ⟨hm,hw,hp,hc⟩

noncomputable def builtCallCost (hr : Stable s C r) (hzero : r.depth=0) (hroot : r.prec≤C*s)
    (Ls : LayoutSupply (C:=C) sel r) (c : Call (PhysicalHost f ell)) : ℕ :=
  measuredCall cfg sel hr (paidTapeSupply cfg sel hr hzero hroot Ls) c+
    if h : NativeReach (Plan sel) r c then
      if ha : (S).cutoff<c.edges then
        let d := ready_reachable cfg sel h hr ha
        J9PrintedSchedule.probeCount c.edges (2^(S).levelBits c.depth)*
          (∑ t : Center S c,(rawSite sel d t (Ls c h d)).steps)
      else 0
    else 0

def comboFee (s C : ℕ) : ℕ :=
  uniformFee s C+buildUniform s C

theorem built_call_cap (hr : Stable s C r) (hzero : r.depth=0) (hroot : r.prec≤C*s)
    (Ls : LayoutSupply (C:=C) sel r) (c : Call (PhysicalHost f ell)) :
    builtCallCost cfg sel hr hzero hroot Ls c≤comboFee s C*
      2^(branchBits (Nat.clog 2 s)+depthExponent s C (Nat.clog 2 s) (siteConstant C) c.depth) := by
  let lam := Nat.clog 2 s
  let E := depthExponent s C lam (siteConstant C) c.depth
  let T := paidTapeSupply cfg sel hr hzero hroot Ls
  have hOld := measured_call_cap cfg sel hr hzero hroot T c
  unfold builtCallCost comboFee
  rw [Nat.add_mul]
  apply Nat.add_le_add hOld
  split
  · rename_i h
    split
    · rename_i ha
      let d := ready_reachable cfg sel h hr ha
      have hs : (∑ t : Center S c,(rawSite sel d t (Ls c h d)).steps)≤
          Nat.card (Center S c)*buildUniform s C := by
        calc
          _≤∑ _ : Center S c,buildUniform s C := Finset.sum_le_sum (fun t _=>
            (paid_tape_supply_exact cfg sel hr hzero hroot Ls h d t).2.2.2)
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
        _≤2^(4*lam)*(Nat.card (Center S c)*buildUniform s C) := Nat.mul_le_mul hp hs
        _≤2^(4*lam)*(2^(lam+1)*buildUniform s C) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hC)
        _=buildUniform s C*((2:ℕ)^(4*lam)*2^(lam+1)) := by ring
        _≤_ := by
          rw [← pow_add]
          apply Nat.mul_le_mul_left
          apply Nat.pow_le_pow_right (by decide)
          change 4*lam+(lam+1)≤(5*lam+7)+E
          omega
    · exact Nat.zero_le _
  · exact Nat.zero_le _

theorem total_built_mode_cost (hr : Stable s C r) (hzero : r.depth=0) (hroot : r.prec≤C*s)
    (Ls : LayoutSupply (C:=C) sel r) :
    let lam := Nat.clog 2 s
    let H := pathLimit s C
    (∑ j∈Finset.range H,((occurrences (Plan sel) r j).map (builtCallCost cfg sel hr hzero hroot Ls)).sum)≤
      H*comboFee s C*2^(branchBits lam*H+24*depthScale s C lam (siteConstant C)) := by
  apply total_fee_bound
  · intro j c hc
    obtain ⟨hR,hD⟩ := exact_depth_occurrence sel hzero j c hc
    simpa only [hD] using live_addresses_bound cfg sel hR hr hzero hroot
  · intro j c hc
    obtain ⟨_,hD⟩ := exact_depth_occurrence sel hzero j c hc
    simpa only [hD] using built_call_cap cfg sel hr hzero hroot Ls c

theorem total_built_printed_rate (hr : Stable s C r) (hzero : r.depth=0) (hroot : r.prec≤C*s)
    (Ls : LayoutSupply (C:=C) sel r) :
    let lam := Nat.clog 2 s
    let H := pathLimit s C
    (∑ j∈Finset.range H,((occurrences (Plan sel) r j).map (builtCallCost cfg sel hr hzero hroot Ls)).sum)≤
      H*comboFee s C*2^(prefixConstant C * J9PrintedSchedule.leafThreshold s lam) := by
  apply (total_built_mode_cost cfg sel hr hzero hroot Ls).trans
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_right (by decide)
  exact compress_exponent s C cfg.constPos cfg.size (root_lambda_large cfg)

#print axioms total_built_printed_rate
#print axioms paid_tape_supply_exact
#print axioms built_call_cap
#print axioms total_built_mode_cost
end J6R17ModeTape


