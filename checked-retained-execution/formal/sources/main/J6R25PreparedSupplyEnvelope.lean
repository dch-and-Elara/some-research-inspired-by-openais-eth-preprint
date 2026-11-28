import J6R25PreparedSupplyWhole
import J6R16ModeCostCompress

/-! Printed-schedule bound on the actual new mode bill, including
R17's paid sparse dispatch. This is not a bound on the rest of the
prepared recursion, registry installation, or layout preparation. -/
namespace J6R25PreparedSupply
open scoped Polynomial BigOperators Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R16ModeCost J6R17ModeTape
open J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint
open J1PPrinted J6R24MeteredRecursion

theorem batch_cap_mono {a A w W m M q k : ℕ} (ha : a≤A) (hw : w≤W) (hm : m≤M) :
    emitBatchCap a q w m k≤emitBatchCap A q W M k := by
  unfold emitBatchCap delayCap transitionCap scanCap dispatchStride recordStride
  gcongr

theorem batch_cap_scale (a q w m k X : ℕ) (hx : 1≤X) (hk : k≤X) :
    emitBatchCap a q w m k≤emitBatchCap a q w m 1*X := by
  let c := 16*q+14+4*(w+1)*(q+1)
  let d := delayCap q w
  let l := m*dispatchStride a q+10
  have h1 : k+1≤2*X := by omega
  have h2 : c≤c*X := by
    exact (by rw [Nat.mul_one] : c=c*1).le.trans (Nat.mul_le_mul_left c hx)
  have h3 : 4≤4*X := by omega
  change c+(k+1)*d+l*k+4≤(c+(1+1)*d+l*1+4)*X
  calc
    _≤c*X+(2*X)*d+l*X+4*X :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add h2 (Nat.mul_le_mul_right d h1))
        (Nat.mul_le_mul_left l hk)) h3
    _=_ := by ring

def batchUniform (s C : ℕ) : ℕ :=
  buildUniform s C+emitBatchCap (Nat.clog 2 s) (uniformWidth s C) (rosterSize s C) (rosterSize s C) 1

variable {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
variable (T : Input cfg sel r hf)
variable {c : Call (PhysicalHost f ell)}

set_option maxHeartbeats 3600000 in
theorem Input.draw_uniform (hc : NativeReach (Plan sel) r c)
    (d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c)
    (t : Center (printedParams (f:=f) (ell:=ell) s) c) :
    (T.draw hc d t).steps≤batchUniform s C*
      2^(depthExponent s C (Nat.clog 2 s) (siteConstant C) c.depth) := by
  let Q := uniformWidth s C
  let R := rosterSize s C
  let Z := rawSite sel d t (T.layouts c hc d)
  let I := paidTapeSupply cfg sel T.rootStable T.dZero T.rWidth T.layouts c hc d t
  let e := paid_tape_supply_exact cfg sel T.rootStable T.dZero T.rWidth T.layouts hc d t
  let xs := strictTuples (I.modes.map modeWeight) (registerPrecision S c t)
  let X := (2:ℕ)^(depthExponent s C (Nat.clog 2 s) (siteConstant C) c.depth)
  obtain ⟨_,_,_,_,_,_,hC⟩ := native_produced_is_complete cfg sel T.rootStable T.dZero T.rWidth T.layouts hc d t
  have n : I.modes.length≤R := roster_size_bound cfg sel hc T.rootStable T.dZero T.rWidth d t
    I.modes I.nodup I.allModes
  have hm : Z.result.modes.length≤R := by rw [e.1,List.length_map]; exact n
  have hw : Z.result.weights.length≤R := by
    have eW := (actual_raw_valid cfg sel T.rootStable T.dZero T.rWidth T.layouts hc d t).sameLength
    change Z.result.weights.length=Z.result.modes.length at eW
    rwa [eW]
  have ha : (S).levelBits c.depth≤Nat.clog 2 s := bits_le_lam _ _
  have hK : xs.length≤X := tuple_depth_bound cfg sel hc T.rootStable T.dZero T.rWidth d t
    I.modes I.nodup I.allModes
  have hX : 1≤X := Nat.succ_le_of_lt (by unfold X; positivity)
  have hE := (batch_cap_mono (q:=Q) (k:=xs.length) ha hw hm).trans
    (batch_cap_scale (Nat.clog 2 s) Q R R xs.length X hX hK)
  have hBuild : buildUniform s C≤buildUniform s C*X := by
    exact (by rw [Nat.mul_one] : buildUniform s C=buildUniform s C*1).le.trans
      (Nat.mul_le_mul_left _ hX)
  exact hC.trans ((Nat.add_le_add hBuild hE).trans_eq (by
    change _=batchUniform s C*X
    rw [batchUniform,Nat.add_mul]))

set_option maxHeartbeats 3100000 in
theorem Input.mode_at_uniform (hc : NativeReach (Plan sel) r c) :
    T.modeAt c≤batchUniform s C*
      2^(branchBits (Nat.clog 2 s)+depthExponent s C (Nat.clog 2 s) (siteConstant C) c.depth) := by
  unfold Input.modeAt
  rw [dif_pos hc]
  split
  · rename_i ha
    let G := T.geometry c hc ha
    let lam := Nat.clog 2 s
    let E := depthExponent s C lam (siteConstant C) c.depth
    have hcN : G.centres.length≤2^(branchBits lam) := by
      have hEq : G.centres.toFinset=Finset.univ := by ext t; simp [G.complete t]
      rw [←List.toFinset_card_of_nodup G.nodup,hEq,Finset.card_univ,←Nat.card_eq_fintype_card]
      have A : (S).levelBits c.depth+1≤branchBits lam := by
        have this := bits_le_lam lam c.depth
        unfold branchBits
        change stepA lam c.depth+1≤_
        omega
      exact (centers_le S c).trans (Nat.pow_le_pow_right (by decide) A)
    have hS := list_sum_cap G.centres _ (batchUniform s C*2^E)
      (fun t _=>T.draw_uniform hc (ready_reachable cfg sel hc T.rootStable ha) t)
    refine hS.trans ((Nat.mul_le_mul_right _ hcN).trans_eq ?_)
    rw [pow_add]
    ring
  · exact Nat.zero_le _

set_option maxHeartbeats 3200000 in
theorem Input.total_producer_bound :
    (∑ j∈Finset.range (pathLimit s C+1),levelBill (Plan sel) r T.modeAt j)≤
      pathLimit s C*batchUniform s C*
        2^(prefixConstant C*J9PrintedSchedule.leafThreshold s (Nat.clog 2 s)) := by
  let H := pathLimit s C
  let lam := Nat.clog 2 s
  have last : levelBill (Plan sel) r T.modeAt H=0 := by
    have zero (c : Call (PhysicalHost f ell)) (h : c∈occurrences (Plan sel) r H) : T.modeAt c=0 := by
      obtain ⟨hr,hd⟩ := exact_depth_occurrence sel T.dZero H c h
      have hp : ¬ (S).cutoff<c.edges := by
        intro ha
        have ht := active_strictly_before_limit cfg sel T.rootStable hr ha
        change c.depth<H at ht
        omega
      simp only [Input.modeAt,dif_pos hr,dif_neg hp]
    have h := list_sum_cap (occurrences (Plan sel) r H) T.modeAt 0 (fun c hc=>(zero c hc).le)
    exact Nat.eq_zero_of_le_zero (by simpa only [Nat.mul_zero] using h)
  rw [Finset.sum_range_succ,last,Nat.add_zero]
  have H0 := total_fee_bound (Plan sel) r s C lam (siteConstant C) (branchBits lam) H (batchUniform s C) T.modeAt
    (fun j c hc=>by
      obtain ⟨h,hd⟩ := exact_depth_occurrence sel T.dZero j c hc
      simpa only [hd] using live_addresses_bound cfg sel h T.rootStable T.dZero T.rWidth)
    (fun j c hc=>by
      obtain ⟨h,hd⟩ := exact_depth_occurrence sel T.dZero j c hc
      simpa only [hd] using T.mode_at_uniform h)
  refine H0.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) ?_))
  exact compress_exponent s C cfg.constPos cfg.size (root_lambda_large cfg)

#print axioms batch_cap_mono
#print axioms batch_cap_scale
#print axioms Input.draw_uniform
#print axioms Input.mode_at_uniform
#print axioms Input.total_producer_bound
end J6R25PreparedSupply

