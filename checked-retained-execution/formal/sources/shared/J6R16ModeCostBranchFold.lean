import J6R16ModeCostSite
import J6R16ModeCostLayers

/-! Actual recursive occurrences, retaining duplicate Call records
when they arise from distinct printed addresses. -/
namespace J6R16ModeCost
open scoped BigOperators Classical Polynomial
open J1PPrinted J6ActiveRun J6ActiveSchedule J6R10Reachable J6R12Blueprint J6R11Blueprint

variable {f : ℤ[X]} {ell s C : ℕ}
variable (cfg : RootBounds s C f)
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

variable {r : Call (PhysicalHost f ell)}
include cfg
theorem active_strictly_before_limit (hr : Stable s C r) {c : Call (PhysicalHost f ell)}
    (h : NativeReach (Plan sel) r c) (ha : (S).cutoff<c.edges) :
    c.depth<pathLimit s C := by
  have hs := (stable_reachable cfg sel h hr).sizeByDepth
  have hL : 0<Nat.clog 2 s := (by decide : 0<(1024:ℕ)).trans_le (root_lambda_large cfg)
  exact Nat.lt_succ_of_le (Nat.le_log_of_pow_le (by decide)
    (active_depth_power s (Nat.clog 2 s) C c.edges c.depth hL ha hs))

omit cfg in
theorem exact_depth_occurrence (hzero : r.depth=0) (j : ℕ) (c : Call (PhysicalHost f ell))
    (h : c∈occurrences (Plan sel) r j) : NativeReach (Plan sel) r c ∧ c.depth=j := by
  have H := occurrence_reach_depth (Plan sel) (fun x=>x.depth) (fun _ _=>rfl) r j c h
  simpa only [hzero,zero_add] using H

theorem no_occurrences_past_bound (hr : Stable s C r) (hzero : r.depth=0) (d : ℕ)
    (hj : pathLimit s C<d) : occurrences (Plan sel) r d=[] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro c hc
  obtain ⟨hx,hD⟩ := exact_depth_occurrence sel hzero d c hc
  have H := path_depth_bound cfg sel hx hr hzero
  omega

theorem total_native_occurrences (hr : Stable s C r) (hzero : r.depth=0) (hroot : r.prec≤C*s) :
    let lam := Nat.clog 2 s
    let H := pathLimit s C
    (∑ j∈Finset.range (H+1),(occurrences (Plan sel) r j).length)≤
      (H+1)*2^(branchBits lam*H+24*depthScale s C lam (siteConstant C)) := by
  apply total_occur_bound
  intro j c hc
  obtain ⟨hR,hD⟩ := exact_depth_occurrence sel hzero j c hc
  simpa only [hD] using live_addresses_bound cfg sel hR hr hzero hroot

#print axioms active_strictly_before_limit
#print axioms exact_depth_occurrence
#print axioms no_occurrences_past_bound
#print axioms total_native_occurrences
end J6R16ModeCost
