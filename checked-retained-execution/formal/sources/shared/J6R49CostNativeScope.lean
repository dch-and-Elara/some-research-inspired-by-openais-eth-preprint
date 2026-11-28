import J6R49CostPathScope
import J6R32StatefulArithmeticPath

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 18000000
set_option maxRecDepth 2700

/-! Path-dependent bit bills for the genuine printed Plan, with actual
Appendix-D schedule, exact child slots and Call-depth stopping. The
local running-meter premise must be proved for the installed executable. -/
namespace J6R49Cost
open scoped BigOperators Polynomial
open J1PPrinted J6ActiveRun J6ActiveSchedule J6R10Reachable J6R12Blueprint J6R11Blueprint
open J6R16ModeCost J6R24MeteredRecursion J6R32StatefulArithmetic

variable {f : ℤ[X]} {ell s C : ℕ}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

noncomputable def nativeScopedPlan
    (sel : Selector S (sourceDelta s)) (r : Call (PhysicalHost f ell)) :
    FinitePlan (Sigma (Path sel r)) :=
  scopePlan (Plan sel) (Path sel r) (fun z slot => .step z.2 slot)

theorem printed_path_scoped_budget
    (cfg : RootBounds s C f) (sel : Selector S (sourceDelta s)) (r : Call (PhysicalHost f ell))
    (hr : Stable s C r) (hzero : r.depth=0) (hroot : r.prec ≤ C*s)
    (total localFee : Sigma (Path sel r) → ℕ) (fixed address : ℕ)
    (runStep : ∀ z : Sigma (Path sel r),
      total z ≤ localFee z+((childList (nativeScopedPlan sel r) z).map total).sum)
    (ownBound : ∀ z : Sigma (Path sel r),
      localFee z ≤ fixed+address*Nat.card ((Plan sel).Slot z.1)) :
    total ⟨r,Path.root⟩ ≤ (pathLimit s C+1)*(fixed+address)*
      2^(branchBits (Nat.clog 2 s)*(pathLimit s C+1)+24*depthScale s C (Nat.clog 2 s) (siteConstant C)) := by
  let P := Plan sel
  let Y := Path sel r
  let Q : ∀ z : Sigma Y, ∀ slot : P.Slot z.1, Y (P.child z.1 slot) :=
    fun z slot => .step z.2 slot
  let H := pathLimit s C
  have hTerm : occurrences P r (H+1)=[] :=
    no_occurrences_past_bound cfg sel hr hzero (H+1) (Nat.lt_succ_self _)
  have hSlots (j : ℕ) (x : Call (PhysicalHost f ell)) (hx : x∈occurrences P r j) :
      Nat.card (P.Slot x) ≤ 2^(branchBits (Nat.clog 2 s)+
        depthExponent s C (Nat.clog 2 s) (siteConstant C) j) := by
    obtain ⟨hReach,hDepth⟩ := exact_depth_occurrence sel hzero j x hx
    simpa only [hDepth] using live_addresses_bound cfg sel hReach hr hzero hroot
  exact scoped_occurrence_upper P Y Q ⟨r,Path.root⟩ s C (Nat.clog 2 s) (siteConstant C)
    (branchBits (Nat.clog 2 s)) H fixed address total localFee hTerm hSlots
    (fun _ z _ => runStep z) (fun _ z _ => ownBound z)

#print axioms nativeScopedPlan
#print axioms printed_path_scoped_budget
end J6R49Cost

