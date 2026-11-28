
import J6R52PeakBudget
import J6R52PeakDemand

/-! At a true nonroot demand, the actual authored addon and indexed
sidecar tape are measured by the same paid acquisition phase, at
its own local snapshot. This is not a claim of a memoized across-slot
cache or that all arithmetic/allocator scratch is resident. -/
namespace J6R52Peak
open scoped Polynomial
open AOracleMachineTime J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R16ModeCost J6R24MeteredRecursion J6R30ProducedGateRegistry J6R32StatefulArithmetic
open J6R33StatefulArithmeticPage J6R36ChildFramedRoute J6R48RawRoute J6R48GeneratedAddons
open J6R48DFS J6R50Peak J6R50SourceProducer J6R51Peak J6R51Online

set_option autoImplicit false
set_option maxRecDepth 3700
set_option maxHeartbeats 21500000
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "P" => (Plan sel)
local notation "L" => PageBank f ell key prec tw bw page
local notation "J" => PageJob f ell key prec tw bw page

def uniformSidecarCap (s C owner addr key prec page : ℕ) : ℕ :=
  2*(C*s)*(addr+2*addonCap owner (Nat.clog 2 s) key prec page)

theorem actual_online_sidecar_phase_has_joint_peak
    (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ) (initial : L)
    (fits : q≤uniformWidth s C) (pageBound high fixed addr seed owner : ℕ)
    (pageFit : ExactPageFit M pageBound) (hi : ActualHighFit M high)
    (sizes : EntryWidths M fixed addr) (boot : BootBodyWidth M seed)
    (p : Path sel r c) (u : (P).Slot c) (w : (P).Slot ((P).child c u))
    (ownerFit : (M.demand (sourceState M p u) w).result.directory.ow≤owner) :
    let path := Path.step p u
    let B := stackBank (borns M) initial path
    let new := (M.demand (sourceState M p u) w).result.advance.next
    let j := new.birth.job
    ∃ b,OnlineTrace M retire initial (.step path w) b ∧
      residentAtlasBits B+pendingPageBits j+b+directoryBits B+(pairedAddonPayload new.site).length≤
        actualOnlineRoof (s:=s) (C:=C) initial r.edges r.prec pageBound high fixed addr seed+
          uniformSidecarCap s C owner addr key prec page := by
  let X := sourceState M p u
  let K := (M.demand X w).result
  let path := Path.step p u
  let B := stackBank (borns M) initial path
  let body := sourceBodyCap s C seed
  let j := K.advance.next.birth.job
  obtain ⟨b,trace,scheduled⟩ := same_online_arithmetic_and_atlas_at_path
    M retire initial fits pageBound high pageFit hi (.step path w)
  change residentAtlasBits (afterOne B j)+b≤_ at scheduled
  rw [true_queued_pages_are_exact_increment] at scheduled
  have dir := bounded_descriptor_stack_at_original_start (borns M) initial fixed addr body
    (geometry_of_real_demand_caps_the_raw_header M fixed addr seed sizes boot) path
  have sc := (true_demand_sidecar_has_its_fee_and_selected_fields M p u w).2.2.2
  have coord : dim (successorTicket (p.ticket u) w)≤Nat.clog 2 s := bits_le_lam _ _
  have edgeCount := actual_edges_uniform T path
  have addrFit : K.advance.next.birth.port≤addr := by
    have b := (sizes path w).2
    change K.advance.next.birth.port+6≤addr at b
    omega
  have hasOwner : K.directory.ow≤owner := ownerFit
  have width :
      addonCap K.directory.ow (dim (successorTicket (p.ticket u) w)) key prec page≤
        addonCap owner (Nat.clog 2 s) key prec page := by
    unfold addonCap
    omega
  have currentBound := sc.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 2 edgeCount)
    (Nat.add_le_add addrFit (Nat.mul_le_mul_left 2 width)))
  exact ⟨b,trace,Nat.add_le_add (Nat.add_le_add scheduled dir) currentBound⟩

#print axioms actual_online_sidecar_phase_has_joint_peak
end
end J6R52Peak
