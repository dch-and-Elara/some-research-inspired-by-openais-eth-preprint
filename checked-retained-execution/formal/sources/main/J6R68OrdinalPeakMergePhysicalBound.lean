import J6R68OrdinalPeakMergeLivePath
import J6R57LiveSpaceCachedStack

/-! The R68 physical-ingress reserve can be reused after identifying
the actual object fields, not the numeric/paused peak of its old
evaluator. No two arithmetic traces are added. -/
namespace J6R68.OrdinalPeakMerge
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R16ModeCost
open J1PPrinted J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R21Ancestor J6R24MeteredRecursion J6R26DescriptorTree J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R48RawRoute J6R49DFS
open J6R50SourceProducer J6R51Online J6R51ParentFrames J6R52CacheWhole
open J6R52Peak J6R53PeakAddon J6R54PeakInput J6R57LiveSpace J6R62ActivePrep J6R63Ordinal J6R64Active J6R66Active
open J6R66.BootPeak J6R68.RecursivePeak
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 4300
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 13000000
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q cw b : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
variable {M : OnlineMachine T key prec tw bw page (q+1)}
variable {F : RetainedAfter T key prec tw bw page (q+1) cw}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)
local notation "PP" => (@Plan f ell s sel)

theorem parent_and_child_addon_views_fit_their_exact_cached_ingress
    (M : OnlineMachine T key prec tw bw page (q+1)) (initial : L)
    (p : Path sel r c) (u : (PP).Slot c) (w : (PP).Slot ((PP).child c u)) :
    (residentAddonPayload (sourceEntered M initial p u).resident).length+
      (residentAddonPayload (sourceEntered M initial (.step p u) w).resident).length≤
      cachedIngressBits M (.step (.step p u) w) := by
  let a := (residentAddonPayload (sourceEntered M initial p u).resident).length
  let b := (residentAddonPayload (sourceEntered M initial (.step p u) w).resident).length
  change a+b≤physicalInputStackBits M (.step (.step p u) w)+
    (rawStackBits M (.step (.step p u) w)+(addonStackBits M p+a+b)+cacheStackBits M (.step (.step p u) w))
  omega

theorem selected_ranked_pause_and_child_fit_the_same_child_physical_reserve
    (R : RankedRequests M F b) (wired : HasOldCheckedWiring R)
    (retire : J → ℕ) (initial : L)
    (p : Path sel r c) (u : (PP).Slot c)
    (on : (SP).cutoff<((PP).child c u).edges) (t : Center SP ((PP).child c u))
    (H : PulseWitness R (sourceEntered M initial p u) on t)
    (z : Probe SP ((PP).child c u)) (g : Fin 64)
    (ready : ReadyOnStack (borns M) initial) :
    let x := sourceEntered M initial p u
    let w := atAddress x on t z H.mode g
    let childPath := Path.step (Path.step p u) w
    selectedPauseAndChild H (mountResident x.site x.resident).result z g≤(atTape M F x on t).words.length*(q+1)+2*b+
      mountedSelectedBits (stackBank (borns M) initial childPath)+cachedIngressBits M childPath := by
  let x := sourceEntered M initial p u
  let w := atAddress x on t z H.mode g
  let future := Path.step (Path.step p u) w
  let old := sourceEntered M initial (.step p u) w
  have same := (actual_ranked_publication_installs_same_child_objects_on_the_r68_path
    R wired retire initial p u on t H z g ready).1
  have width := (real_pulse_observation_is_same_row_and_two_words H).2
  let room := (atTape M F x on t).words.length*(q+1)+2*b
  have addon := parent_and_child_addon_views_fit_their_exact_cached_ingress M initial p u w
  unfold selectedPauseAndChild
  dsimp only
  rw [same,width]
  change room+mountedSelectedBits old.bank+(residentAddonPayload x.resident).length+
    (residentAddonPayload old.resident).length≤
    room+mountedSelectedBits old.bank+cachedIngressBits M future
  simpa only [Nat.add_assoc] using Nat.add_le_add_left addon (room+mountedSelectedBits old.bank)

#print axioms parent_and_child_addon_views_fit_their_exact_cached_ingress
#print axioms selected_ranked_pause_and_child_fit_the_same_child_physical_reserve
end
end J6R68.OrdinalPeakMerge

