import J6R68RecursivePeakPaths
import J6R68RecursivePeakFrames
import J6R68RecursivePeakStaging

/-! Combined selected recursive storage. No inferred allocator peak:
the covered quantities are the retained literal physical input tape,
raw and indexed addon rows, cached frames, actual live directory,
creation-polynomial frame, Page payload, and actual suspended numerical
and mode state, including outgoing prefix views. -/
namespace J6R68.RecursivePeak
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R16ModeCost
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R24MeteredRecursion J6R26DescriptorTree J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49LiveBits
open J6R50SourceProducer J6R51Online J6R51Peak J6R52Peak J6R52CacheWhole
open J6R53PeakAddon J6R54PeakInput J6R57LiveSpace J6R66.BootPeak
open J6R63Active J6R64Active J6R66Active J6R49DFS
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4650
set_option maxHeartbeats 19500000
set_option Elab.async false

noncomputable section
attribute [local irreducible] J6R12Blueprint.printedParams
variable {f : ℤ[X]} {ell s C key prec tw bw page q cw ew : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (@Plan f ell s sel)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)
local notation "Machine" => (OnlineMachine T key prec tw bw page q)

def recursiveResidentBits (shared : ℕ) (M : Machine) (B : PageBank f ell key prec tw bw page) (p : Path sel r c)
    (paused : ℕ) : ℕ :=
  shared+paused+mountedSelectedBits (stackBank (borns M) B p)+cachedIngressBits M p

def recursiveResidentRoof (shared : ℕ) (B : PageBank f ell key prec tw bw page)
    (r : Call (PhysicalHost f ell)) (pageBound high fixed addr seed owner : ℕ) (s C : ℕ) : ℕ :=
  shared+actualOnlineRoof (s:=s) (C:=C) B r.edges r.prec pageBound high fixed addr seed+
    cachedIngressRoof r.edges s C addr seed owner key prec page+
    (bankFrameBits B+pathLimit s C*frameSlope (prec:=prec) (s:=s) (r:=r))

variable (M : OnlineMachine T key prec tw bw page q) (F : RetainedAfter T key prec tw bw page q cw)
variable (E : RootInputs T key prec tw bw page cw ew)
variable (B : PageBank f ell key prec tw bw page) (own : OwnsHeader E.header B) (retire : PageJob f ell key prec tw bw page→ℕ)

private theorem live_high_is_actual_high (high : ℕ)
    (hi : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (a : (S).cutoff<x.edges),
      x.prec+(liveActiveAt M F E B own p a).result.extraPrecision≤high) :
    ActualHighFit (shadow M F E B own) high := by
  intro x p a
  rw [same_actual_preparation_for_pause M F E B own p a]
  exact hi p a

private theorem resident_equals_old_selected_plus_own_frame
    (shared b : ℕ) (p : Path sel r c) :
    recursiveResidentBits shared M B p b=
      selectedCachedStackBits shared (shadow M F E B own) B p b+
        bankFrameBits (stackBank (borns M) B p) := by
  obtain ⟨ingress,bank⟩ := same_source_ingress_and_directory M F E B own p
  unfold recursiveResidentBits selectedCachedStackBits mountedSelectedBits
  rw [ingress,bank]
  ac_rfl

theorem real_r66_resident_path_has_joint_selected_bound
    (shared : ℕ) (fits : q≤uniformWidth s C) (pageBound high fixed addr seed owner : ℕ)
    (pageFit : ExactPageFit (shadow M F E B own) pageBound)
    (hi : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (a : (S).cutoff<x.edges),
      x.prec+(liveActiveAt M F E B own p a).result.extraPrecision≤high)
    (sizes : EntryWidths (shadow M F E B own) fixed addr)
    (boot : BootBodyWidth (shadow M F E B own) seed)
    (owners : OwnerWidth (shadow M F E B own) owner)
    (legal : ReadyOnStack (borns M) B) (p : Path sel r c) :
    ∃ b,CachedPausePath (shadow M F E B own) retire B p b ∧
      recursiveResidentBits shared M B p b≤recursiveResidentRoof shared B r pageBound high fixed addr seed owner s C := by
  let Q := shadow M F E B own
  have admissible : ReadyOnStack (borns Q) B := by
    rw [shadow_births_unchanged M F E B own]
    exact legal
  obtain ⟨b,obs,cap⟩ := all_named_fields_on_same_cached_path_have_joint_cap shared Q retire B fits
    pageBound high fixed addr seed owner pageFit (live_high_is_actual_high M F E B own high hi)
    sizes boot owners admissible p
  have frame := actual_live_frame_stack_is_bounded M B p
  refine ⟨b,obs,?_⟩
  rw [resident_equals_old_selected_plus_own_frame M F E B own shared b p]
  exact Nat.add_le_add cap frame

/-- The parent arithmetic is still suspended during child writes.
The staging cut has its actual outgoing prefix, not a fresh second
copy of every inherited Page. The true child reserve for the same
suspension dominates it (and includes the child Page and header). -/
theorem all_recursive_write_points_fit_the_next_actual_resident_bound
    (shared : ℕ) (fits : q≤uniformWidth s C) (pageBound high fixed addr seed owner : ℕ)
    (pageFit : ExactPageFit (shadow M F E B own) pageBound)
    (hi : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (a : (S).cutoff<x.edges),
      x.prec+(liveActiveAt M F E B own p a).result.extraPrecision≤high)
    (sizes : EntryWidths (shadow M F E B own) fixed addr)
    (boot : BootBodyWidth (shadow M F E B own) seed)
    (owners : OwnerWidth (shadow M F E B own) owner)
    (legal : ReadyOnStack (borns M) B) (p : Path sel r c) (w : (P).Slot c) :
    ∃ b,CachedPausePath (shadow M F E B own) retire B (.step p w) b ∧
      recursiveResidentBits shared M B (.step p w) b≤recursiveResidentRoof shared B r pageBound high fixed addr seed owner s C ∧
      ∀ point,recursiveStagingBits M B p w shared b point≤recursiveResidentRoof shared B r pageBound high fixed addr seed owner s C := by
  obtain ⟨b,obs,cap⟩ := real_r66_resident_path_has_joint_selected_bound M F E B own retire shared fits
    pageBound high fixed addr seed owner pageFit hi sizes boot owners legal (.step p w)
  exact ⟨b,obs,cap,fun point=>(suspended_parent_plus_staging_fits_the_actual_child_reserve M B p w shared b point).trans cap⟩

#print axioms real_r66_resident_path_has_joint_selected_bound
#print axioms all_recursive_write_points_fit_the_next_actual_resident_bound
end
end J6R68.RecursivePeak