import J6R68RetireScratchScope
import J6R66ActiveRun

/-! Make the selected return observer explicit at both literal R66
entrances. The measured program projects to the original interpreter
with its original single sidecar, incoming owner, and parent restore.
The observation holds only the two named old/copied word pairs. -/
namespace J6R68.RetireScratch
open scoped Polynomial
open Polynomial AOracleMachineTime J6R21Ancestor J6R26DescriptorTree
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R50SourceProducer J6R24MeteredRecursion
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R51Online J6R51ParentFrames J6R52CacheSource J6R52CacheWhole J6R48RawRoute
open J6R54PeakInput J6R57ScopeFee J6R64Active J6R66Active J6R68.RecursivePeak

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 15500000
set_option maxRecDepth 4600
set_option maxSynthPendingDepth 12

noncomputable section
attribute [local irreducible] J6R12Blueprint.printedParams
variable {f : ℤ[X]} {ell s C key prec tw bw page width q cw : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
local notation "P" => (@Plan f ell s sel)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)
local notation "Here" => (Path.root : Path sel r r)

def observeOpenOnce {X : StoredSite T v key prec tw bw page} {u : (P).Slot v.child}
    {Out : Type} (started : Meter (LocalLoad X u)) (cache : CachedParentFrames X.site)
    (tails : SavedDirectoryTails width)
    (child : (next : StoredSite T (successorTicket v u) key prec tw bw page) → WithIncoming next Out)
    (bad : Meter Out) (B : L) :
    Meter (Out×L) × Option (TailCopyObservation width) :=
  let made := produceCacheSidecarOnce started.result cache
  let next := made.result.next
  let installed := installResidentBank next
  let out := observeHeaderScope tails (D:=PagedEnvelope f ell prec page) next.birth.job
    (fun R own=>child next installed.result R own) bad B
  (⟨out.1.result,started.steps+(made.steps+installed.steps)+out.1.steps⟩,out.2)

theorem observed_open_once_preserves_the_actual_meter
    {X : StoredSite T v key prec tw bw page} {u : (P).Slot v.child}
    {Out : Type} (started : Meter (LocalLoad X u)) (cache : CachedParentFrames X.site)
    (tails : SavedDirectoryTails width)
    (child : (next : StoredSite T (successorTicket v u) key prec tw bw page) → WithIncoming next Out)
    (bad : Meter Out) (B : L) :
    (observeOpenOnce started cache tails child bad B).1=
      openOnce started cache (retireSavedDirectory tails) child bad B := by
  unfold observeOpenOnce openOnce
  dsimp only
  rw [observed_header_projects_to_same_actual_meter]

theorem observed_open_once_on_the_actual_successor_has_two_tail_copies
    {X : StoredSite T v key prec tw bw page} {u : (P).Slot v.child}
    {Out : Type} (started : Meter (LocalLoad X u)) (cache : CachedParentFrames X.site)
    (tails : SavedDirectoryTails width)
    (child : (next : StoredSite T (successorTicket v u) key prec tw bw page) → WithIncoming next Out)
    (bad : Meter Out) (B : L) (legal : JobsReady B [started.result.advance.next.birth.job]) :
    observeOpenOnce started cache tails child bad B=
      (openOnce started cache (retireSavedDirectory tails) child bad B,some ⟨tails,tails⟩) := by
  apply Prod.ext
  · exact observed_open_once_preserves_the_actual_meter started cache tails child bad B
  · unfold observeOpenOnce
    dsimp only
    rw [one_emission_is_same_actual_next_site]
    exact legal_header_observes_exact_tail_copy tails _ _ bad B legal

def observeBootWithHeader {w : (P).Slot r} {Out : Type}
    (boot : Meter (StoredSite T ((Here).ticket w) key prec tw bw page))
    (tails : SavedDirectoryTails width)
    (child : (next : StoredSite T ((Here).ticket w) key prec tw bw page) → WithIncoming next Out)
    (bad : Meter Out) (B : L) :
    Meter (Out×L) × Option (TailCopyObservation width) :=
  let start := boot.result
  let scope := observeHeaderScope tails (D:=PagedEnvelope f ell prec page) start.birth.job
    (fun R own=>
      let loaded := installResidentBank start
      let done := child start loaded.result R own
      ⟨done.result,loaded.steps+done.steps⟩) bad B
  (⟨scope.1.result,boot.steps+scope.1.steps⟩,scope.2)

theorem observed_boot_preserves_the_actual_meter
    {w : (P).Slot r} {Out : Type}
    (boot : Meter (StoredSite T ((Here).ticket w) key prec tw bw page))
    (tails : SavedDirectoryTails width)
    (child : (next : StoredSite T ((Here).ticket w) key prec tw bw page) → WithIncoming next Out)
    (bad : Meter Out) (B : L) :
    (observeBootWithHeader boot tails child bad B).1=
      bootWithHeader boot (retireSavedDirectory tails) child bad B := by
  unfold observeBootWithHeader bootWithHeader
  dsimp only
  rw [observed_header_projects_to_same_actual_meter]

theorem observed_boot_on_the_actual_first_slot_has_two_tail_copies
    {w : (P).Slot r} {Out : Type}
    (boot : Meter (StoredSite T ((Here).ticket w) key prec tw bw page))
    (tails : SavedDirectoryTails width)
    (child : (next : StoredSite T ((Here).ticket w) key prec tw bw page) → WithIncoming next Out)
    (bad : Meter Out) (B : L) (legal : JobsReady B [boot.result.birth.job]) :
    observeBootWithHeader boot tails child bad B=
      (bootWithHeader boot (retireSavedDirectory tails) child bad B,some ⟨tails,tails⟩) := by
  apply Prod.ext
  · exact observed_boot_preserves_the_actual_meter boot tails child bad B
  · unfold observeBootWithHeader
    dsimp only
    exact legal_header_observes_exact_tail_copy tails _ _ bad B legal

theorem the_real_R66_child_returns_the_same_mounted_directory
    (M : OnlineMachine T key prec tw bw page q)
    (F : RetainedAfter T key prec tw bw page q cw)
    (tails : SavedDirectoryTails width)
    {c : Call (PhysicalHost f ell)} (p : Path sel r c) (w : (P).Slot c)
    (Y : StoredSite T (p.ticket w) key prec tw bw page) (live : ResidentBank Y) (B : L) :
    let mounted := afterOne B Y.birth.job
    (runAfter M F (retireSavedDirectory tails) c p w Y live mounted
      (show OwnsHeader Y.birth.job.entry.result mounted from rfl)).result.2=mounted :=
  active_after_restores M F (retireSavedDirectory tails) p w Y live _ _

#print axioms observed_open_once_preserves_the_actual_meter
#print axioms observed_open_once_on_the_actual_successor_has_two_tail_copies
#print axioms observed_boot_preserves_the_actual_meter
#print axioms observed_boot_on_the_actual_first_slot_has_two_tail_copies
#print axioms the_real_R66_child_returns_the_same_mounted_directory
end
end J6R68.RetireScratch
