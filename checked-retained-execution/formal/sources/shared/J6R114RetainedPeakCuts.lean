import J6R114RetainedPeakActive
import J6R111KeptOwnerFlowNext

/-! The selected successor cut of the retained run. The new capture
uses one real installation, the actual new head, and the parent's
already emitted output for its layout/labels. Only the new publication
payload of the bank is added while the parent is suspended. -/
namespace J6R114RetainedPeak
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R21Ancestor J6OrientedHost J6R34RootAtlas
open J6Mesh J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R34ChildPath J6R37StructuredRoot J6R41StructuredAllPaths
open J6R54TerminalBoot J6R53OldOwner J6R53OldOwnerRoot J6R26DescriptorTree J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion J6R52CacheSource
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS J6R10Repack J6ActiveSchedule
open J6R50SourceProducer J6R51Online J6R51ParentFrames J6R52CacheWhole J6R64Active J6R66Active
open J6R59Public J6R94HeldOwnerProvider J6R54PeakInput J6R48RawRoute J6R49SourceLayout
open J6R58RequestSource J6R52Dispatch J6R53Dispatch J6R27OriginalGate J6R36ChildFramedRoute
open J6R62ActivePrep J6R82LayoutDebit V8NativeMessage.N2DLabels J6R68ActiveInputs J6R68ActiveInputs.Sweep
open J6R9Recursive J6R22Active J6R49DFS J6R10Reachable
open J6R111KeptOwnerFlow J6R52Peak J6R53PeakAddon J6R55SelectedPeak J6R75RawPeak J6R66.BootPeak

set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 17500000
set_option maxRecDepth 4950
set_option maxSynthPendingDepth 12
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C rate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable {rank : ℕ} (D : KeptDrivers X M rank)
variable (x : KeptInvocation X M)
variable (on : (printedParams (f:=f) (ell:=ell) s).cutoff<x.call.edges)
variable (u : (Plan sel).Slot (x.path.ticket x.slot).child)
variable (retire : PageJob f ell key prec tw bw (pageKeyWidth m+pad)→ℕ)

local notation "Header" => (incumbentAtActualActive X M x)
local notation "Cache" => (mountedAtActualActive X M x)
local notation "PackOut" => (layoutAtActualActive X M D x on)
local notation "xPath" => (Path.step x.path x.slot)

def actualActiveOwnerLoad :=
  retainActualSelectedDemand X x.path x.slot x.site x.entry M u (Header).result

local notation "Load" => (actualActiveOwnerLoad X M x u)
local notation "Next" => ((produceCacheSidecarOnce (Load).result.load (Cache).result).result.next)
local notation "Code" => (actual_live_keys_at_the_selected_site X M D x u)

def actualActiveBorrowedLabels :=
  checkedChildLabelWords X x.path x.slot x.site x.entry M on (Header).result
    (D.layout x on (Header).result) u (Cache).result Code (PackOut).result rfl

local notation "Borrow" => (actualActiveBorrowedLabels X M D x on u)
local notation "Roster" => (carriedRosterAtEmission X x.path x.slot x.site u Load (Cache).result Code)

def successfulActiveCapture : CapturedEntry X xPath u Next :=
  ⟨(installResidentBank Next).result,afterOne x.entry.bank (Next).birth.job,rfl,Roster,Borrow⟩

local notation "Child" => (successfulActiveCapture X M D x on u)

theorem actual_child_observed_labels_are_the_parent_single_emission :
    packedKeptBits (Child).labelled.raw=packedKeptBits (PackOut).result :=
  rfl

/-- One selected child cut, with its parent cache still accounted for.
The already-shared layout is not serialized or counted again. -/
def activeChildCutBits (shared : ℕ) : ℕ :=
  activeRetainedBits X M D x on shared +
    mountedInsertionBits (Next).birth.job +
    (residentAddonPayload (Child).resident).length +
    (indexedOwnerTape (Child).owners.raw).length + (Child).labelled.axis.length

theorem actual_active_child_cut_has_both_raw_owner_tapes_and_one_bank_insertion (shared : ℕ) :
    let parent := x.entry
    let new := Child
    new.bank=afterOne parent.bank (Next).birth.job ∧
    new.resident=(installResidentBank Next).result ∧
    HEq new.owners.raw (Load).result.held.raw ∧
    mountedSelectedBits new.bank=mountedSelectedBits parent.bank+mountedInsertionBits (Next).birth.job ∧
    activeChildCutBits X M D x on u shared=
      activeRetainedBits X M D x on shared+mountedInsertionBits (Next).birth.job+
      (residentAddonPayload new.resident).length+
      (indexedOwnerTape new.owners.raw).length+new.labelled.axis.length :=
  ⟨rfl,rfl,(emitted_child_keeps_the_complete_original_roster_in_its_paid_order X x.path x.slot
    x.site u Load (Cache).result Code).2.1,
    publication_adds_exact_selected_record x.entry.bank (Next).birth.job,
    rfl⟩

theorem successful_retained_scope_consumes_the_observed_capture
    (legal : JobsReady x.entry.bank [(Next).birth.job])
    (bad : Meter (Block (T.frame (Path.step xPath u).reached) ell)) :
    let same := selected_load_emits_the_actual_driver_source_after_retention X x.path x.slot x.site
      x.entry M u (Header).result (Cache).result x.actualSite
    let resume := fun entered : CapturedEntry X xPath u Next =>
      runRetained X M D retire ⟨x.call,xPath,u,_,same,entered⟩
    let next := Next
    let made := produceCacheSidecarOnce (Load).result.load (Cache).result
    let done := resume Child
    let j := next.birth.job
    nextR66OwnerScope X x.path x.slot x.site u Load (Cache).result Code retire Borrow resume bad x.entry.bank =
      ⟨(done.result.1,x.entry.bank),(Load).steps+(made.steps+(installResidentBank next).steps)+
        (publishFee x.entry.bank j.entry j.offset j.built+done.steps+retire j+4)⟩ :=
  next_R66_scope_keeps_the_paid_roster_and_actual_installed_resident X x.path x.slot
    x.site u Load (Cache).result Code retire Borrow _ bad x.entry.bank legal

#print axioms actual_child_observed_labels_are_the_parent_single_emission
#print axioms activeChildCutBits
#print axioms actual_active_child_cut_has_both_raw_owner_tapes_and_one_bank_insertion
#print axioms successful_retained_scope_consumes_the_observed_capture
end
end J6R114RetainedPeak

