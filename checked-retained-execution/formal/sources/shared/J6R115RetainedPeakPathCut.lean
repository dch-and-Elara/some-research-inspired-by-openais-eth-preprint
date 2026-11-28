import J6R114RetainedPeakCuts
import J6R115RetainedActualChild

/-! Compose the named R114 cut with the literal child of the same
retained interpreter. The current bank already contains the ancestors'
publications. The child's borrowed packed layout is already one of
the named fields in the cut; neither is added a second time. -/
namespace J6R115RetainedPeakPath
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
open J6R114RetainedPeak

set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 12000000
set_option maxRecDepth 4900
set_option maxSynthPendingDepth 12
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C rate rank : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (D : KeptDrivers X M rank)
variable (x : KeptInvocation X M)

def invocationEntryBits (shared : ℕ) : ℕ :=
  entryKeptBits X x.path x.slot x.site x.entry shared

/-- The ancestor contribution still named at the child. It omits
the current outgoing packed data: that word tape is already the
child's inherited packed data. The current bank and common table
also remain counted under the child's entry role, not here. -/
def suspendedParentBits : ℕ :=
  (residentAddonPayload x.entry.resident).length+
    (indexedOwnerTape x.entry.owners.raw).length+packedKeptBits x.entry.labelled.raw+
    x.entry.labelled.axis.length+
    (cachedWireBits (mountedAtActualActive X M x).result).length+
    rawLayoutBits oneOwnerHeaderBits (incumbentAtActualActive X M x).result.raw

variable (on : (printedParams (f:=f) (ell:=ell) s).cutoff<x.call.edges)
variable (u : (Plan sel).Slot x.call)

theorem same_literal_child_inherits_the_single_parent_packed_output :
    packedKeptBits (retainedActiveChildAt X M D x on u).entry.labelled.raw =
      packedKeptBits (layoutAtActualActive X M D x on).result :=
  actual_child_observed_labels_are_the_parent_single_emission X M D x on u

/-- At this native child cut, move the common bank and the borrowed
packed words to the child entry role. This is an exact equality
for the named fields, not a deletion of the parent data. -/
theorem exact_child_cut_is_suspended_parent_plus_that_child_entry (shared : ℕ) :
    activeChildCutBits X M D x on u shared =
      suspendedParentBits X M x + invocationEntryBits X M
        (retainedActiveChildAt X M D x on u) shared := by
  let child := retainedActiveChildAt X M D x on u
  let emitted := layoutAtActualActive X M D x on
  have chart : packedKeptBits child.entry.labelled.raw=packedKeptBits emitted.result :=
    same_literal_child_inherits_the_single_parent_packed_output X M D x on u
  have bank : mountedSelectedBits child.entry.bank=mountedSelectedBits x.entry.bank+
      mountedInsertionBits child.site.birth.job :=
    (actual_active_child_cut_has_both_raw_owner_tapes_and_one_bank_insertion X M D x on u shared).2.2.2.1
  change activeChildCutBits X M D x on u shared =
    suspendedParentBits X M x +
      (shared+mountedSelectedBits child.entry.bank+(residentAddonPayload child.entry.resident).length+
        (indexedOwnerTape child.entry.owners.raw).length+packedKeptBits child.entry.labelled.raw+
        child.entry.labelled.axis.length)
  rw [chart,bank]
  change (shared+mountedSelectedBits x.entry.bank+
      (residentAddonPayload x.entry.resident).length+(indexedOwnerTape x.entry.owners.raw).length+
      packedKeptBits x.entry.labelled.raw+x.entry.labelled.axis.length+
      (cachedWireBits (mountedAtActualActive X M x).result).length+
      rawLayoutBits oneOwnerHeaderBits (incumbentAtActualActive X M x).result.raw+
      packedKeptBits emitted.result) +
      mountedInsertionBits child.site.birth.job+
      (residentAddonPayload child.entry.resident).length+
      (indexedOwnerTape child.entry.owners.raw).length+child.entry.labelled.axis.length = _
  unfold suspendedParentBits
  ac_rfl

theorem actual_parent_active_bits_are_at_most_the_child_cut (shared : ℕ) :
    activeRetainedBits X M D x on shared ≤ activeChildCutBits X M D x on u shared := by
  unfold activeChildCutBits
  omega

#print axioms invocationEntryBits
#print axioms suspendedParentBits
#print axioms same_literal_child_inherits_the_single_parent_packed_output
#print axioms exact_child_cut_is_suspended_parent_plus_that_child_entry
#print axioms actual_parent_active_bits_are_at_most_the_child_cut
end
end J6R115RetainedPeakPath

