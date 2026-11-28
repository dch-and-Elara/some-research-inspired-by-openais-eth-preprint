import J6R57LiveSpaceBootBits
import J6R55TerminalBootJoinedCore
import J6R55SelectedPeakBootLink
import J6R54PeakInputOccurrence

/-! The tape charged once as globally shared is the very lane tape
consumed by every first request of the generated exterior machine.
The new port file stored in its actual initial occurrence is counted
separately by the later DFS input observer. -/
namespace J6R57LiveSpace
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6R27OriginalGate J6OrientedHost
open J6Mesh J6R35RootOrigins J6R37StructuredRoot J6R34RootAtlas J6R31RootResidentTables
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R32RootGeneratedRegistryInputs
open J6R26DescriptorTree J6R34ChildPath J6R36ChildFramedRoute J6R50SourceProducer
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R22Active J6R24MeteredRecursion
open J6R9Recursive J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R49SourceLayout
open J6R55TerminalBootJoined J6R54PeakInput J6R55SelectedPeak
open J6R53OldOwner J6R53OldOwnerRoot J6R54ExteriorOwner J6R41StructuredAllPaths J6R51Online J6R55TerminalOrigin J6R54TerminalBoot J6R55BootBodies
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 33000000
set_option maxRecDepth 6100
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw own rate : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
variable {s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable {rootName : SourceVertex P→Word own}
variable (root : RootRoster (P:=P) gate pad rootName)



variable (M : (OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate))

variable (A : FirstBodyProgram X gate pad T)


variable (D : OwnerWordsAtBodies X gate pad root A)
variable (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
variable (live : IsLive (X.seed pad) B) (rootInj : Function.Injective rootName)

theorem the_shared_file_is_the_input_of_the_real_initial_slots
    (w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group)) (k : ℕ) :
    let N := withJoinedBoot X gate pad root M A D B live rootInj
    let out := readFirstPhysical X gate pad A.lanes (A.seats w)
    let supplied := (N.initial w).result.input
    sharedBootBits X A.lanes=(orderedExteriorEdges X).length*rootLaneRowBits m key prec pad ∧
    sourcePhysicalBitTape supplied=out.result.raw.flatMap physicalPortWords ∧
    bootWriterFocusBits A.lanes.run.result (A.seats w).made.result out.result.raw k≤
      sharedBootBits X A.lanes+((A.seats w).made.result.flatMap physicalSeatBits).length+
        (sourcePhysicalBitTape supplied).length := by
  let N := withJoinedBoot X gate pad root M A D B live rootInj
  let out := readFirstPhysical X gate pad A.lanes (A.seats w)
  let supplied := (N.initial w).result.input
  have used : supplied=(bodyAtActualSlot X gate pad A w).result :=
    joined_source_identity X gate pad root M A D B live rootInj w
  have exactFile : sourcePhysicalBitTape supplied=out.result.raw.flatMap physicalPortWords := by
    rw [used]
    rfl
  refine ⟨exact_shared_boot_file_width X A.lanes,exactFile,?_⟩
  change bootWriterFocusBits A.lanes.run.result (A.seats w).made.result out.result.raw k≤
    sharedBootBits X A.lanes+((A.seats w).made.result.flatMap physicalSeatBits).length+
      (sourcePhysicalBitTape supplied).length
  rw [exactFile]
  exact actual_boot_writer_focus_is_bounded_by_full_returned_tape A.lanes.run.result (A.seats w).made.result k

#print axioms the_shared_file_is_the_input_of_the_real_initial_slots
end
end J6R57LiveSpace
