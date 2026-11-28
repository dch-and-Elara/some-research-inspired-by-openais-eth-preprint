import J6R64BootSeatsNative
import J6R55BootBodiesOccurrence

/-! Proof that the actual R55 physical writer and given receiving-seats
file can be fed in lockstep when the already supplied receiving chart
uses the printed exterior order. Works also for an empty source. -/
namespace J6R64.BootSeats
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R26DescriptorTree J6R35RootOrigins J6R36ChildFramedRoute
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R34RootAtlas J6R41StructuredAllPaths
open J6Mesh J6OrientedHost J6R24LegalLayout J6R10Repack J6R12Blueprint
open J6R12Repack J6ActiveRun J6ActiveSchedule J6R32StatefulArithmetic
open J6R32ChildResidentTransfer J6R27OriginalGate J6R33StatefulArithmeticPage
open J6R37StructuredRoot J6R30GeneratedRootLayout J6R25PreparedSupply
open J6R48RawRoute J6R11Blueprint J1PPrinted J6R24MeteredRecursion J6R50SourceProducer
open J6R55BootBodies
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4200
set_option Elab.async false

noncomputable section
attribute [local irreducible] J6R12Blueprint.printedParams
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {P₀ : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P₀
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
variable {s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group))
local notation "first" => ((Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group) (exteriorChild G ell X.centre X.sample X.group)).ticket w)
variable {b : ℕ}

theorem paired_order_of_real_boot_occurrence
    (template : Meter (OccurrenceInput T first key prec tw bw (pageKeyWidth m+pad)))
    (L : BootLaneTape X gate pad) (S : TerminalSeats X sel (ticketReady T first) (first).centerAt b)
    (agree : template.result.geometry.edges=orderedExteriorEdges X) :
    let I := (bootOccurrence X gate pad w template L S).result
    I.native.result.physical.order=pairedPorts I.geometry.edges := by
  change pairedPorts (orderedExteriorEdges X)=pairedPorts template.result.geometry.edges
  exact congrArg pairedPorts agree.symm

#print axioms paired_order_of_real_boot_occurrence
end
end J6R64.BootSeats
