import J6R54TerminalBootPath
import J6R54TerminalBootBinding
import J6R54TerminalBootRoster
import J6R54ExteriorOwnerChart

/-! The actual first paid owner table and the terminal's proof-side
Gate history are the same typed data. This adapter reuses the exact
raw bytes and fee of the measured first mount. Keys remain the
actual .site.oldKey, not independently ranked owner coordinates. -/
namespace J6R54TerminalBoot
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6R27OriginalGate J6OrientedHost
open J6Mesh J6R35RootOrigins J6R37StructuredRoot J6R34RootAtlas J6R31RootResidentTables
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R32RootGeneratedRegistryInputs
open J6R26DescriptorTree J6R34ChildPath J6R36ChildFramedRoute J6R50SourceProducer
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R22Active J6R24MeteredRecursion
open J6R9Recursive J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R49SourceLayout
open J6R51ParentFrames J6R51Online J6R53TerminalGate J6R53TerminalExterior J6R41StructuredAllPaths
open J6R53OldOwner J6R53OldOwnerRoot J6R54ExteriorOwner
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 48000000
set_option maxRecDepth 6200
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw own : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C rate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable (gate : Stamp key prec)
local notation "r" => (exteriorChild G ell X.centre X.sample X.group)

def same_meter_first_roster
    (boot : ExactPrintedBoot X M gate)
    (w : (Plan sel).Slot r)
    (loaded : Meter (CompleteRoster (M.initial w).result.site.oldKey (exteriorData X gate pad))) :
    Meter (RosterAt M (bootGates X) .root w) :=
  let old := loaded.result
  ⟨⟨old.order,old.unique,old.complete,old.raw,by
    rw [old.exactRows]
    apply List.map_congr_left
    intro u _
    refine congrArg (fun z=>RefRow.mk ((M.initial w).result.site.oldKey u) z) ?_
    rw [physical_first_owner_is_the_boot_source X gate u]
    change _=OwnerData.mk ((M.initial w).result.origins u) (bootGates X u)
    rw [boot.origins w]⟩,loaded.steps⟩

theorem retyped_first_roster_uses_identical_bytes
    (boot : ExactPrintedBoot X M gate)
    (w : (Plan sel).Slot r)
    (loaded : Meter (CompleteRoster (M.initial w).result.site.oldKey (exteriorData X gate pad))) :
    (same_meter_first_roster X M gate boot w loaded).result.raw=loaded.result.raw ∧
    (same_meter_first_roster X M gate boot w loaded).steps=loaded.steps :=
  ⟨rfl,rfl⟩

end
#print axioms same_meter_first_roster
#print axioms retyped_first_roster_uses_identical_bytes
end J6R54TerminalBoot
