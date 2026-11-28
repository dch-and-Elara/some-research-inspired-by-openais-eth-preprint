import J6R110ScopeWordRatesPositive
import J6R68RecursivePeakScope

/-! Typed arguments at a real R66 continuation: one installed resident,
a complete owner spool, and the actual preceding layout. -/
namespace J6R111KeptOwnerFlow
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R21Ancestor J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R35RootOrigins J6R26DescriptorTree J6R34ChildPath
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS
open J6R50Leaf J6R50SourceProducer J6R51Leaf J6R51Online J6R49Leaf J6R48Leaf
open J6R57Public J6R58LeafScale J6R62Leaf J6R27OriginalGate J6R36ChildFramedRoute J6R54TerminalBoot
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R37StructuredRoot J6R41StructuredAllPaths
open J6R52Terminal J6R53TerminalGate J6R53OldOwner J6R49SourceLayout J6R66LeafTariff J6R65LeafRate
open J6R52CacheWhole J6R51ParentFrames J6R82LayoutDebit J6R82LeafTime
open J6R9Recursive J6R58LeafScale J6R16ModeCost J6R14LayoutCost J6R68ActiveInputs
open V8NativeMessage.N2DLabels J6R10Repack J6R94HeldOwnerProvider J6R110ScopeWordRates
open J6R66Active J6R64Active J6R68.RecursivePeak J6R54PeakInput
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 18000000
set_option maxRecDepth 5500
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
variable {c : Call (PhysicalHost f ell)}
variable (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c)
variable (w : (Plan sel).Slot c)
variable (Y : StoredSite T (p.ticket w) key prec tw bw (pageKeyWidth m+pad))
local instance sourceEdge : Fintype c.host.Edge := c.host.finiteEdge

/-- The complete parent layout retained for this child, indexed by the same
already-paid physical owner roster. The fields are borrowed, not created here. -/
structure LabelWitness
    (R : CompleteRoster Y.site.oldKey (parentData Y (gateHistory T (bootGates X) p))) where
  names : Function.Injective Y.site.oldKey
  input : CallFormat (printedParams (f:=f) (ell:=ell) s) c
  ingress : Ingress input
  units : ℕ
  dims : ℕ
  copies : ℕ
  rank : ℕ
  extent : ℕ
  raw : KeptLayoutWords dims copies rank extent
  axis : List Bool
  law : ExistingRosterLabels Y (gateHistory T (bootGates X) p) R input ingress units raw.rawView axis

/-- No second call to `installResidentBank` is used to assemble the entry. -/
def bindKept {R : CompleteRoster Y.site.oldKey (parentData Y (gateHistory T (bootGates X) p))}
    (A : LabelWitness X p w Y R) (res : ResidentBank Y) : LiveKeptStopTapes X p w Y :=
  ⟨res,R,A.names,A.input,A.ingress,A.units,A.dims,A.copies,A.rank,A.extent,A.raw,A.axis,A.law⟩

structure CapturedEntry where
  resident : ResidentBank Y
  bank : PageBank f ell key prec tw bw (pageKeyWidth m+pad)
  own : OwnsHeader Y.birth.job.entry.result bank
  owners : CompleteRoster Y.site.oldKey (parentData Y (gateHistory T (bootGates X) p))
  labelled : LabelWitness X p w Y owners

def physicalEntered (A : CapturedEntry X p w Y) :
    Entered T key prec tw bw (pageKeyWidth m+pad) :=
  ⟨c,p,w,Y,A.resident,A.bank,A.own⟩

def readPositiveHere (A : CapturedEntry X p w Y) :
    Meter (Block (T.frame (Path.step p w).reached) ell) :=
  let input := readKeptStopTapes X p w Y (bindKept X p w Y A.labelled A.resident)
  let F := T.frame (Path.step p w).reached
  finishOwnerAttempt F (executeOwnerTerminal X p w Y input F A.bank)

theorem the_live_capture_is_an_actual_R66_entry (A : CapturedEntry X p w Y) :
    (physicalEntered X p w Y A).site=Y ∧
      (physicalEntered X p w Y A).resident=A.resident ∧
      (physicalEntered X p w Y A).bank=A.bank := ⟨rfl,rfl,rfl⟩

variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)

theorem same_entered_resident_and_bank_run_the_original_R65_reader
    (initial : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
    (res : ResidentBank (sourceState M p w))
    (owners : CompleteRoster (sourceState M p w).site.oldKey
      (parentData (sourceState M p w) (gateHistory T (bootGates X) p)))
    (A : LabelWitness X p w (sourceState M p w) owners) :
    let K := bindKept X p w (sourceState M p w) A res
    let Q : CapturedEntry X p w (sourceState M p w) :=
      ⟨res,stackBank (borns M) initial (.step p w),rfl,owners,A⟩
    readPositiveHere X p w (sourceState M p w) Q=
      readProvidedOnR65Bank X M p w
        (actualStoppedInputFromKeptTapes X M p w res owners K.names K.input K.ingress K.units K.raw K.axisBytes K.sameChart)
        initial := rfl

#print axioms bindKept
#print axioms the_live_capture_is_an_actual_R66_entry
#print axioms same_entered_resident_and_bank_run_the_original_R65_reader
end
end J6R111KeptOwnerFlow

