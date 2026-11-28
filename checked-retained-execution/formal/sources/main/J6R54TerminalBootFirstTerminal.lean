import J6R54TerminalBootRetype
import J6R54TerminalBootPaidPath

/-! A measured first owner publication seeds the original measured
roster/terminal path. The chosen first bytes and charges are preserved;
this adapter does not claim to produce the exterior publication itself. -/
namespace J6R54TerminalBoot
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R27OriginalGate J6OrientedHost
open J6Mesh J6R35RootOrigins J6R34RootAtlas J6R31RootResidentTables J6R32RootGeneratedRegistryInputs
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe
open J6R26DescriptorTree J6R34ChildPath J6R36ChildFramedRoute J6R50SourceProducer
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R22Active J6R24MeteredRecursion
open J6R9Recursive J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R49SourceLayout
open J6R51ParentFrames J6R51Online J6R53TerminalGate J6R53TerminalExterior J6R41StructuredAllPaths
open J6R53OldOwner J6R54ExteriorOwner
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 48000000
set_option maxRecDepth 6500
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
variable (gate : Stamp key prec)
variable (boot : ExactPrintedBoot X M gate)
local notation "r" => (exteriorChild G ell X.centre X.sample X.group)

structure FirstRosterAndRekeys where
  first : ∀ w : (Plan sel).Slot r, Meter (CompleteRoster
    (M.initial w).result.site.oldKey (exteriorData X gate pad))
  steps : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel r c) (w : (Plan sel).Slot c)
    (incoming : RosterAt M (bootGates X) p w) (u : (Plan sel).Slot (p.ticket w).child),
    ActualOwnerWords M (bootGates X) p w incoming u

def roster_program_from_measured_first
    (A : FirstRosterAndRekeys X M gate) :
    PathRosterProgram M (bootGates X) where
  initial w := same_meter_first_roster X M gate boot w (A.first w)
  stepWords := A.steps

theorem terminal_from_first_raw_roster_and_measured_rekeys
    (A : FirstRosterAndRekeys X M gate)
    (gateWidth : gate.created.val=base)
    {c : Call (PhysicalHost f ell)} (p : Path sel r c) (w : (Plan sel).Slot c)
    (saved : CachedParentFrames (sourceState M p w).site)
    (groups : Meter (List (Word 6)))
    (groupLaw : groups.result=(runRosterAlong M (bootGates X)
      (roster_program_from_measured_first X M gate boot A) p w).result.order.map
      (fun v=>(ownerGroupRow (sourceState M p w).site v).group))
    (inj : Function.Injective (sourceState M p w).site.oldKey)
    (hBase : 0<base) {b : ℕ} (hb : 0<b) (fit : (p.ticket w).child.edges≤2^b)
    (rootLive : PageBank f ell key prec tw bw (pageKeyWidth m+pad)→Prop)
    (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
    (openRoot : IsLive (X.seed pad) B)
    (live : opened (borns M) rootLive (.step p w) B)
    (F : Frame f (p.ticket w).child.prec) :
    let prog := roster_program_from_measured_first X M gate boot A
    let out := meteredTerminalAfterRosterHistory X M prog p w saved groups groupLaw b F B
    ∃ word,out.result=some word ∧ F.decode word=reduce (p.ticket w).child.prec f ell ((p.ticket w).child.host.contract X.hf) :=
  actual_terminal_uses_computed_same_path_roster X M gate boot (roster_program_from_measured_first X M gate boot A)
    p w gateWidth saved groups groupLaw inj hBase hb fit rootLive B openRoot live F

end
#print axioms roster_program_from_measured_first
#print axioms terminal_from_first_raw_roster_and_measured_rekeys
end J6R54TerminalBoot
