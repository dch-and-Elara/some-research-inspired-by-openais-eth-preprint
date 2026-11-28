import J6R54TerminalBootPath
import J6R54TerminalBootRoster

/-! Consume the actual paid owner-history output, not an externally
materialized all-path owner table. The actual final group words are
separately measured. This does not charge the original DFS a second
time or pretend the caller already generated those local words. -/
namespace J6R54TerminalBoot
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R27OriginalGate J6OrientedHost
open J6Mesh J6R35RootOrigins J6R34RootAtlas J6R31RootResidentTables J6R32RootGeneratedRegistryInputs
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe
open J6R26DescriptorTree J6R34ChildPath J6R36ChildFramedRoute J6R50SourceProducer
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R22Active J6R24MeteredRecursion
open J6R9Recursive J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R49SourceLayout
open J6R51ParentFrames J6R51Online J6R53TerminalGate J6R53TerminalExterior J6R41StructuredAllPaths
open J6R53OldOwner
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 46000000
set_option maxRecDepth 6300
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
variable (prog : PathRosterProgram M (bootGates X))
variable {c : Call (PhysicalHost f ell)}
variable (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c)
variable (w : (Plan sel).Slot c)

def meteredTerminalAfterRosterHistory
    (saved : CachedParentFrames (sourceState M p w).site)
    (groups : Meter (List (Word 6)))
    (groupLaw : groups.result=(runRosterAlong M (bootGates X) prog p w).result.order.map
      (fun v=>(ownerGroupRow (sourceState M p w).site v).group))
    (b : ℕ) (F : Frame f (p.ticket w).child.prec) (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad)) :
    Meter (Option (Block F ell)) :=
  let site := sourceState M p w
  let prior := runRosterAlong M (bootGates X) prog p w
  let H := useCompleteRoster site (parentData site (gateHistory T (bootGates X) p))
    prior.result groups.result groupLaw
  let run := meteredTerminalFromOwners site saved H.result.raw prior.result.raw b F B
  ⟨run.result,prior.steps+groups.steps+H.steps+run.steps+5⟩

include boot in
theorem actual_terminal_uses_computed_same_path_roster
    (gateWidth : gate.created.val=base)
    (saved : CachedParentFrames (sourceState M p w).site)
    (groups : Meter (List (Word 6)))
    (groupLaw : groups.result=(runRosterAlong M (bootGates X) prog p w).result.order.map
      (fun v=>(ownerGroupRow (sourceState M p w).site v).group))
    (inj : Function.Injective (sourceState M p w).site.oldKey)
    (hBase : 0<base) {b : ℕ} (hb : 0<b) (fit : (p.ticket w).child.edges≤2^b)
    (rootLive : PageBank f ell key prec tw bw (pageKeyWidth m+pad)→Prop)
    (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
    (openRoot : IsLive (X.seed pad) B)
    (live : opened (borns M) rootLive (.step p w) B)
    (F : Frame f (p.ticket w).child.prec) :
    let out := meteredTerminalAfterRosterHistory X M prog p w saved groups groupLaw b F B
    ∃ word,out.result=some word ∧ F.decode word=reduce (p.ticket w).child.prec f ell ((p.ticket w).child.host.contract X.hf) := by
  let site := sourceState M p w
  let prior := runRosterAlong M (bootGates X) prog p w
  let H := useCompleteRoster site (parentData site (gateHistory T (bootGates X) p))
    prior.result groups.result groupLaw
  exact actual_terminal_on_one_printed_boot X M gate boot p w gateWidth saved H.result prior.result
    inj hBase hb fit rootLive B openRoot live F

end
#print axioms meteredTerminalAfterRosterHistory
#print axioms actual_terminal_uses_computed_same_path_roster
end J6R54TerminalBoot
