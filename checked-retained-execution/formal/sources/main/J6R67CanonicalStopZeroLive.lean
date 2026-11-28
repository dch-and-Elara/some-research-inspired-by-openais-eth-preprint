import J6R67CanonicalStopZero
import J6R49LeafRuntime

/-! Runtime-ready zero stop at the same reached slot and opened bank.
The source proof relates the output to the original blueprint, not
to equality of the old opaque fallback syntax or its total Meter. -/
namespace J6R67CanonicalStop
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6R27OriginalGate J6OrientedHost
open J6Mesh J6R35RootOrigins J6R37StructuredRoot J6R34RootAtlas J6R31RootResidentTables
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R32RootGeneratedRegistryInputs
open J6R26DescriptorTree J6R34ChildPath J6R36ChildFramedRoute J6R50SourceProducer
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R22Active J6R24MeteredRecursion
open J6R9Recursive J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R49SourceLayout
open J6R51ParentFrames J6R51Online J6R52Terminal J6R53TerminalGate J6R53TerminalExterior
open J6R53OldOwner J6R50Leaf J6R41StructuredAllPaths J6R54TerminalBoot J6R51Leaf J6R48DFS
open J6R48Leaf J6R57Public J6R62Leaf J6R49Leaf

set_option quotPrecheck false
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 17000000
set_option maxRecDepth 4400
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
variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel)
  (exteriorChild G ell X.centre X.sample X.group))]
variable {c : Call (PhysicalHost f ell)}
variable (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c)
variable (w : (Plan sel).Slot c)

local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "K" => (p.ticket w).child
local notation "Y" => (sourceState M p w)
local notation "F" => (T.frame (Path.step p w).reached)
local notation "Bank" => (PageBank f ell key prec tw bw (pageKeyWidth m+pad))

theorem reached_zero_terminal_returns_original_blueprint
    (input : Meter (OwnerTerminalInput X p w (sourceState M p w)))
    (initial : Bank) (rootLive : IsLive (X.seed pad) initial) (ready : ReadyOnStack (borns M) initial)
    (gate : Stamp key prec) (boot : ExactPrintedBoot X M gate) (gateWidth : gate.created.val=base)
    (basePos : 0<base) (zero : (K).edges=0) :
    let active := stackBank (borns M) initial (Path.step p w)
    let out := zeroTerminal X M p w input active
    ∃ block,out.result=some block ∧
      (F).decode block=(sourceBlueprint sel Ext X.hf).program.run (K) := by
  let path := Path.step p w
  let active := stackBank (borns M) initial path
  have live : opened (borns M) (IsLive (X.seed pad)) path active :=
    stack_is_opened (borns M) initial (IsLive (X.seed pad)) (live_monotone (X.seed pad))
      rootLive ready path
  have extLive := opened_keeps_root X pad (borns M) path active live
  obtain ⟨value,paid,decode⟩ := zero_terminal_uses_actual_paid_source X M p w input active gate boot
    gateWidth basePos zero (IsLive (X.seed pad)) extLive live
  have cut : (K).edges≤(printedParams (f:=f) (ell:=ell) s).cutoff := zero.symm ▸ Nat.zero_le _
  exact ⟨value,paid,decode.trans (true_source_stops_on_same_host T path cut)⟩

#print axioms reached_zero_terminal_returns_original_blueprint
end
end J6R67CanonicalStop

