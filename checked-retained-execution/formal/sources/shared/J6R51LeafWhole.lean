import J6R51LeafMachine
import J6R51OnlineCorrect

/-! The official R51 root runner with the actual paid StoredSite
terminal implementation. Its former abstract LeafAgreement premise
is derived, on the same bank and source state, from the positive
resident chart condition. Zero and root leaves need no new chart. -/
namespace J6R51Leaf
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 A1R11 A1R12
open J6Mesh J6OrientedHost P11FullPacking P1DyadicGrid J6R24LegalLayout
open J6R10Repack J6R11Blueprint J6R11Repack J6R12Blueprint J6R21Ancestor J6R20Ancestor
open J6R14ZeroMode J6R27PrescribedProbe J6R32RootGeneratedRegistryInputs
open J6R31RootResidentTables J6R30GeneratedRootLayout J6R27OriginalGate J6R9PacketScopes
open J6ActiveRun J6ActiveSchedule J1PPrinted J6R26StablePreparedRoot
open J6R34RootAtlas J6R33StatefulArithmeticPage J6R32StatefulArithmetic
open J6R30ProducedGateRegistry J6R22Active J6R35RootOrigins J6R48Leaf J6R49Leaf
open J6R9Recursive J6R10Reachable J6R24MeteredRecursion J6R21Leaf J6R16ModeCost
open J6R26DescriptorTree J6R34ChildPath J6R25PreparedSupply
open J6R48DFS J6R50Leaf J6R50SourceProducer J6R51Online
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 47000000
set_option maxRecDepth 4800

noncomputable section
variable {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {V : Type} [Fintype V]
variable {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {q ro co d edgew tc tj key prec tw bw rate : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
variable {P : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (pad : ℕ)
local notation "ext" => exteriorChild G ell X.centre X.sample X.group
local notation "pg" => pageKeyWidth m+pad
local notation "SP" => printedParams (f:=f) (ell:=ell) s
variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel)
  (exteriorChild G ell X.centre X.sample X.group))]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (M : OnlineMachine P key prec tw bw (pageKeyWidth m+pad) rate)
variable (basePos : 0<base)
variable (rootOrd : Fin (exteriorChild G ell X.centre X.sample X.group).edges≃
  (exteriorChild G ell X.centre X.sample X.group).host.Edge)
variable (data : ∀ {v : Ticket sel (exteriorChild G ell X.centre X.sample X.group)}
  (site : StoredSite P v key prec tw bw (pageKeyWidth m+pad)),ResidentLeafData site)

def LoopCharts : Prop :=
  ∀ {c : Call (PhysicalHost f ell)} (p : Path sel ext c) (w : (Plan sel).Slot c),
    ((Plan sel).child c w).edges≤(SP).cutoff→0<((Plan sel).child c w).edges→
    let actual := sourceState M p w
    let J := actual.birth.native
    let D := data actual
    ∃ name : Vertex ((Plan sel).child c w)→J6R15ModeCost.Word D.own,
      D.roster=(vertexList ((Plan sel).child c w).host).map name ∧
      ∀ u : Vertex ((Plan sel).child c w),
        SourceCommand ((Plan sel).child c w).edges
          (fun j=>childKey P (p.ticket w) J.physical (actualEdgeOrder P (p.ticket w) J.physical j))
          D.lines D.table (name u)
          (sourceLeafRow X pad (machineInputs X pad M) basePos (Path.step p w)
            (actualEdgeOrder P (p.ticket w) J.physical) u).code

theorem wired_births_are_original :
    ((fun {_} p w=>borns (replaceTerminalFields X pad M basePos rootOrd data) p w) :
      J6R33StatefulArithmeticPage.Births P key prec tw bw pg)=
    (fun {_} p w=>borns M p w) := by
  funext c p w
  exact same_supplied_source_birth X pad M basePos rootOrd data p w

theorem proved_terminal_agreement
    (initial : PageBank f ell key prec tw bw pg)
    (rootLive : IsLive (X.seed pad) initial) (valid : ReadyOnStack (borns M) initial)
    (chart : LoopCharts X pad M basePos data) :
    LeafAgreement (replaceTerminalFields X pad M basePos rootOrd data) initial := by
  let R := replaceTerminalFields X pad M basePos rootOrd data
  refine ⟨?_,?_⟩
  · intro stop
    exact source_root_terminal_unchanged X pad (machineInputs X pad M) basePos stop rootOrd initial rootLive
  · intro c p w stop
    let walk := Path.step p w
    let B := stackBank (borns M) initial walk
    have Bchange : stackBank (borns R) initial walk=B :=
      congrArg (fun (F : J6R33StatefulArithmeticPage.Births P key prec tw bw pg)=>
        stackBank F initial walk) (wired_births_are_original X pad M basePos rootOrd data)
    have live : opened (borns M) (IsLive (X.seed pad)) walk B :=
      stack_is_opened (borns M) initial (IsLive (X.seed pad)) (live_monotone (X.seed pad))
        rootLive valid walk
    change (P.frame walk.reached).decode
      (R.leafAfter p w (sourceState R p w) stop (stackBank (borns R) initial walk)).result=_
    rw [Bchange]
    by_cases e : ((Plan sel).child c w).edges=0
    · have h := replacement_keeps_actual_source_state X pad M basePos rootOrd data p w
      rw [show sourceState R p w=sourceState M p w from h]
      exact (source_stored_empty_is_old X pad (machineInputs X pad M) basePos p w
        (sourceState M p w) (fun _=>data (sourceState M p w)) stop e B live).2
    · obtain ⟨name,names,allowed⟩ := chart p w stop (Nat.pos_of_ne_zero e)
      exact actually_connected_leaf_decodes X pad M basePos rootOrd data p w stop B live name names allowed

theorem actual_online_root_with_proved_terminal_fields
    (initial : PageBank f ell key prec tw bw pg)
    (rootLive : IsLive (X.seed pad) initial) (valid : ReadyOnStack (borns M) initial)
    (chart : LoopCharts X pad M basePos data)
    (retire : PageJob f ell key prec tw bw pg→ℕ) :
    let R := replaceTerminalFields X pad M basePos rootOrd data
    let out := runRoot R retire initial
    (P.frame (Path.root : Path sel ext ext).reached).decode out.result.1=
        (sourceBlueprint sel ext X.hf).program.run ext ∧ out.result.2=initial := by
  let R := replaceTerminalFields X pad M basePos rootOrd data
  have eq := wired_births_are_original X pad M basePos rootOrd data
  have readyEq : ReadyOnStack (borns M) initial=ReadyOnStack (borns R) initial :=
    congrArg (fun (F : J6R33StatefulArithmeticPage.Births P key prec tw bw pg)=>
      ReadyOnStack F initial) eq.symm
  have legal : ReadyOnStack (borns R) initial :=
    @Eq.mp (ReadyOnStack (borns M) initial) (ReadyOnStack (borns R) initial)
      readyEq (fun {_} p w=>valid p w)
  exact full_online_selected_source R initial retire legal
    (proved_terminal_agreement X pad M basePos rootOrd data initial rootLive valid chart)

#print axioms wired_births_are_original
#print axioms proved_terminal_agreement
#print axioms actual_online_root_with_proved_terminal_fields
end
end J6R51Leaf
