import J6R68LeafPeakOwner
import J6R68LeafPeakMaximum
import J6R68RecursivePeakTotal

/-! The positive literal owner terminal, one scaffolded actual R66
paused/entered path, and the maximum of its actual reading/summing
cuts. No equality to a replacement leaf interpreter is presumed. -/
namespace J6R68.LeafPeak
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R35RootOrigins J6R26DescriptorTree J6R34ChildPath
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS
open J6R9Recursive J6R50Leaf J6R50SourceProducer J6R51Leaf J6R51Online J6R49Leaf J6R48Leaf
open J6R57Public J6R62Leaf J6R54TerminalBoot J6R52Terminal J6R22Active J6R53TerminalGate
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R37StructuredRoot J6R41StructuredAllPaths
open J6R55CachedLedger J6R56PrintedExponent J6R49Cost J6R16ModeCost J6R10Reachable
open J6R64Active J6R66Active J6R30ProducedGateRegistry J6R68.RecursivePeak
open J6R57LiveSpace J6R51Peak J6R52Peak J6R50Peak J6ActiveSchedule
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4950
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 19500000
set_option Elab.async false

noncomputable section
attribute [local irreducible] J6R12Blueprint.printedParams
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {plant : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) plant
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C rate cw ew : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable {c : Call (PhysicalHost f ell)}
local notation "Pg" => (pageKeyWidth m+pad)
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (@Plan f ell s sel)
local notation "Bank" => (PageBank f ell key prec tw bw (pageKeyWidth m+pad))
local notation "Job" => (PageJob f ell key prec tw bw (pageKeyWidth m+pad))
local notation "Cmd" => (ReadCmd key (pageKeyWidth m+pad))
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel)
  (exteriorChild G ell X.centre X.sample X.group))]

theorem same_r66_positive_owner_leaf_has_paused_and_local_named_peak
    (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
    (basePos : 0<base)
    (ord : Fin (exteriorChild G ell X.centre X.sample X.group).edges ≃
      (exteriorChild G ell X.centre X.sample X.group).host.Edge)
    (ownerInputs : OwnerInputProvider (T:=T) (pad:=pad) X)
    (gate : Stamp key prec) (boot : ExactPrintedBoot X M gate)
    (F : RetainedAfter T key prec tw bw Pg rate cw) (E : RootInputs T key prec tw bw Pg cw ew)
    (retire : Job→ℕ) (B0 : Bank) (own : OwnsHeader E.header B0)
    (rootLive : IsLive (X.seed pad) B0) (valid : ReadyOnStack (borns M) B0)
    (supply : HasMeasuredOwnerInputs X M ownerInputs) (gateWidth : gate.created.val=base)
    (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c) (w : (P).Slot c)
    (stop : ((P).child c w).edges≤(SP).cutoff) (positive : 0<((P).child c w).edges)
    (shared : ℕ) (fits : rate≤uniformWidth s C) (pageBound high fixed addr seed owner : ℕ)
    (pageFit : ExactPageFit (shadow (withPaidOwnerLeaves X M basePos ord ownerInputs) F E B0 own) pageBound)
    (hi : ∀ {x : Call (PhysicalHost f ell)}
      (j : Path sel (exteriorChild G ell X.centre X.sample X.group) x) (a : (SP).cutoff<x.edges),
      x.prec+(liveActiveAt (withPaidOwnerLeaves X M basePos ord ownerInputs) F E B0 own j a).result.extraPrecision≤high)
    (sizes : EntryWidths (shadow (withPaidOwnerLeaves X M basePos ord ownerInputs) F E B0 own) fixed addr)
    (bootWidth : BootBodyWidth (shadow (withPaidOwnerLeaves X M basePos ord ownerInputs) F E B0 own) seed)
    (owners : OwnerWidth (shadow (withPaidOwnerLeaves X M basePos ord ownerInputs) F E B0 own) owner) :
    let r := exteriorChild G ell X.centre X.sample X.group
    let R := withPaidOwnerLeaves X M basePos ord ownerInputs
    let Q := shadow R F E B0 own
    let Y := sourceState M p w
    let path := Path.step p w
    let B := stackBank (borns M) B0 path
    let frame := T.frame path.reached
    let baseRoof := recursiveResidentRoof shared B0 r pageBound high fixed addr seed owner s C+
      pathLimit s C*(prec+max ew fixed+rate)+
      pathLimit s C*suspendedRosterCap s C (absolutePrecision s r.edges r.prec)
    ∃ (A : OwnerTerminalInput X p w Y) (older : List Cmd) (b k : ℕ),
      ObservedRosterPause Q retire B0 path b k ∧
      (ownerInputs p w Y stop).result=some A ∧
      (oldCompiler X p w Y A).result=some older ∧
      let clk := (visitFramesClock A.saved.rows).result
      let rows := older++(trueFreshPages Y).map (freshWord Y)
      let query := actualRowQuery X.hf frame T.vPositive B rows
      let exactRows := runRows X.hf frame T.vPositive B clk rows
      let work := executeOwnerTerminal X p w Y ⟨A,(ownerInputs p w Y stop).steps⟩ frame B
      let held := recursiveResidentBits shared R B0 path b+literalControlPath R F E B0 own path+k
      let ceiling := baseRoof+(encodedLeafInputs clk rows+
        leafAssignmentMax clk.length rows.length (ell*(frame.words.length*((P).child c w).prec)))
      clk.length=((P).child c w).edges ∧
      liveVisit R F E retire B0 own path=⟨(exactRows.result,B),work.steps+3⟩ ∧
      (∀ rev (lefts : List (Block frame ell)) (pre post : List Cmd) (cmd : Cmd),
        rows=pre++cmd::post → ClockCut frame.hp query clk [] rev lefts →
        ReadFormat B clk.length cmd ∧
          held+(encodedLeafInputs clk rows+liveReadRegisters X.hf frame T.vPositive B pre cmd rev lefts)≤ceiling) ∧
      (∀ rev (lefts : List (Block frame ell)),ClockCut frame.hp query clk [] rev lefts → ∀ i,
        held+(encodedLeafInputs clk rows+liveReverseRegisters rev lefts i)≤ceiling) ∧
      (∀ tail rev (lefts : List (Block frame ell)),ClockCut frame.hp query clk (()::tail) rev lefts →
        held+(encodedLeafInputs clk rows+liveAddRegisters frame.hp query tail rev lefts)≤ceiling) := by
  let R := withPaidOwnerLeaves X M basePos ord ownerInputs
  let path := Path.step p w
  let Y := sourceState M p w
  let B := stackBank (borns M) B0 path
  let frame := T.frame path.reached
  have kept : ReadyOnStack (borns R) B0 := by
    have same : ReadyOnStack (borns R) B0=ReadyOnStack (borns M) B0 :=
      congrArg (fun BB : Births T key prec tw bw Pg=>ReadyOnStack BB B0)
        (paid_owner_leaf_keeps_births X M basePos ord ownerInputs)
    exact @Eq.mpr (ReadyOnStack (borns R) B0) (ReadyOnStack (borns M) B0)
      same (fun {_} j u=>valid j u)
  obtain ⟨A,older,got,compiled,len,fmt,visit⟩ :=
    actual_r66_positive_owner_visit_uses_real_clock_and_formatted_commands X M basePos ord
      ownerInputs gate boot F E retire B0 own rootLive valid supply gateWidth p w stop positive
  obtain ⟨_,_,b,k,observed,_,preserved,_⟩ :=
    real_r66_child_publication_and_native_tape_selected_peak R F E B0 own retire shared fits
      pageBound high fixed addr seed owner pageFit hi sizes bootWidth owners kept p w
  let clk := (visitFramesClock A.saved.rows).result
  let rows := older++(trueFreshPages Y).map (freshWord Y)
  refine ⟨A,older,b,k,observed,got,compiled,len,visit,?_,?_,?_⟩
  · intro rev lefts pre post cmd split cut
    obtain ⟨_,formatted,read⟩ := measured_read_phase_uses_actual_clock_and_entry
      X.hf frame T.vPositive B clk rows pre post cmd split fmt rev lefts cut
    exact ⟨formatted,Nat.add_le_add preserved read⟩
  · intro rev lefts cut i
    have reversing := measured_reverse_phase_retains_only_these_named_views
      X.hf frame T.vPositive B clk rows rev lefts cut i
    exact Nat.add_le_add preserved reversing
  · intro tail rev lefts cut
    have add := measured_add_phase_has_one_actual_pair_and_result
      X.hf frame T.vPositive B clk tail rows rev lefts cut
    exact Nat.add_le_add preserved add

#print axioms same_r66_positive_owner_leaf_has_paused_and_local_named_peak
end
end J6R68.LeafPeak