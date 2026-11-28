import J6R75RawPeakStop
import J6R75RawPeakPositive
import J6R75RawPeakTerminalClock

/-! The three actual stop branches and their real emitted command
cuts, while a supplied already observed ancestor charge stays resident. -/
namespace J6R75RawPeak
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
open J6R64Active J6R66Active J6R30ProducedGateRegistry J6R68.RecursivePeak J6R68.LeafPeak J6R68ActiveInputs.Sweep
open J6R68.LeafPeak.Packet J6R21Ancestor J6R50Leaf J6R62Leaf J6R18ChildWrite
open J6R52Peak J6R54PeakInput J6R51Peak J6R57ScopeFee J6R66.BootPeak
open J6R35RootOrigins J6R34ChildPath J6R50Peak J6R30ProducedGateRegistry
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

local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "Here" => (Path.root : Path sel Ext Ext)
local notation "Mach" => (OnlineMachine T key prec tw bw Pg rate)

def SameRawOriginalRootStop
    (M : Mach) (basePos : 0<base) (ord : Fin (Ext).edges≃(Ext).host.Edge)
    (ownerInputs : OwnerInputProvider (T:=T) (pad:=pad) X)
    (F : RetainedAfter T key prec tw bw Pg rate cw) (chart : MountedChart T)
    (layout : ExteriorLayout (T:=T) (page:=Pg) (cw:=cw) X)
    {width : ℕ} (tails : SavedDirectoryTails width)
    (B0 : Bank) (own : OwnsHeader X.header.result B0) (shared : ℕ) : Prop :=
  let R := withPaidOwnerLeaves X M basePos ord ownerInputs
  let d := sourceLeafTape X pad (machineInputs X pad M) basePos Here ord
  let frame := T.frame (Here).reached
  let rows := rawLeafCommands d
  let resident := recursiveResidentBits shared R B0 Here 0
  let out := runRows X.hf frame T.vPositive B0 d.clock rows
  runRawPhysicalExterior X R F chart layout (retireSavedDirectory tails) B0 own=⟨(out.result,B0),out.steps⟩ ∧
  SelectedStopClockCuts X.hf frame T.vPositive B0 d.clock rows resident resident

theorem same_physical_raw_root_stop_has_all_named_clock_cuts
    (M : Mach) (basePos : 0<base) (ord : Fin (Ext).edges≃(Ext).host.Edge)
    (ownerInputs : OwnerInputProvider (T:=T) (pad:=pad) X)
    (F : RetainedAfter T key prec tw bw Pg rate cw) (chart : MountedChart T)
    (layout : ExteriorLayout (T:=T) (page:=Pg) (cw:=cw) X)
    {width : ℕ} (tails : SavedDirectoryTails width)
    (B0 : Bank) (own : OwnsHeader X.header.result B0) (live : IsLive (X.seed pad) B0)
    (stop : (Ext).edges≤(SP).cutoff) (shared : ℕ) :
    SameRawOriginalRootStop X M basePos ord ownerInputs F chart layout tails B0 own shared := by
  obtain ⟨ran,cuts,_⟩ := stopped_raw_exterior_uses_its_original_clock_and_regions
    X M basePos ord ownerInputs F chart layout tails B0 own live stop shared
  exact ⟨ran,actual_paid_clock_has_all_its_selected_stop_cuts _ _ _ _ _ _ _ _ le_rfl cuts.1⟩

def SameRawOriginalZeroStop
    (M : Mach) (basePos : 0<base) (ord : Fin (Ext).edges≃(Ext).host.Edge)
    (ownerInputs : OwnerInputProvider (T:=T) (pad:=pad) X)
    (F : RetainedAfter T key prec tw bw Pg rate cw) (chart : MountedChart T)
    {width : ℕ} (tails : SavedDirectoryTails width) (B0 : Bank)
    (p : Path sel Ext c) (w : (P).Slot c) (resident roof : ℕ) : Prop :=
  let R := withPaidOwnerLeaves X M basePos ord ownerInputs
  let entered := sourceEntered R B0 p w
  let path := Path.step p w
  let ordHere := actualEdgeOrder T (p.ticket w) entered.site.birth.native.physical
  let d := sourceLeafTape X pad (machineInputs X pad M) basePos path ordHere
  let frame := T.frame path.reached
  let rows := rawLeafCommands d
  let out := runRows X.hf frame T.vPositive entered.bank d.clock rows
  d.clock=[] ∧
  runRawAfter R F chart (retireSavedDirectory tails) c p w entered.site entered.resident entered.bank entered.owner=
    ⟨(out.result,entered.bank),(storedBook entered.site).steps+out.steps+3⟩ ∧
  SelectedStopClockCuts X.hf frame T.vPositive entered.bank d.clock rows resident roof

theorem same_raw_zero_stop_has_all_named_clock_cuts
    (M : Mach) (basePos : 0<base) (ord : Fin (Ext).edges≃(Ext).host.Edge)
    (ownerInputs : OwnerInputProvider (T:=T) (pad:=pad) X)
    (F : RetainedAfter T key prec tw bw Pg rate cw) (chart : MountedChart T)
    {width : ℕ} (tails : SavedDirectoryTails width) (B0 : Bank)
    (live : IsLive (X.seed pad) B0) (valid : ReadyOnStack (borns M) B0)
    (p : Path sel Ext c) (w : (P).Slot c)
    (stop : ((P).child c w).edges≤(SP).cutoff) (zero : ((P).child c w).edges=0)
    (resident roof : ℕ) (fit : resident≤roof) :
    SameRawOriginalZeroStop X M basePos ord ownerInputs F chart tails B0 p w resident roof := by
  let R := withPaidOwnerLeaves X M basePos ord ownerInputs
  let entered := sourceEntered R B0 p w
  let path := Path.step p w
  let ordHere := actualEdgeOrder T (p.ticket w) entered.site.birth.native.physical
  let d := sourceLeafTape X pad (machineInputs X pad M) basePos path ordHere
  let frame := T.frame path.reached
  have bankEq : entered.bank=stackBank (borns M) B0 path := by
    change stackBank (borns R) B0 path=_
    rw [paid_owner_leaf_keeps_births X M basePos ord ownerInputs]
  have alive : opened (borns M) (IsLive (X.seed pad)) path entered.bank := by
    rw [bankEq]
    exact stack_is_opened (borns M) B0 (IsLive (X.seed pad)) (live_monotone (X.seed pad)) live valid path
  have format : HasResidentFormat d entered.bank :=
    compiled_leaf_format (planEdges (T:=T) path)
      (sourceLeafRow X pad (machineInputs X pad M) basePos path ordHere) entered.bank alive
  have exec := (true_raw_terminal_tape_has_selected_clock_cuts X.hf frame T.vPositive entered.bank d
    format resident roof fit).1
  refine ⟨List.length_eq_zero_iff.mp (d.clockExact.trans zero),?_,
    actual_paid_clock_has_all_its_selected_stop_cuts X.hf frame T.vPositive entered.bank d.clock
      (rawLeafCommands d) resident roof fit (actual_raw_leaf_command_formats d entered.bank format)⟩
  rw [stopped_raw_after_uses_original_leaf R F chart (retireSavedDirectory tails)
    p w entered.site entered.resident entered.bank entered.owner stop]
  simp only [R,withPaidOwnerLeaves,if_pos zero]
  change (⟨((runTape d X.hf frame T.vPositive entered.bank).result,entered.bank),
    (storedBook entered.site).steps+(runTape d X.hf frame T.vPositive entered.bank).steps+3⟩ : Meter _)=_
  rw [exec]
  rfl

def SameRawOriginalPositiveStop
    (M : Mach) (basePos : 0<base) (ord : Fin (Ext).edges≃(Ext).host.Edge)
    (ownerInputs : OwnerInputProvider (T:=T) (pad:=pad) X)
    (F : RetainedAfter T key prec tw bw Pg rate cw) (chart : MountedChart T)
    {width : ℕ} (tails : SavedDirectoryTails width) (B0 : Bank)
    (p : Path sel Ext c) (w : (P).Slot c)
    (stop : ((P).child c w).edges≤(SP).cutoff) (resident roof : ℕ) : Prop :=
  let R := withPaidOwnerLeaves X M basePos ord ownerInputs
  let entered := sourceEntered R B0 p w
  let Y := sourceState M p w
  let path := Path.step p w
  let B := stackBank (borns M) B0 path
  let frame := T.frame path.reached
  ∃ (A : OwnerTerminalInput X p w Y) (older : List Cmd),
    (ownerInputs p w Y stop).result=some A ∧ (oldCompiler X p w Y A).result=some older ∧
    let clk := (visitFramesClock A.saved.rows).result
    let rows := older++(trueFreshPages Y).map (freshWord Y)
    let exactRows := runRows X.hf frame T.vPositive B clk rows
    let work := executeOwnerTerminal X p w Y ⟨A,(ownerInputs p w Y stop).steps⟩ frame B
    runRawAfter R F chart (retireSavedDirectory tails) c p w entered.site entered.resident entered.bank entered.owner=
      ⟨(exactRows.result,B),work.steps+3⟩ ∧
    SelectedStopClockCuts X.hf frame T.vPositive B clk rows resident roof

theorem same_raw_positive_stop_has_all_named_clock_cuts
    (M : Mach) (basePos : 0<base) (ord : Fin (Ext).edges≃(Ext).host.Edge)
    (ownerInputs : OwnerInputProvider (T:=T) (pad:=pad) X)
    (gate : Stamp key prec) (boot : ExactPrintedBoot X M gate)
    (F : RetainedAfter T key prec tw bw Pg rate cw) (E : RootInputs T key prec tw bw Pg cw ew)
    (chart : MountedChart T) {width : ℕ} (tails : SavedDirectoryTails width) (B0 : Bank)
    (own : OwnsHeader E.header B0) (live : IsLive (X.seed pad) B0) (valid : ReadyOnStack (borns M) B0)
    (supply : HasMeasuredOwnerInputs X M ownerInputs) (gateWidth : gate.created.val=base)
    (p : Path sel Ext c) (w : (P).Slot c)
    (stop : ((P).child c w).edges≤(SP).cutoff) (positive : 0<((P).child c w).edges)
    (resident roof : ℕ) (fit : resident≤roof) :
    SameRawOriginalPositiveStop X M basePos ord ownerInputs F chart tails B0 p w stop resident roof := by
  let Y := sourceState M p w
  let frame := T.frame (Path.step p w).reached
  let B := stackBank (borns M) B0 (.step p w)
  obtain ⟨A,older,got,compiled,_,formats,ran⟩ :=
    actual_raw_positive_stop_uses_that_same_paid_owner_clock_and_bank X M basePos ord ownerInputs gate boot
      F E chart (retireSavedDirectory tails) B0 own live valid supply gateWidth p w stop positive
  refine ⟨A,older,got,compiled,ran,?_⟩
  exact actual_paid_clock_has_all_its_selected_stop_cuts X.hf frame T.vPositive B
    (visitFramesClock A.saved.rows).result (older++(trueFreshPages Y).map (freshWord Y)) resident roof fit formats

#print axioms same_physical_raw_root_stop_has_all_named_clock_cuts
#print axioms same_raw_zero_stop_has_all_named_clock_cuts
#print axioms same_raw_positive_stop_has_all_named_clock_cuts
end
end J6R75RawPeak
