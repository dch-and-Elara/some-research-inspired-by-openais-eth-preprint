import J6R75RawPeakJetFold
import J6R75RawPeakPacketRegions
import J6R68ActiveInputsSweepRun
import J6R57PublicNoChartOnline

/-! Attach the actual paid positive owner terminal (not an arbitrary
leafAfter) to the very R66 entered occurrence. Finite command
production and format refer to the same StoredSite and live bank. -/
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

private theorem original_tape_stop_with_packets
    {j : Call (PhysicalHost f ell)} (bank : Bank)
    (d : RawTape j key Pg) (frame : Frame f j.prec)
    (format : HasResidentFormat d bank) (resident roof : ℕ) (fit : resident≤roof) :
    let rows := rawLeafCommands d
    runTape d X.hf frame T.vPositive bank=runRows X.hf frame T.vPositive bank d.clock rows ∧
    SelectedTerminalCuts X.hf frame T.vPositive bank d resident roof ∧
    (∀ (pre post : List Cmd) (id : J6R15ModeCost.Word key) (pg : J6R15ModeCost.Word Pg)
      (u : ℕ) (wires : List WireRead) (rev : List Bool) (left : List (Block frame ell)),
      rows=pre++(.packet id pg u wires)::post →
      ClockCut frame.hp (actualRowQuery X.hf frame T.vPositive bank rows) d.clock [] rev left →
      SamePacketRegionCuts X.hf frame T.vPositive bank d.clock rows pre post id pg u wires rev left resident roof) := by
  obtain ⟨out,cuts⟩ := true_raw_terminal_tape_has_selected_clock_cuts X.hf frame T.vPositive bank
    d format resident roof fit
  refine ⟨out,cuts,?_⟩
  intro pre post id pg depth wires rev left order clock
  exact actual_formatted_packet_keeps_setup_dfs_resize_with_one_regional_roof
    X.hf frame T.vPositive bank d.clock (rawLeafCommands d) pre post id pg depth wires
    order (actual_raw_leaf_command_formats d bank format) rev left clock resident roof fit

theorem stopped_raw_exterior_uses_its_original_clock_and_regions
    (M : Mach) (basePos : 0<base) (ord : Fin (Ext).edges≃(Ext).host.Edge)
    (ownerInputs : OwnerInputProvider (T:=T) (pad:=pad) X)
    (F : RetainedAfter T key prec tw bw Pg rate cw) (chart : MountedChart T)
    (layout : ExteriorLayout (T:=T) (page:=Pg) (cw:=cw) X)
    {width : ℕ} (tails : SavedDirectoryTails width)
    (B0 : Bank) (own : OwnsHeader X.header.result B0) (live : IsLive (X.seed pad) B0)
    (stop : (Ext).edges≤(SP).cutoff) (shared : ℕ) :
    let R := withPaidOwnerLeaves X M basePos ord ownerInputs
    let d := sourceLeafTape X pad (machineInputs X pad M) basePos Here ord
    let frame := T.frame (Here).reached
    let rows := rawLeafCommands d
    let resident := recursiveResidentBits shared R B0 Here 0
    let out := runRows X.hf frame T.vPositive B0 d.clock rows
    runRawPhysicalExterior X R F chart layout (retireSavedDirectory tails) B0 own=⟨(out.result,B0),out.steps⟩ ∧
    SelectedTerminalCuts X.hf frame T.vPositive B0 d resident resident ∧
    (∀ (pre post : List Cmd) (id : J6R15ModeCost.Word key) (pg : J6R15ModeCost.Word Pg)
      (u : ℕ) (wires : List WireRead) (rev : List Bool) (left : List (Block frame ell)),
      rows=pre++(.packet id pg u wires)::post →
      ClockCut frame.hp (actualRowQuery X.hf frame T.vPositive B0 rows) d.clock [] rev left →
      SamePacketRegionCuts X.hf frame T.vPositive B0 d.clock rows pre post id pg u wires rev left resident resident) := by
  let R := withPaidOwnerLeaves X M basePos ord ownerInputs
  let d := sourceLeafTape X pad (machineInputs X pad M) basePos Here ord
  let frame := T.frame (Here).reached
  let resident := recursiveResidentBits shared R B0 Here 0
  have format : HasResidentFormat d B0 :=
    compiled_leaf_format (planEdges (T:=T) Here)
      (sourceLeafRow X pad (machineInputs X pad M) basePos Here ord) B0 live
  obtain ⟨exec,cuts,packet⟩ := original_tape_stop_with_packets X (T:=T) B0 d frame format resident resident le_rfl
  refine ⟨?_,cuts,packet⟩
  rw [runRawPhysicalExterior,runRawRoot,dif_pos stop]
  change (⟨((runTape d X.hf frame T.vPositive B0).result,B0),
      (runTape d X.hf frame T.vPositive B0).steps⟩ : Meter _) = _
  rw [exec]

theorem real_raw_zero_stop_keeps_its_original_clock_and_augmented_ancestors
    (M : Mach) (basePos : 0<base) (ord : Fin (Ext).edges≃(Ext).host.Edge)
    (ownerInputs : OwnerInputProvider (T:=T) (pad:=pad) X)
    (F : RetainedAfter T key prec tw bw Pg rate cw) (chart : MountedChart T)
    (E : RootInputs T key prec tw bw Pg cw ew) {width : ℕ} (tails : SavedDirectoryTails width)
    (B0 : Bank) (own : OwnsHeader E.header B0) (live : IsLive (X.seed pad) B0)
    (valid : ReadyOnStack (borns M) B0)
    (p : Path sel Ext c) (w : (P).Slot c)
    (stop : ((P).child c w).edges≤(SP).cutoff) (zero : ((P).child c w).edges=0)
    (shared pageBound fixed addr seed owner carry : ℕ)
    (pageFit : ExactPageFit (withPaidOwnerLeaves X M basePos ord ownerInputs) pageBound)
    (sizes : EntryWidths (withPaidOwnerLeaves X M basePos ord ownerInputs) fixed addr)
    (bootFit : BootBodyWidth (withPaidOwnerLeaves X M basePos ord ownerInputs) seed)
    (owners : OwnerWidth (withPaidOwnerLeaves X M basePos ord ownerInputs) owner)
    (anc : ActualRawAncestorStack (withPaidOwnerLeaves X M basePos ord ownerInputs)
      F chart E B0 own tails (.step p w) carry) :
    let R := withPaidOwnerLeaves X M basePos ord ownerInputs
    let entered := sourceEntered R B0 p w
    let path := Path.step p w
    let ordHere := actualEdgeOrder T (p.ticket w) entered.site.birth.native.physical
    let d := sourceLeafTape X pad (machineInputs X pad M) basePos path ordHere
    let frame := T.frame path.reached
    let rows := rawLeafCommands d
    let out := runRows X.hf frame T.vPositive entered.bank d.clock rows
    let jetRoom := pathLimit s C*rawAncestorJetRoof s C ell f.natDegree (absolutePrecision s (Ext).edges (Ext).prec)
    let roof := rawCarrierRoof shared B0 Ext pageBound fixed addr seed owner s C rate+jetRoom
    ∃ extra,ActualRawJetSupplement R F chart E B0 own tails path carry extra ∧
      let resident := recursiveResidentBits shared R B0 path carry+extra
      d.clock=[] ∧
      runRawAfter R F chart (retireSavedDirectory tails) c p w entered.site entered.resident entered.bank entered.owner=
        ⟨(out.result,entered.bank),(storedBook entered.site).steps+out.steps+3⟩ ∧
      SelectedTerminalCuts X.hf frame T.vPositive entered.bank d resident roof ∧
      (∀ (pre post : List Cmd) (id : J6R15ModeCost.Word key) (pg : J6R15ModeCost.Word Pg)
        (u : ℕ) (wires : List WireRead) (rev : List Bool) (left : List (Block frame ell)),
        rows=pre++(.packet id pg u wires)::post →
        ClockCut frame.hp (actualRowQuery X.hf frame T.vPositive entered.bank rows) d.clock [] rev left →
        SamePacketRegionCuts X.hf frame T.vPositive entered.bank d.clock rows pre post id pg u wires rev left resident roof) := by
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
  have cap := raw_ancestor_and_same_physical_carrier_fit_together R F chart E B0 own tails shared
    pageBound fixed addr seed owner pageFit sizes bootFit owners path carry anc
  obtain ⟨extra,jets,jcap⟩ := existing_raw_stack_carries_its_same_suspended_half_jets R F chart E B0 own tails path carry anc
  obtain ⟨exec,cuts,packet⟩ := original_tape_stop_with_packets X (T:=T) entered.bank d frame format _ _
    (Nat.add_le_add cap jcap)
  refine ⟨extra,jets,List.length_eq_zero_iff.mp (d.clockExact.trans zero),?_,cuts,packet⟩
  rw [stopped_raw_after_uses_original_leaf R F chart (retireSavedDirectory tails)
    p w entered.site entered.resident entered.bank entered.owner stop]
  simp only [R,withPaidOwnerLeaves,if_pos zero]
  change (⟨((runTape d X.hf frame T.vPositive entered.bank).result,entered.bank),
    (storedBook entered.site).steps+(runTape d X.hf frame T.vPositive entered.bank).steps+3⟩ : Meter _)=_
  rw [exec]
  rfl

#print axioms stopped_raw_exterior_uses_its_original_clock_and_regions
#print axioms real_raw_zero_stop_keeps_its_original_clock_and_augmented_ancestors
end
end J6R75RawPeak
