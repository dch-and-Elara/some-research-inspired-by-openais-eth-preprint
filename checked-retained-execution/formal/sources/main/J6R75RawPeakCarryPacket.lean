import J6R75RawPeakCarry
import J6R75RawPeakPacket

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

theorem true_raw_positive_packet_named_setup_and_resize_keep_the_same_carry
    (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
    (basePos : 0<base)
    (ord : Fin (exteriorChild G ell X.centre X.sample X.group).edges ≃
      (exteriorChild G ell X.centre X.sample X.group).host.Edge)
    (ownerInputs : OwnerInputProvider (T:=T) (pad:=pad) X)
    (gate : Stamp key prec) (boot : ExactPrintedBoot X M gate)
    (F : RetainedAfter T key prec tw bw Pg rate cw) (E : RootInputs T key prec tw bw Pg cw ew)
    (chart : MountedChart T) {width : ℕ} (tails : SavedDirectoryTails width) (B0 : Bank) (own : OwnsHeader E.header B0)
    (rootLive : IsLive (X.seed pad) B0) (valid : ReadyOnStack (borns M) B0)
    (supply : HasMeasuredOwnerInputs X M ownerInputs) (gateWidth : gate.created.val=base)
    (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c) (w : (P).Slot c)
    (stop : ((P).child c w).edges≤(SP).cutoff) (positive : 0<((P).child c w).edges)
    (shared pageBound fixed addr seed owner carry : ℕ)
    (pageFit : ExactPageFit (withPaidOwnerLeaves X M basePos ord ownerInputs) pageBound)
    (sizes : EntryWidths (withPaidOwnerLeaves X M basePos ord ownerInputs) fixed addr)
    (bootFit : BootBodyWidth (withPaidOwnerLeaves X M basePos ord ownerInputs) seed)
    (owners : OwnerWidth (withPaidOwnerLeaves X M basePos ord ownerInputs) owner)
    (anc : ActualRawAncestorStack (withPaidOwnerLeaves X M basePos ord ownerInputs)
      F chart E B0 own tails (.step p w) carry) :
    let R := withPaidOwnerLeaves X M basePos ord ownerInputs
    let entered := sourceEntered R B0 p w
    let Y := sourceState M p w
    let path := Path.step p w
    let B := stackBank (borns M) B0 path
    let frame := T.frame path.reached
    let resident := recursiveResidentBits shared R B0 path carry
    let roof := rawCarrierRoof shared B0 (exteriorChild G ell X.centre X.sample X.group)
      pageBound fixed addr seed owner s C rate
    ∃ (A : OwnerTerminalInput X p w Y) (older : List Cmd),
      (ownerInputs p w Y stop).result=some A ∧
      (oldCompiler X p w Y A).result=some older ∧
      let clk := (visitFramesClock A.saved.rows).result
      let rows := older++(trueFreshPages Y).map (freshWord Y)
      let exactRows := runRows X.hf frame T.vPositive B clk rows
      let work := executeOwnerTerminal X p w Y ⟨A,(ownerInputs p w Y stop).steps⟩ frame B
      let leafRoom := encodedLeafInputs clk rows+
        leafAssignmentMax clk.length rows.length (ell*(frame.words.length*((P).child c w).prec))
      runRawAfter R F chart (retireSavedDirectory tails) c p w entered.site entered.resident entered.bank entered.owner=
        ⟨(exactRows.result,B),work.steps+3⟩ ∧
      (∀ (pre post : List Cmd) (id : J6R15ModeCost.Word key) (pg : J6R15ModeCost.Word Pg)
        (d : ℕ) (wires : List WireRead),
        rows=pre++(.packet id pg d wires)::post →
        ∀ (rev : List Bool) (lefts : List (Block frame ell)),
        ClockCut frame.hp (actualRowQuery X.hf frame T.vPositive B rows) clk [] rev lefts →
        ∃ Q : LivePageHit B id pg,
          let bits := (reverseTape rev []).result
          let held := resident+(encodedLeafInputs clk rows+
            pendingLeafWords X.hf frame T.vPositive B pre rev lefts)
          let current := (.packet id pg d wires : Cmd).read X.hf frame T.vPositive B bits
          let wf := ell*(frame.words.length*((P).child c w).prec)
          bits.length=clk.length ∧ current.result=(Q.delivered X.hf frame T.vPositive d wires bits).result ∧
          ∀ j k i,
            max (held+(Q.routeBits d wires bits+
              (tableBits ((Q.board T.vPositive d wires bits).result.take j)).length+
              ((Q.tests.result.take k).flatMap checkBits).length))
              (held+((leafPayload (Q.createdValue T.vPositive d wires bits).result).length+
                ((leafPayload (Q.delivered X.hf frame T.vPositive d wires bits).result).take i).length))≤
              roof+leafRoom+max (Q.routeRoom wires+Q.tableRoom) (Q.W+wf)) := by
  let R := withPaidOwnerLeaves X M basePos ord ownerInputs
  let path := Path.step p w
  let resident := recursiveResidentBits shared R B0 path carry
  have roof := raw_ancestor_and_same_physical_carrier_fit_together R F chart E B0 own tails
    shared pageBound fixed addr seed owner pageFit sizes bootFit owners path carry anc
  obtain ⟨A,older,got,compiled,ran,reads⟩ :=
    raw_positive_real_packet_setup_and_resize_at_actual_clock X M basePos ord ownerInputs gate boot
      F E chart (retireSavedDirectory tails) B0 own rootLive valid supply gateWidth p w stop positive resident
  refine ⟨A,older,got,compiled,ran,?_⟩
  intro pre post id pg d wires ordered rev lefts cut
  obtain ⟨Q,len,val,setup,resize⟩ := reads pre post id pg d wires ordered rev lefts cut
  refine ⟨Q,len,val,?_⟩
  intro j k i
  exact Nat.max_le.mpr ⟨(setup j k).trans
    (Nat.add_le_add (Nat.add_le_add_right roof _) (Nat.le_max_left _ _)),
    (resize i).trans (Nat.add_le_add (Nat.add_le_add_right roof _) (Nat.le_max_right _ _))⟩

#print axioms true_raw_positive_packet_named_setup_and_resize_keep_the_same_carry
end
end J6R75RawPeak
