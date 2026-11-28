import J6R72SameRunLocalPeak
import J6R68LeafPeakOwner
import J6R68LeafPeakMaximum

/-! The positive literal owner terminal, one scaffolded actual R66
paused/entered path, and the maximum of its actual reading/summing
cuts. No equality to a replacement leaf interpreter is presumed. -/
namespace J6R72SameRunLocalPeak
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
open J6R57LiveSpace J6R51Peak J6R52Peak J6R50Peak J6ActiveSchedule J6R68.LeafPeak J6R57ScopeFee J6R68.RetireScratch
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

theorem existing_paused_positive_stop_bounds_real_leaf_and_return_by_a_max
    (M : OnlineMachine T key prec tw bw Pg rate)
    (basePos : 0<base)
    (ord : Fin (exteriorChild G ell X.centre X.sample X.group).edges ≃
      (exteriorChild G ell X.centre X.sample X.group).host.Edge)
    (ownerInputs : OwnerInputProvider (T:=T) (pad:=pad) X)
    (gate : Stamp key prec) (boot : ExactPrintedBoot X M gate)
    (F : RetainedAfter T key prec tw bw Pg rate cw) (E : RootInputs T key prec tw bw Pg cw ew)
    {width : ℕ} (tails : SavedDirectoryTails width) (B0 : Bank) (own : OwnsHeader E.header B0)
    (rootLive : IsLive (X.seed pad) B0) (valid : ReadyOnStack (borns M) B0)
    (supply : HasMeasuredOwnerInputs X M ownerInputs) (gateWidth : gate.created.val=base)
    (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c) (w : (P).Slot c)
    (stop : ((P).child c w).edges≤(SP).cutoff) (positive : 0<((P).child c w).edges)
    (shared buf roster roof : ℕ)
    (observed : ObservedRosterPause (shadow (withPaidOwnerLeaves X M basePos ord ownerInputs) F E B0 own)
      (retireSavedDirectory tails) B0 (.step p w) buf roster)
    (enter : recursiveResidentBits shared (withPaidOwnerLeaves X M basePos ord ownerInputs) B0 (.step p w) buf+
      literalControlPath (withPaidOwnerLeaves X M basePos ord ownerInputs) F E B0 own (.step p w)+roster≤roof) :
    let R := withPaidOwnerLeaves X M basePos ord ownerInputs
    let Y := sourceState M p w
    let path := Path.step p w
    let B := stackBank (borns M) B0 path
    let frame := T.frame path.reached
    let held := recursiveResidentBits shared R B0 path buf+literalControlPath R F E B0 own path+roster
    let returned := retireBits R F E B0 own p w shared buf roster ⟨tails,tails⟩
    ∃ (A : OwnerTerminalInput X p w Y) (older : List Cmd),
      ObservedRosterPause (shadow R F E B0 own) (retireSavedDirectory tails) B0 path buf roster ∧
      (ownerInputs p w Y stop).result=some A ∧ (oldCompiler X p w Y A).result=some older ∧
      let clk := (visitFramesClock A.saved.rows).result
      let rows := older++(trueFreshPages Y).map (freshWord Y)
      let query := actualRowQuery X.hf frame T.vPositive B rows
      let exactRows := runRows X.hf frame T.vPositive B clk rows
      let work := executeOwnerTerminal X p w Y ⟨A,(ownerInputs p w Y stop).steps⟩ frame B
      let leafRoom := encodedLeafInputs clk rows+leafAssignmentMax clk.length rows.length
        (ell*(frame.words.length*((P).child c w).prec))
      let room := roof+max leafRoom (4*width)
      clk.length=((P).child c w).edges ∧
      liveVisit R F E (retireSavedDirectory tails) B0 own path=⟨(exactRows.result,B),work.steps+3⟩ ∧
      (∀ rev (lefts : List (Block frame ell)) (pre post : List Cmd) (cmd : Cmd),
        rows=pre++cmd::post → ClockCut frame.hp query clk [] rev lefts →
        ReadFormat B clk.length cmd ∧
          max (held+(encodedLeafInputs clk rows+liveReadRegisters X.hf frame T.vPositive B pre cmd rev lefts))
            returned≤room) ∧
      (∀ rev (lefts : List (Block frame ell)),ClockCut frame.hp query clk [] rev lefts → ∀ i,
        max (held+(encodedLeafInputs clk rows+liveReverseRegisters rev lefts i)) returned≤room) ∧
      (∀ tail rev (lefts : List (Block frame ell)),ClockCut frame.hp query clk (()::tail) rev lefts →
        max (held+(encodedLeafInputs clk rows+liveAddRegisters frame.hp query tail rev lefts)) returned≤room) := by
  let R := withPaidOwnerLeaves X M basePos ord ownerInputs
  let path := Path.step p w
  let Y := sourceState M p w
  let B := stackBank (borns M) B0 path
  let frame := T.frame path.reached
  obtain ⟨A,older,got,compiled,len,fmt,visit⟩ :=
    actual_r66_positive_owner_visit_uses_real_clock_and_formatted_commands X M basePos ord
      ownerInputs gate boot F E (retireSavedDirectory tails) B0 own rootLive valid supply gateWidth p w stop positive
  let clk := (visitFramesClock A.saved.rows).result
  let rows := older++(trueFreshPages Y).map (freshWord Y)
  let budget := encodedLeafInputs clk rows+leafAssignmentMax clk.length rows.length
    (ell*(frame.words.length*((P).child c w).prec))
  let room := roof+max budget (4*width)
  have returnBound : retireBits R F E B0 own p w shared buf roster
      (⟨tails,tails⟩ : TailCopyObservation width)≤room := by
    rw [return_cut_fits_existing_reserve_plus_two_pairs]
    exact Nat.add_le_add enter (Nat.le_max_right budget _)
  have combine {k : ℕ} (h : k≤budget) :
      recursiveResidentBits shared R B0 path buf+literalControlPath R F E B0 own path+roster+k≤room :=
    Nat.add_le_add enter (h.trans (Nat.le_max_left budget (4*width)))
  refine ⟨A,older,observed,got,compiled,len,visit,?_,?_,?_⟩
  · intro rev lefts pre post cmd split cut
    obtain ⟨_,formatted,read⟩ := measured_read_phase_uses_actual_clock_and_entry
      X.hf frame T.vPositive B clk rows pre post cmd split fmt rev lefts cut
    exact ⟨formatted,Nat.max_le.mpr ⟨combine read,returnBound⟩⟩
  · intro rev lefts cut i
    have reverseWork := measured_reverse_phase_retains_only_these_named_views
      X.hf frame T.vPositive B clk rows rev lefts cut i
    exact Nat.max_le.mpr ⟨combine reverseWork,returnBound⟩
  · intro tail rev lefts cut
    have add := measured_add_phase_has_one_actual_pair_and_result
      X.hf frame T.vPositive B clk tail rows rev lefts cut
    exact Nat.max_le.mpr ⟨combine add,returnBound⟩

#print axioms existing_paused_positive_stop_bounds_real_leaf_and_return_by_a_max
end
end J6R72SameRunLocalPeak
