import J6R68LeafPeakVisit
import J6R62LeafActual

/-! Attach the actual paid positive owner terminal (not an arbitrary
leafAfter) to the very R66 entered occurrence. Finite command
production and format refer to the same StoredSite and live bank. -/
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

theorem actual_r66_positive_owner_visit_uses_real_clock_and_formatted_commands
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
    (stop : ((P).child c w).edges≤(SP).cutoff) (positive : 0<((P).child c w).edges) :
    let R := withPaidOwnerLeaves X M basePos ord ownerInputs
    let Y := sourceState M p w
    let path := Path.step p w
    let B := stackBank (borns M) B0 path
    let frame := T.frame path.reached
    ∃ (A : OwnerTerminalInput X p w Y) (older : List Cmd),
      (ownerInputs p w Y stop).result=some A ∧
      (oldCompiler X p w Y A).result=some older ∧
      let clk := (visitFramesClock A.saved.rows).result
      let rows := older++(trueFreshPages Y).map (freshWord Y)
      let exactRows := runRows X.hf frame T.vPositive B clk rows
      let work := executeOwnerTerminal X p w Y ⟨A,(ownerInputs p w Y stop).steps⟩ frame B
      clk.length=((P).child c w).edges ∧
      (∀ row∈rows,ReadFormat B clk.length row) ∧
      liveVisit R F E retire B0 own path=⟨(exactRows.result,B),work.steps+3⟩ := by
  let R := withPaidOwnerLeaves X M basePos ord ownerInputs
  let Y := sourceState M p w
  let path := Path.step p w
  let B := stackBank (borns M) B0 path
  let frame := T.frame path.reached
  obtain ⟨A,older,got,compiled,_,_⟩ := mounted_positive_leaf_is_exact_and_has_source_sized_fee
    X p w M basePos ord ownerInputs gate boot B0 stop positive gateWidth rootLive valid supply
  let clk := (visitFramesClock A.saved.rows).result
  let rows := older++(trueFreshPages Y).map (freshWord Y)
  let run := runRows X.hf frame T.vPositive B clk rows
  let work := executeOwnerTerminal X p w Y ⟨A,(ownerInputs p w Y stop).steps⟩ frame B
  have clockWidth : clk.length=((P).child c w).edges := by
    unfold clk
    rw [frame_clock_exact]
    exact (List.length_replicate).trans (canonical_terminal_table_censuses X p w Y A).1
  have live : opened (borns M) (IsLive (X.seed pad)) path B :=
    stack_is_opened (borns M) B0 (IsLive (X.seed pad)) (live_monotone (X.seed pad)) rootLive valid path
  have rootHere := opened_keeps_root X pad (borns M) path B live
  have born : OnPath (borns M) Y.birth.job path := .youngest p w rfl
  have formatted (row : Cmd) (mem : row∈rows) : ReadFormat B clk.length row := by
    rw [clockWidth]
    rcases List.mem_append.mp mem with h|h
    · exact every_actual_retained_owner_command_is_formatted X M p w gate boot gateWidth A
        (IsLive (X.seed pad)) B rootHere live older compiled row h
    · exact actual_compiled_atlas_read_formats Y path (borns M) born (IsLive (X.seed pad))
        B live (p.ticket w).child.edges row h
  have reply : work.result=some run.result := by
    change (joinPaidTerminal Y A.saved (oldCompiler X p w Y A) frame B).result=_
    exact congrArg Meter.result
      (measured_joined_terminal_exact Y A.saved (oldCompiler X p w Y A) frame B older compiled)
  have bankExact : stackBank (borns R) B0 path=B :=
    congrArg (fun BB : Births T key prec tw bw Pg=>stackBank BB B0 path)
      (paid_owner_leaf_keeps_births X M basePos ord ownerInputs)
  refine ⟨A,older,got,compiled,clockWidth,formatted,?_⟩
  change liveVisit R F E retire B0 own path=_
  rw [actual_stopped_r66_visit_is_the_entered_leaf_meter R F E retire B0 own p w stop]
  change (⟨((readLeaf R B0 path stop).result,stackBank (borns R) B0 path),
    (readLeaf R B0 path stop).steps⟩ : Meter _) = _
  rw [bankExact,read_leaf_uses_positive_owner_runtime X p w M basePos ord ownerInputs B0 stop positive,
    accepted_owner_inputs_use_the_actual_reader X ownerInputs p w Y stop B A got run.result reply]
  rfl

#print axioms actual_r66_positive_owner_visit_uses_real_clock_and_formatted_commands
end
end J6R68.LeafPeak