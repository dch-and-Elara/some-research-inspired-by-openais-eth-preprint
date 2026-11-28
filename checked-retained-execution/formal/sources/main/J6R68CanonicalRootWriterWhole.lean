import J6R68CanonicalRootWriterOwners

/-! On the actual exterior stop, compile the complete paid owner
roster and evaluate it with one paid physical edge book. Proof-side
orders are used only to certify that the produced list is complete.
The old canonical typed tape is compared by its decoded value. -/
namespace J6R68CanonicalRootWriter
open scoped Polynomial Classical
open Polynomial AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost J6R21Ancestor
open J6R26DescriptorTree J6R35RootOrigins J6R36ChildFramedRoute
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R34RootAtlas J6R41StructuredAllPaths
open J6Mesh J6OrientedHost J6R24LegalLayout J6R10Repack J6R12Blueprint
open J6R12Repack J6ActiveRun J6ActiveSchedule J6R32StatefulArithmetic
open J6R32ChildResidentTransfer J6R27OriginalGate J6R33StatefulArithmeticPage
open J6R37StructuredRoot J6R30GeneratedRootLayout J6R25PreparedSupply
open J6R55BootBodies J6R48RawRoute J6R50SourceProducer J6R54ExteriorOwner
open J6R53OldOwner J6R62Leaf J6R50Leaf J6R52Terminal J6R53TerminalGate
open J6R67CanonicalStop J6R11Blueprint J6R49Leaf J6R51Leaf J6R34ChildPath J6R21Leaf
open J6R54TerminalBoot J6R24MeteredRecursion J6R48Leaf J6R53OldOwnerRoot

set_option quotPrecheck false
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 19000000
set_option maxRecDepth 5400
set_option Elab.async false

theorem write_list_on_literal_roster {A S D : Type} (xs : List A) (row : A→S)
    (draw : S→Meter (Option D)) (expected : A→D) (correct : ∀ v,(draw (row v)).result=some (expected v)) :
    (gatherOptions 1 draw (xs.map row)).result=some (xs.map expected) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,gatherOptions,correct x,Option.bind_some,ih,Option.map_some]

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co d edgew tc tj key prec tw bw own : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "U" => (Vertex (exteriorChild G ell X.centre X.sample X.group))
local notation "N" => (exteriorChild G ell X.centre X.sample X.group).edges
local notation "Pg" => (pageKeyWidth m+pad)
local notation "RAW" => (RawRoster own (SuffixWordWidth m) key prec Pg)
local notation "FR" => (FramedEdge (rootHalfWidth m) own key prec Pg)

def paidOwnerRosterRaw (name : U→Word own)
    (owners : Meter (ExteriorRoster X gate pad name)) : Meter RAW :=
  ⟨owners.result.raw,owners.steps⟩

theorem all_actual_root_commands_are_generated (name : U→Word own)
    (injective : Function.Injective name) (gateWidth : gate.created.val=base)
    (edgeCount : (Ext).host.edgeCount=N) (b : ℕ) (hb : 0<b) (fit : N≤2^b)
    (owners : ExteriorRoster X gate pad name) :
    let fs := trueFrames X gate pad name
    let bk := frameKeys fs
    let cmds := owners.order.map (expectedRootCommand X pad edgeCount b fit)
    (writeRootRows b bk.result fs owners.raw).result=some cmds ∧
      cmds.length=Nat.card U := by
  let fs := trueFrames X gate pad name
  let bk := frameKeys fs
  constructor
  · change (writeRootRows b bk.result fs owners.raw).result=_
    unfold writeRootRows
    rw [owners.exactRows]
    exact write_list_on_literal_roster owners.order
      (fun v=>⟨name v,exteriorData X gate pad v⟩)
      (writeRootOwner b bk.result fs) (expectedRootCommand X pad edgeCount b fit)
      (actual_raw_owner_writes_the_expected_command X gate pad name injective gateWidth edgeCount b hb fit)
  · dsimp only
    rw [List.length_map]
    exact actual_complete_order_length owners.order owners.unique owners.complete

theorem raw_root_writer_returns_the_canonical_root_value
    (basePos : 0<base) (name : U→Word own) (injective : Function.Injective name)
    (gateWidth : gate.created.val=base) (edgeCount : (Ext).host.edgeCount=N)
    (b : ℕ) (hb : 0<b) (fit : N≤2^b)
    (incident : PaidIncidentNames X name) (lanes : BootLaneTape X gate pad)
    (owners : Meter (ExteriorRoster X gate pad name)) (F : Frame f (Ext).prec)
    (B : PageBank f ell key prec tw bw Pg) (live : IsLive (X.seed pad) B) :
    let setup := prepareRootBook X gate pad name incident lanes
    let fs := trueFrames X gate pad name
    let bk := frameKeys fs
    let ord := exteriorOrdinal X edgeCount
    let cmds := owners.result.order.map (expectedRootCommand X pad edgeCount b fit)
    let work := runRootWriter b X.hf F X.positive B setup (paidOwnerRosterRaw X gate pad name owners)
    ∃ word,work.result=some word ∧
      F.decode word=F.decode (runTape (rootTape X pad basePos F ord edgeCount) X.hf F X.positive B).result ∧
      cmds.length=Nat.card U ∧
      work.steps=setup.steps+owners.steps+
        (3+(owners.result.raw.map (fun u=>(writeRootOwner b bk.result fs u).steps+7)).sum)+
        (4*N+2)+(runRows X.hf F X.positive B (visitFramesClock fs).result cmds).steps+9 := by
  let fs := trueFrames X gate pad name
  let bk := frameKeys fs
  let ord := exteriorOrdinal X edgeCount
  let cmds := owners.result.order.map (expectedRootCommand X pad edgeCount b fit)
  let setup := prepareRootBook X gate pad name incident lanes
  let raw := paidOwnerRosterRaw X gate pad name owners
  let clock := visitFramesClock fs
  let work := runRootWriter b X.hf F X.positive B setup raw
  have setupVal : setup.result=some (fs,bk.result) := by
    unfold setup bk
    rw [prepare_root_book_is_literal_and_paid X gate pad name incident lanes edgeCount,
      actual_root_edge_book X gate pad name edgeCount]
  have written := all_actual_root_commands_are_generated X gate pad name injective gateWidth edgeCount b hb fit owners.result
  have joined := root_writer_uses_one_chart_and_exact_meter b X.hf F X.positive B
    setup raw fs bk.result setupVal cmds written.1
  have fsLength : fs.length=N := by
    unfold fs trueFrames
    rw [List.length_map,ordered_exterior_exact_length X edgeCount]
  have cWidth : clock.result.length=N := by
    unfold clock
    rw [frame_clock_exact,List.length_replicate,fsLength]
  have cFee : clock.steps=4*N+2 := by
    unfold clock
    rw [frame_clock_exact,fsLength]
  have physical :=
    exact_raw_terminal_physical_order X.hf F X.positive B ord clock.result cWidth owners.result.order
      owners.result.unique owners.result.complete (expectedRootCommand X pad edgeCount b fit)
      (actual_compiled_root_row_has_canonical_semantics X gate pad basePos name gateWidth
        edgeCount b fit F B live)
  have old := actual_root_tape_value X pad basePos F ord edgeCount B live
  refine ⟨(runRows X.hf F X.positive B clock.result cmds).result,
    congrArg Meter.result joined,physical.trans old.symm,written.2,?_⟩
  change work.steps=_
  rw [show work=_ from joined]
  dsimp only [raw,paidOwnerRosterRaw]
  rw [cFee]

theorem real_mounted_owner_roster_drives_the_root_stop {rootOwn : ℕ}
    {rootName : SourceVertex P→Word rootOwn}
    (basePos : 0<base) (name : U→Word own)
    (injective : Function.Injective name) (sourceInjective : Function.Injective rootName)
    (gateWidth : gate.created.val=base) (edgeCount : (Ext).host.edgeCount=N)
    (b : ℕ) (hb : 0<b) (fit : N≤2^b)
    (incident : PaidIncidentNames X name) (lanes : BootLaneTape X gate pad)
    (source : RootRoster (P:=P) gate pad rootName)
    (names : KeyInputs X gate pad source name)
    (F : Frame f (Ext).prec) (B : PageBank f ell key prec tw bw Pg) (live : IsLive (X.seed pad) B) :
    let owners := mountFirstOwners X gate pad source B live names sourceInjective
    let setup := prepareRootBook X gate pad name incident lanes
    let out := runRootWriter b X.hf F X.positive B setup (paidOwnerRosterRaw X gate pad name owners)
    ∃ word,out.result=some word ∧ F.decode word=J6R9Recursive.reduce (Ext).prec f ell ((Ext).host.contract X.hf) := by
  let owners := mountFirstOwners X gate pad source B live names sourceInjective
  obtain ⟨ans,success,meaning,_,_⟩ :=
    raw_root_writer_returns_the_canonical_root_value X gate pad basePos name injective
      gateWidth edgeCount b hb fit incident lanes owners F B live
  refine ⟨ans,success,meaning.trans ?_⟩
  exact actual_root_tape_value X pad basePos F (exteriorOrdinal X edgeCount) edgeCount B live


#print axioms real_mounted_owner_roster_drives_the_root_stop
#print axioms write_list_on_literal_roster
#print axioms all_actual_root_commands_are_generated
#print axioms raw_root_writer_returns_the_canonical_root_value
end
end J6R68CanonicalRootWriter

