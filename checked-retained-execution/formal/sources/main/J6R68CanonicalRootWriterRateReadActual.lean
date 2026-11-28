import J6R68CanonicalRootWriterRateGeometry
import J6R68CanonicalRootWriterRateReadRows
import J6R62LeafOldFormat

/-! No arbitrary decoder charge is used. Each owner is a literal
original Gate or one exact page in the already live outer packet bank.
The maximum below is a mathematical bound over recorded sizes only;
the running leaf does not compute this maximum or enumerate extra pages. -/
namespace J6R68CanonicalRootWriter
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R21Ancestor J6R21Leaf
open J6R26DescriptorTree J6R35RootOrigins J6R36ChildFramedRoute
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R34RootAtlas J6R41StructuredAllPaths
open J6Mesh J6OrientedHost J6R24LegalLayout J6R10Repack J6R12Blueprint
open J6ActiveRun J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R37StructuredRoot J6R30GeneratedRootLayout J6R27OriginalGate
open J6R55BootBodies J6R48RawRoute J6R50SourceProducer J6R54ExteriorOwner
open J6R53OldOwner J6R53OldOwnerRoot J6R50Leaf J6R62Leaf J6R48Leaf J6R52Terminal
open J6R67CanonicalStop J6R49SourceLayout J6R24MeteredRecursion J6R58BootScope

set_option quotPrecheck false
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 18500000
set_option maxRecDepth 5100
set_option Elab.async false

theorem original_read_code_uses_at_most_its_arity {r k d : ℕ}
    (fit : r≤ 2^k) (ports : Fin d→Fin r) (src : Gate d) :
    gatePorts (forgetGate (gateTape fit ports src))≤ d := by
  cases src <;> simp [gatePorts,forgetGate,gateTape]

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {plant : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) plant (constantRootWord m)}
variable {ell q ro co d edgew tc tj key prec tw bw own : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "E" => (exteriorChild G ell X.centre X.sample X.group).edges
local notation "U" => ((exteriorChild G ell X.centre X.sample X.group).host.Row ⊕
  (exteriorChild G ell X.centre X.sample X.group).host.Col)
local notation "Pg" => (pageKeyWidth m+pad)
local notation "Bank" => (PageBank f ell key prec tw bw Pg)

abbrev printedRootWires (edgeCount : (Ext).host.edgeCount=E) (k : CanonicalPage m) :
    List WireRead :=
  (orderedPagePorts X k).map
    (fun u=>⟨pageWireHeader X k u,List.replicate (pageWireOrdinal X edgeCount k u).val true⟩)

include gate pad in
theorem emitted_root_packet_has_real_wire_sizes
    (name : U→Word own) (edgeCount : (Ext).host.edgeCount=E) (k : CanonicalPage m) :
    let ws := printedRootWires X edgeCount k
    ws.length≤ E ∧ ∀ w∈ws,w.header.length≤ rootBodyWidth m ∧ w.lane.length≤ E := by
  constructor
  · unfold printedRootWires orderedPagePorts scanSubtype
    simp only [List.length_map]
    exact (List.length_filterMap_le _ _).trans_eq (ordered_exterior_exact_length X edgeCount)
  · intro w used
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp used
    have mem : exteriorFrameAt X gate pad name (edge u.val)∈trueFrames X gate pad name := by
      apply List.mem_map.mpr
      exact ⟨edge u.val,(reviewed_exterior_order X).2 _,rfl⟩
    have h := (physical_frames_use_printed_payload_widths X gate pad name _ mem).2
    have same := (emitted_packet_seed_is_same_frame X gate pad name k u).2
    change (pageWireHeader X k u).length≤ rootBodyWidth m ∧
      (List.replicate (pageWireOrdinal X edgeCount k u).val true).length≤ E
    exact ⟨(congrArg List.length same).symm.le.trans h,
      List.length_replicate.trans_le (pageWireOrdinal X edgeCount k u).isLt.le⟩

def physicalRootReadCap (B : Bank) (e p b D : ℕ) : ℕ :=
  max (originalGateFee E b (max D 2)+A1R11.uvWidth e ell p+4)
    ((Finset.univ : Finset (CanonicalPage m)).sup (fun k=>
      stoppedPacketLookupCap B (X.seed pad).immutable.payload (X.chosenFields k) p E (rootBodyWidth m)))

include gate in
theorem each_actual_root_command_reads_with_size_bound
    (B : Bank) (live : IsLive (X.seed pad) B)
    (name : U→Word own) (edgeCount : (Ext).host.edgeCount=E)
    (e p b D : ℕ) (degree : ∀ u,plant.degree u≤ D) (fit : E≤ 2^b) (v : U) :
    let cmd := expectedRootCommand X pad edgeCount b fit v
    ReadFormat B E cmd ∧ readCmdFee B e p E cmd≤ physicalRootReadCap X pad B e p b D := by
  cases v with
  | inl u =>
    let D0 := J6R68CanonicalRootWriter.rootLocalGate X u
    let b0 := tracedSlot (oldRootTrace X u) (exteriorOrdinal X edgeCount)∘D0.port
    change True ∧ originalGateFee E b (gatePorts (forgetGate (gateTape fit b0 D0.gate)))+
      A1R11.uvWidth e ell p+4≤ physicalRootReadCap X pad B e p b D
    refine ⟨True.intro,?_⟩
    have le := (original_read_code_uses_at_most_its_arity fit b0 D0.gate).trans
      (original_root_local_gate_fits D degree u.val)
    apply Nat.le_trans _ (le_max_left _ _)
    unfold originalGateFee
    gcongr
  | inr c =>
    let k := rootPageSource X c
    let pg := (widened pad (residentPageKey m k)).result
    let ws := printedRootWires X edgeCount k
    let R := (X.seed pad).immutable.payload
    let data := X.chosenFields k
    change ReadFormat B E (.packet (X.seed pad).identifier pg 0 ws) ∧
      readCmdFee B e p E (.packet (X.seed pad).identifier pg 0 ws)≤ physicalRootReadCap X pad B e p b D
    refine ⟨true_exterior_seed_packet_format X (pad:=pad) B live k E 0 ws,?_⟩
    have wsFit := emitted_root_packet_has_real_wire_sizes X gate pad name edgeCount k
    have act := literal_found_root_packet_price B R data (X.seed pad).identifier pg
      live.2 (true_seed_payload_page X pad k) ws p e E (rootBodyWidth m) wsFit.1 wsFit.2
    refine act.trans ((Finset.le_sup
      (f:=fun j : CanonicalPage m=>stoppedPacketLookupCap B R (X.chosenFields j) p E (rootBodyWidth m))
      (Finset.mem_univ k)).trans (le_max_right _ _))

theorem same_root_interpreter_cutoff_fee_from_actual_dimensions
    (B : Bank) (live : IsLive (X.seed pad) B)
    (name : U→Word own) (owners : ExteriorRoster X gate pad name)
    (edgeCount : (Ext).host.edgeCount=E) (F : Frame f (Ext).prec)
    (b D : ℕ) (degree : ∀ u,plant.degree u≤ D) (fit : E≤ 2^b) :
    let fs := trueFrames X gate pad name
    let cmds := owners.order.map (expectedRootCommand X pad edgeCount b fit)
    (runRows X.hf F X.positive B (visitFramesClock fs).result cmds).steps≤
      rawLeafCap F.words.length ell (Ext).prec E (Nat.card U)
        (Nat.card U*physicalRootReadCap X pad B F.words.length (Ext).prec b D) F.hp := by
  let fs := trueFrames X gate pad name
  let cmds := owners.order.map (expectedRootCommand X pad edgeCount b fit)
  let clock := visitFramesClock fs
  have size : clock.result.length=E := by
    unfold clock
    rw [frame_clock_exact,List.length_replicate]
    unfold fs trueFrames
    rw [List.length_map,ordered_exterior_exact_length X edgeCount]
  have census : cmds.length=Nat.card U :=
    (List.length_map _).trans (actual_complete_order_length owners.order owners.unique owners.complete)
  have row (t : ReadCmd key Pg) (h : t∈cmds) :
      ReadFormat B E t ∧ readCmdFee B F.words.length (Ext).prec E t≤
        physicalRootReadCap X pad B F.words.length (Ext).prec b D := by
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp h
    exact each_actual_root_command_reads_with_size_bound X gate pad B live name edgeCount
      F.words.length (Ext).prec b D degree fit v
  have e := same_row_interpreter_fee X.hf F X.positive B clock.result size cmds
    (fun t h=>(row t h).1)
  have book : cmdBill B F.words.length (Ext).prec E cmds≤
      Nat.card U*physicalRootReadCap X pad B F.words.length (Ext).prec b D := by
    unfold cmdBill
    exact (sum_map_cap cmds _ _ (fun t h=>(row t h).2)).trans_eq
      (congrArg (fun n=>n*physicalRootReadCap X pad B F.words.length (Ext).prec b D) census)
  rw [census] at e
  refine e.trans ?_
  unfold rawLeafCap
  gcongr

#print axioms original_read_code_uses_at_most_its_arity
#print axioms emitted_root_packet_has_real_wire_sizes
#print axioms each_actual_root_command_reads_with_size_bound
#print axioms same_root_interpreter_cutoff_fee_from_actual_dimensions
end
end J6R68CanonicalRootWriter
