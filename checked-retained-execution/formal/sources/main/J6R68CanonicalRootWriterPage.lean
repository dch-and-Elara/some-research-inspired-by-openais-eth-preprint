import J6R68CanonicalRootWriterPageBasis

/-! Emit a full packet command on the immutable physical root
frames. The raw scan walks the actual page keys, then writes
its unary ordinals by paid fixed-word seek. -/
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
open J6R67CanonicalStop J6R11Blueprint J6R49Leaf J6R51Leaf J6R34ChildPath
open J6R24MeteredRecursion

set_option quotPrecheck false
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 16000000
set_option maxRecDepth 4600
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co d edgew tc tj key prec tw bw own : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "E" => (exteriorChild G ell X.centre X.sample X.group).host.Edge
local notation "U" => (Vertex (exteriorChild G ell X.centre X.sample X.group))
local notation "Pg" => (pageKeyWidth m+pad)

def pageWireHeader (k : CanonicalPage m) (x : PortAt (pagePoint X k)) : List Bool :=
  (emittedPageTrace X k).literal (originSeed (rootChart P) (oddAxis m) X.group k) x

def pageWireOrdinal (edgeCount : (Ext).host.edgeCount=(Ext).edges) (k : CanonicalPage m)
    (x : PortAt (pagePoint X k)) : Fin (Ext).edges :=
  (exteriorOrdinal X edgeCount).symm (edge x.val)

def exteriorPageCommand (edgeCount : (Ext).host.edgeCount=(Ext).edges) (k : CanonicalPage m) :
    ReadCmd key Pg :=
  .packet (X.seed pad).identifier (widened pad (residentPageKey m k)).result 0
    ((orderedPagePorts X k).map
      (fun x=>⟨pageWireHeader X k x,List.replicate (pageWireOrdinal X edgeCount k x).val true⟩))

theorem true_root_page_word (k : CanonicalPage m) :
    bootPageKey X pad (pageCol X k)=(widened pad (residentPageKey m k)).result := by
  unfold bootPageKey pageCol
  rw [Equiv.symm_apply_apply]

theorem actual_root_requests_are_same_page_routes
    (name : U→Word own) (gateWidth : gate.created.val=base)
    (edgeCount : (Ext).host.edgeCount=(Ext).edges) (k : CanonicalPage m) :
    let fs := trueFrames X gate pad name
    let pg := bootPageKey X pad (pageCol X k)
    let eWord := exteriorEdgeWord X∘exteriorOrdinal X edgeCount
    (scanFresh pg fs).result=(orderedPagePorts X k).map
      (fun x=>⟨eWord (pageWireOrdinal X edgeCount k x),pageWireHeader X k x⟩) := by
  dsimp only
  rw [actual_root_packet_scan X gate pad name gateWidth k]
  apply List.map_congr_left
  intro x _
  unfold requestView
  have keyEq := (two_frame_lanes_share_true_edge_word X gate pad name (edge x.val)).2
  have body := (emitted_packet_seed_is_same_frame X gate pad name k x).2
  have native : (exteriorOrdinal X edgeCount) (pageWireOrdinal X edgeCount k x)=edge x.val :=
    (exteriorOrdinal X edgeCount).apply_symm_apply _
  dsimp only [Function.comp_apply]
  rw [keyEq,native]
  exact congrArg (WireRequest.mk (exteriorEdgeWord X (edge x.val))) body

theorem paid_page_writer_is_same_physical_packet (name : U→Word own)
    (gateWidth : gate.created.val=base) (edgeCount : (Ext).host.edgeCount=(Ext).edges)
    (k : CanonicalPage m) :
    let fs := trueFrames X gate pad name
    let pg := bootPageKey X pad (pageCol X k)
    let b := frameKeys fs
    let r := compileFreshOne (X.seed pad).identifier b.result fs pg
    r.result=some (exteriorPageCommand X pad edgeCount k) ∧
      r.steps=3+(fs.map (freshVisitFee pg)).sum+
        (4+((orderedPagePorts X k).map
          (fun x=>sourceWireFee (rootHalfWidth m) (pageWireOrdinal X edgeCount k x).val
            (pageWireHeader X k x).length)).sum)+(3*key+1)+(3*Pg+1)+7 := by
  let fs := trueFrames X gate pad name
  let pg := bootPageKey X pad (pageCol X k)
  let b := frameKeys fs
  let eWord := exteriorEdgeWord X∘exteriorOrdinal X edgeCount
  have eUnique : Function.Injective eWord :=
    (exterior_edge_words_injective X).comp (exteriorOrdinal X edgeCount).injective
  have book : b.result=List.ofFn eWord :=
    congrArg Meter.result (actual_root_edge_book X gate pad name edgeCount)
  obtain ⟨code,fee⟩ := source_wire_tape b.result eWord eUnique book (orderedPagePorts X k)
    (pageWireHeader X k) (pageWireOrdinal X edgeCount k) (scanFresh pg fs).result
    (actual_root_requests_are_same_page_routes X gate pad name gateWidth edgeCount k)
  have scanFee := congrArg Meter.steps (scan_fresh_exact pg fs)
  change (compileFreshOne (X.seed pad).identifier b.result fs pg).result=_ ∧ _
  unfold compileFreshOne
  dsimp only
  rw [code,fee,copy_fixed_exact,copy_fixed_exact,
    show (scanFresh pg fs).steps=3+(fs.map (freshVisitFee pg)).sum from scanFee]
  exact ⟨congrArg some (congrArg (fun w=>ReadCmd.packet (X.seed pad).identifier w 0 _) (true_root_page_word X pad k)),rfl⟩

theorem paid_packet_command_matches_canonical_root_row
    (basePos : 0<base) (name : U→Word own)
    (gateWidth : gate.created.val=base) (edgeCount : (Ext).host.edgeCount=(Ext).edges)
    (k : CanonicalPage m) (F : Frame f (Ext).prec)
    (B : PageBank f ell key prec tw bw Pg) (live : IsLive (X.seed pad) B)
    (bits : Fin (Ext).edges→Bool) :
    let ord := exteriorOrdinal X edgeCount
    let fs := trueFrames X gate pad name
    let b := frameKeys fs
    let out := compileFreshOne (X.seed pad).identifier b.result fs (bootPageKey X pad (pageCol X k))
    ∃ cmd,out.result=some cmd ∧
      F.decode (cmd.read X.hf F X.positive B (List.ofFn bits)).result=
      F.decode (((rootRow X pad basePos F ord (.inr (pageCol X k))).code).run
        X.hf F X.positive B (List.ofFn bits)).result := by
  let ord := exteriorOrdinal X edgeCount
  let tr := emittedPageTrace X k
  let ps := orderedPagePorts X k
  let ws : List WireRead := ps.map (fun x=>⟨pageWireHeader X k x,List.replicate (pageWireOrdinal X edgeCount k x).val true⟩)
  have val := (true_exterior_seed_entry X pad k B live tr F ord bits ps
    (all_page_ports_in_physical_order X k) ws rfl).1
  change F.decode (readPage X.hf F X.positive (X.seed pad).identifier
    (widened pad (residentPageKey m k)).result tr.depth ws (List.ofFn bits) B).result=_
    at val
  have dep : tr.depth=0 := emitted_page_route_depth_is_zero X k
  rw [dep] at val
  refine ⟨exteriorPageCommand X pad edgeCount k,
    (paid_page_writer_is_same_physical_packet X gate pad name gateWidth edgeCount k).1,?_⟩
  exact val.trans ((rootRow X pad basePos F ord (.inr (pageCol X k))).value B live bits).symm

#print axioms true_root_page_word
#print axioms actual_root_requests_are_same_page_routes
#print axioms paid_page_writer_is_same_physical_packet
#print axioms paid_packet_command_matches_canonical_root_row
end
end J6R68CanonicalRootWriter

