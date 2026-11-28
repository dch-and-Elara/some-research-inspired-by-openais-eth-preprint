import J6R68CanonicalRootWriterGateBasis
import J6R54TerminalBootSeed

/-! Compile the literal original Gate in the same exterior edge order.
The old opcode and literal signs are the fixed Plant syntax; the paid
lookups translate its suffixes to live addresses, then to ordinals. -/
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
open J6R54TerminalBoot J6R24MeteredRecursion

set_option quotPrecheck false
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 17500000
set_option maxRecDepth 4900
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co d edgew tc tj key prec tw bw own : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "U" => (Vertex (exteriorChild G ell X.centre X.sample X.group))
local notation "Row" => (exteriorChild G ell X.centre X.sample X.group).host.Row
local notation "Pg" => (pageKeyWidth m+pad)
local notation "W" => (rootHalfWidth m)
local notation "Q" => (pageKeyWidth m+a m)
local notation "N" => (exteriorChild G ell X.centre X.sample X.group).edges

abbrev rootLocalGate (u : Row) := originalPortGate P (constantRootWord m) (rootOldSource X u)

def rootGateSeed (u : Row) (x : PortAt (atVertex Ext (.inl u))) : Word Q :=
  rootSuffixAt (f:=f) (ell:=ell) (base:=base) P (rootOldSource X u) ((oldRootTrace X u).back x)

def rootGateLiveWord (u : Row) (x : PortAt (atVertex Ext (.inl u))) : Word W :=
  exteriorEdgeWord X (edge x.val)

theorem root_old_input_suffix_table (name : U→Word own) (injective : Function.Injective name) (u : Row) :
    let fs := trueFrames X gate pad name
    let requests := collectRetained (name (.inl u)) fs
    let ports := orderedOldPorts X u
    suffixTable Q requests.result=
      ⟨ports.map (fun x=>⟨rootGateSeed X u x,rootGateLiveWord X u x⟩),
        3+(ports.map (fun _=>22+8*Q+3*W)).sum⟩ := by
  let fs := trueFrames X gate pad name
  let R := collectRetained (name (.inl u)) fs
  let ports := orderedOldPorts X u
  let seed := rootGateSeed X u
  let live := rootGateLiveWord X u
  have req : R.result=ports.map (fun x=>⟨live x,[false]++(seed x).bits⟩) := by
    dsimp only [R,fs,ports]
    rw [actual_root_old_scan X gate pad name injective u]
    apply List.map_congr_left
    intro x _
    exact congrArg₂ WireRequest.mk
      (two_frame_lanes_share_true_edge_word X gate pad name (edge x.val)).1
      (retained_lane_is_true_original_suffix X gate pad name u x)
  change suffixTable Q R.result=_
  rw [req,suffix_table_exact ports seed live (fun _=>[false])]
  simp only [List.length_cons,List.length_nil]
  have rate : 17+8*Q+3*W+5=22+8*Q+3*W := by omega
  rw [rate]

theorem raw_gate_writer_is_original_scope (name : U→Word own) (injective : Function.Injective name)
    (edgeCount : (Ext).host.edgeCount=(Ext).edges) (u : Row)
    {b : ℕ} (hb : 0<b) (fit : N≤2^b) :
    let fs := trueFrames X gate pad name
    let book := frameKeys fs
    let ord := exteriorOrdinal X edgeCount
    let d := rootLocalGate X u
    let src := printedGateCode (f:=f) (ell:=ell) (base:=base) P (rootOldSource X u)
    let out := compileSavedGate b book.result fs (name (.inl u)) src
    out.result=some (.gate b (forgetGate (gateTape fit
      (tracedSlot (oldRootTrace X u) ord∘d.port) d.gate))) ∧
    out.steps≤(collectRetained (name (.inl u)) fs).steps+
      (3+((orderedOldPorts X u).map (fun _=>22+8*Q+3*W)).sum)+
      (8+d.degree*(locateFee Q (orderedOldPorts X u).length+W+9))+
      currentGateFee W b N d.degree+7 := by
  let fs := trueFrames X gate pad name
  let book := frameKeys fs
  let ord := exteriorOrdinal X edgeCount
  let j := exteriorEdgeWord X∘ord
  let D := rootLocalGate X u
  let T := oldRootTrace X u
  let slot := tracedSlot T ord∘D.port
  let ps := orderedOldPorts X u
  let s := rootGateSeed X u
  let l := rootGateLiveWord X u
  let pre := collectRetained (name (.inl u)) fs
  let idx := suffixTable Q pre.result
  let sup := T.back.symm∘D.port
  let g := printedGateCode (f:=f) (ell:=ell) (base:=base) P (rootOldSource X u)
  let route := rerouteGate idx.result g
  have hs : Function.Injective s :=
    (actual_owned_root_suffix_injective (f:=f) (ell:=ell) (base:=base) P (rootOldSource X u)).comp T.back.injective
  have src : s∘sup=rootSuffixAt (f:=f) (ell:=ell) (base:=base) P (rootOldSource X u)∘D.port := by
    funext i
    change rootSuffixAt (f:=f) (ell:=ell) (base:=base) P (rootOldSource X u)
      (T.back (T.back.symm (D.port i)))=_
    rw [Equiv.apply_symm_apply]
    rfl
  have dst : l∘sup=j∘slot := by
    funext i
    change exteriorEdgeWord X (edge (T.back.symm (D.port i)).val)=
      exteriorEdgeWord X (ord (ord.symm (edge (T.back.symm (D.port i)).val)))
    rw [Equiv.apply_symm_apply]
  have table := root_old_input_suffix_table X gate pad name injective u
  have eTable : idx.result=ps.map (fun x=>⟨s x,l x⟩) := congrArg Meter.result table
  have cTable : idx.steps=3+(ps.map (fun _=>22+8*Q+3*W)).sum := congrArg Meter.steps table
  have r := reroute_actual_gate ps s hs l sup (fun i=>all_old_ports_in_physical_order X u (sup i)) D.gate
  dsimp only at r
  rw [src,dst] at r
  have rg : route.result=some (encodeGate (j∘slot) D.gate) ∧
      route.steps≤8+D.degree*(locateFee Q ps.length+W+9) := by
    unfold route
    rw [eTable]
    exact r
  have jb : book.result=List.ofFn j :=
    congrArg Meter.result (actual_root_edge_book X gate pad name edgeCount)
  have ji : Function.Injective j := (exterior_edge_words_injective X).comp ord.injective
  have comp := current_source_gate hb fit book.result j ji jb slot D.gate
  change (compileSavedGate b book.result fs (name (.inl u)) g).result=_ ∧ _
  unfold compileSavedGate
  dsimp only
  rw [show (rerouteGate (suffixTable Q pre.result).result g).result=_ from rg.1]
  dsimp only
  refine ⟨?_,?_⟩
  · exact congrArg (Option.map (ReadCmd.gate b)) comp.1
  · change pre.steps+idx.steps+route.steps+
      (compileCurrentGate b book.result (encodeGate (j∘slot) D.gate)).steps+7≤_
    rw [cTable]
    have h := comp.2
    calc
      _≤pre.steps+(3+(ps.map (fun _=>22+8*Q+3*W)).sum)+
        (8+D.degree*(locateFee Q ps.length+W+9))+currentGateFee W b N D.degree+7 :=
        Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_left rg.2 _) h) _
      _=_ := rfl

theorem paid_gate_command_matches_canonical_root_row (basePos : 0<base)
    (name : U→Word own) (injective : Function.Injective name)
    (edgeCount : (Ext).host.edgeCount=(Ext).edges) (u : Row)
    (b : ℕ) (hb : 0<b) (fit : N≤2^b) (F : Frame f (Ext).prec)
    (B : PageBank f ell key prec tw bw Pg) (live : IsLive (X.seed pad) B)
    (bits : Fin N→Bool) :
    let ord := exteriorOrdinal X edgeCount
    let fs := trueFrames X gate pad name
    let out := compileSavedGate b (frameKeys fs).result fs (name (.inl u))
      (printedGateCode (f:=f) (ell:=ell) (base:=base) P (rootOldSource X u))
    ∃ cmd,out.result=some cmd ∧
      F.decode (cmd.read X.hf F X.positive B (List.ofFn bits)).result=
      F.decode (((rootRow X pad basePos F ord (.inl u)).code).run
        X.hf F X.positive B (List.ofFn bits)).result := by
  let ord := exteriorOrdinal X edgeCount
  let source := originalRow P (constantRootWord m) X.hf F X.positive ord
    (.inl u) (IsLive (X.seed pad)) basePos (rootOldSource X u) (oldRootTrace X u) fit
  have same := (raw_gate_writer_is_original_scope X gate pad name injective edgeCount u hb fit).1
  refine ⟨eraseCode source.code,same,?_⟩
  rw [erase_read_exact]
  exact (source.value B live bits).trans ((rootRow X pad basePos F ord (.inl u)).value B live bits).symm

#print axioms root_old_input_suffix_table
#print axioms raw_gate_writer_is_original_scope
#print axioms paid_gate_command_matches_canonical_root_row
end
end J6R68CanonicalRootWriter

