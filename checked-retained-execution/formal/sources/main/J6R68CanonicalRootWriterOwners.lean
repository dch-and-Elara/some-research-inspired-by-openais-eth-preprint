import J6R68CanonicalRootWriterGate
import J6R68CanonicalRootWriterPage
import J6R68CanonicalRootWriterDispatch
import J6R53OldOwnerRootBasis

/-! Validate each actual encoded owner instruction in the true root
stop. The runtime branch test examines the mounted OwnerData; the
proof branches over the actual pre-existing physical vertex sum. -/
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
open J6R54TerminalBoot J6R24MeteredRecursion J6R53OldOwnerRoot

set_option quotPrecheck false
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 18500000
set_option maxRecDepth 5200
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
local notation "Col" => (exteriorChild G ell X.centre X.sample X.group).host.Col
local notation "Pg" => (pageKeyWidth m+pad)
local notation "N" => (exteriorChild G ell X.centre X.sample X.group).edges

def expectedRootCommand (edgeCount : (Ext).host.edgeCount=N) (b : ℕ) (fit : N≤2^b) :
    U→ReadCmd key Pg
  | .inl u =>
    let d := J6R68CanonicalRootWriter.rootLocalGate X u
    .gate b (forgetGate (gateTape fit (tracedSlot (oldRootTrace X u)
      (exteriorOrdinal X edgeCount)∘d.port) d.gate))
  | .inr k=>exteriorPageCommand X pad edgeCount (rootPageSource X k)

theorem actual_raw_owner_writes_the_expected_command
    (name : U→Word own) (injective : Function.Injective name) (gateWidth : gate.created.val=base)
    (edgeCount : (Ext).host.edgeCount=N) (b : ℕ) (hb : 0<b) (fit : N≤2^b) (v : U) :
    let fs := trueFrames X gate pad name
    let bk := frameKeys fs
    let r : RefRow own (OwnerData (SuffixWordWidth m) key prec Pg) :=
      ⟨name v,exteriorData X gate pad v⟩
    (writeRootOwner b bk.result fs r).result=some (expectedRootCommand X pad edgeCount b fit v) := by
  let fs := trueFrames X gate pad name
  let bk := frameKeys fs
  let r : RefRow own (OwnerData (SuffixWordWidth m) key prec Pg) :=
    ⟨name v,exteriorData X gate pad v⟩
  change (writeRootOwner b bk.result fs r).result=_
  rw [root_owner_write_exact_cost]
  dsimp only [r]
  cases v with
  | inl u =>
    change (compileSavedGate b bk.result fs (name (.inl u))
      (printedGateCode (f:=f) (ell:=ell) (base:=base) P (rootOldSource X u))).result=_
    exact (raw_gate_writer_is_original_scope X gate pad name injective edgeCount u hb fit).1
  | inr c =>
    obtain ⟨k,rfl⟩ := (canonicalPageEquiv G ell X.centre).surjective c
    have same : rootPageSource X (pageCol X k)=k := (canonicalPageEquiv G ell X.centre).symm_apply_apply k
    change (compileFreshOne (X.seed pad).identifier bk.result fs (bootPageKey X pad (pageCol X k))).result=
      some (exteriorPageCommand X pad edgeCount (rootPageSource X (pageCol X k)))
    rw [same]
    exact (paid_page_writer_is_same_physical_packet X gate pad name gateWidth edgeCount k).1

theorem actual_compiled_root_row_has_canonical_semantics
    (basePos : 0<base) (name : U→Word own)
    (gateWidth : gate.created.val=base) (edgeCount : (Ext).host.edgeCount=N)
    (b : ℕ) (fit : N≤2^b) (F : Frame f (Ext).prec)
    (B : PageBank f ell key prec tw bw Pg) (live : IsLive (X.seed pad) B)
    (bits : Fin N→Bool) (v : U) :
    let ord := exteriorOrdinal X edgeCount
    F.decode ((expectedRootCommand X pad edgeCount b fit v).read X.hf F X.positive B (List.ofFn bits)).result=
      ((Ext).host.file v).read X.hf (Ext).prec (assignment (Ext).host.network (bits∘ord.symm) v) := by
  let ord := exteriorOrdinal X edgeCount
  cases v with
  | inl u =>
    let r := originalRow P (constantRootWord m) X.hf F X.positive ord
      (.inl u) (IsLive (X.seed pad)) basePos (rootOldSource X u) (oldRootTrace X u) fit
    change F.decode ((eraseCode r.code).read X.hf F X.positive B (List.ofFn bits)).result=_
    rw [erase_read_exact]
    exact r.value B live bits
  | inr c =>
    obtain ⟨k,rfl⟩ := (canonicalPageEquiv G ell X.centre).surjective c
    have same : rootPageSource X (pageCol X k)=k := (canonicalPageEquiv G ell X.centre).symm_apply_apply k
    obtain ⟨cmd,hit,val⟩ := paid_packet_command_matches_canonical_root_row X gate pad basePos name
      gateWidth edgeCount k F B live bits
    have H := (paid_page_writer_is_same_physical_packet X gate pad name gateWidth edgeCount k).1
    have eq : cmd=exteriorPageCommand X pad edgeCount k := Option.some.inj (hit.symm.trans H)
    subst cmd
    change F.decode ((exteriorPageCommand X pad edgeCount (rootPageSource X (pageCol X k))).read
      X.hf F X.positive B (List.ofFn bits)).result=_
    rw [same]
    exact val.trans ((rootRow X pad basePos F ord (.inr (pageCol X k))).value B live bits)

#print axioms actual_raw_owner_writes_the_expected_command
#print axioms actual_compiled_root_row_has_canonical_semantics
end
end J6R68CanonicalRootWriter

