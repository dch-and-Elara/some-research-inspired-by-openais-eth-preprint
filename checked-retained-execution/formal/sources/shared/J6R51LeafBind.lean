import J6R51LeafCore
import J6R50LeafNative

/-! Leaf value on the actual slot and the existing opened source bank.
The live StoredSite supplies the NativeJob; the only remaining local
format proof is that its provided resident owner tape encodes the
true R49 source entries. There is no path-to-patch function. -/
namespace J6R51Leaf
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 A1R11 A1R12
open J6Mesh J6OrientedHost P11FullPacking P1DyadicGrid J6R24LegalLayout
open J6R10Repack J6R11Blueprint J6R11Repack J6R12Blueprint J6R21Ancestor J6R20Ancestor
open J6R14ZeroMode J6R27PrescribedProbe J6R32RootGeneratedRegistryInputs
open J6R31RootResidentTables J6R30GeneratedRootLayout J6R27OriginalGate J6R9PacketScopes
open J6ActiveRun J6ActiveSchedule J1PPrinted J6R26StablePreparedRoot
open J6R34RootAtlas J6R33StatefulArithmeticPage J6R32StatefulArithmetic
open J6R30ProducedGateRegistry J6R22Active J6R35RootOrigins J6R48Leaf J6R49Leaf
open J6R9Recursive J6R10Reachable J6R24MeteredRecursion J6R21Leaf J6R16ModeCost
open J6R26DescriptorTree J6R34ChildPath J6R25PreparedSupply
open J6R50Leaf J6R50SourceProducer
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 45000000
set_option maxRecDepth 4400

noncomputable section
variable {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {V : Type} [Fintype V]
variable {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {q ro co d edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
variable {P : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (pad : ℕ)
variable (actual : InputFamily P key prec tw bw (pageKeyWidth m+pad))
local notation "ext" => exteriorChild G ell X.centre X.sample X.group
local notation "pg" => pageKeyWidth m+pad
local notation "SP" => printedParams (f:=f) (ell:=ell) s
variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel)
  (exteriorChild G ell X.centre X.sample X.group))]

def sourceRootTerminal (basePos : 0<base) (stop : (ext).edges≤(SP).cutoff)
    (ord : Fin (ext).edges≃(ext).host.Edge) (B : PageBank f ell key prec tw bw pg) :
    Meter (Block (P.frame (NativeReach.reflexive ext)) ell) :=
  literalLeafExec X pad actual basePos Path.root stop ord B

theorem source_root_terminal_unchanged (basePos : 0<base) (stop : (ext).edges≤(SP).cutoff)
    (ord : Fin (ext).edges≃(ext).host.Edge) (B : PageBank f ell key prec tw bw pg)
    (alive : IsLive (X.seed pad) B) :
    (P.frame (NativeReach.reflexive ext)).decode (sourceRootTerminal X pad actual basePos stop ord B).result=
      (sourceBlueprint sel ext X.hf).program.run ext :=
  literal_leaf_exec_correct X pad actual basePos Path.root stop ord B alive

def sourceStoredTerminal (basePos : 0<base)
    {c : Call (PhysicalHost f ell)} (par : Path sel ext c) (slot : (Plan sel).Slot c)
    (site : StoredSite P (par.ticket slot) key prec tw bw pg)
    (data : Unit→ResidentLeafData site)
    (stop : ((Plan sel).child c slot).edges≤(SP).cutoff)
    (B : PageBank f ell key prec tw bw pg) :
    Meter (Block (P.frame (Path.step par slot).reached) ell) :=
  let next := Path.step par slot
  let F := P.frame next.reached
  let ord := actualEdgeOrder P (par.ticket slot) site.birth.native.physical
  storedLeaf site data F P.vPositive B
    (fun _=>literalLeafExec X pad actual basePos next stop ord B)

theorem source_stored_empty_is_old (basePos : 0<base)
    {c : Call (PhysicalHost f ell)} (par : Path sel ext c) (slot : (Plan sel).Slot c)
    (site : StoredSite P (par.ticket slot) key prec tw bw pg)
    (data : Unit→ResidentLeafData site)
    (stop : ((Plan sel).child c slot).edges≤(SP).cutoff)
    (empty : ((Plan sel).child c slot).edges=0)
    (B : PageBank f ell key prec tw bw pg)
    (alive : opened (compileFamily actual) (IsLive (X.seed pad)) (Path.step par slot) B) :
    let next := Path.step par slot
    let old := literalLeafExec X pad actual basePos next stop
      (actualEdgeOrder P (par.ticket slot) site.birth.native.physical) B
    let out := sourceStoredTerminal X pad actual basePos par slot site data stop B
    out=⟨old.result,(storedBook site).steps+old.steps+3⟩ ∧
      (P.frame next.reached).decode out.result=
        (sourceBlueprint sel ext X.hf).program.run ((Plan sel).child c slot) := by
  dsimp only
  have e := stored_zero_preserves_read site data (P.frame (Path.step par slot).reached)
    P.vPositive B (fun _=>literalLeafExec X pad actual basePos (Path.step par slot) stop
      (actualEdgeOrder P (par.ticket slot) site.birth.native.physical) B) empty
  refine ⟨e,?_⟩
  rw [show sourceStoredTerminal X pad actual basePos par slot site data stop B=_ from e]
  exact literal_leaf_exec_correct X pad actual basePos (Path.step par slot) stop _ B alive

theorem source_stored_positive_exact (basePos : 0<base)
    {c : Call (PhysicalHost f ell)} (par : Path sel ext c) (slot : (Plan sel).Slot c)
    (site : StoredSite P (par.ticket slot) key prec tw bw pg)
    (sameInput : site.input=actual par slot)
    (data : Unit→ResidentLeafData site)
    (stop : ((Plan sel).child c slot).edges≤(SP).cutoff)
    (positive : 0<((Plan sel).child c slot).edges)
    (B : PageBank f ell key prec tw bw pg)
    (alive : opened (compileFamily actual) (IsLive (X.seed pad)) (Path.step par slot) B)
    (name : Vertex ((Plan sel).child c slot)→J6R15ModeCost.Word (data ()).own)
    (actualNames : (data ()).roster=(vertexList ((Plan sel).child c slot).host).map name)
    (validation : ∀ u : Vertex ((Plan sel).child c slot),
      SourceCommand ((Plan sel).child c slot).edges
        (fun j => childKey P (par.ticket slot) site.birth.native.physical
          (actualEdgeOrder P (par.ticket slot) site.birth.native.physical j))
        (data ()).lines (data ()).table (name u)
        (sourceLeafRow X pad actual basePos (Path.step par slot)
          (actualEdgeOrder P (par.ticket slot) site.birth.native.physical) u).code) :
    let F := P.frame (Path.step par slot).reached
    let attempted := storedAttempt site (data ()) F P.vPositive B (storedBook site)
    let out := sourceStoredTerminal X pad actual basePos par slot site data stop B
    IsLive site.birth.job B ∧
      ∃ value,attempted.result=some value ∧ out=⟨value,attempted.steps+6⟩ ∧
        F.decode value=(sourceBlueprint sel ext X.hf).program.run ((Plan sel).child c slot) := by
  have hb : IsLive site.birth.job B := by
    unfold StoredSite.birth
    rw [sameInput]
    exact alive.2
  obtain ⟨v,hv,hvalue,_⟩ := same_named_child_online_from_selected_book X pad actual basePos par slot
    site.birth.native stop positive B alive (data ()).lines (data ()).table (data ()).roster
      name actualNames validation
  refine ⟨hb,v,hv,?_,hvalue⟩
  exact stored_positive_fee site data (P.frame (Path.step par slot).reached) P.vPositive B
    (fun _=>literalLeafExec X pad actual basePos (Path.step par slot) stop
      (actualEdgeOrder P (par.ticket slot) site.birth.native.physical) B) positive v hv

#print axioms source_root_terminal_unchanged
#print axioms source_stored_empty_is_old
#print axioms source_stored_positive_exact
end
end J6R51Leaf
