import J6R50LeafSource
import J6R34ChildPathOrdinal

/-! Bind the explicit online emitter to the same addressed child of
the original fixed exterior invocation. The current edge book is
the actual paid parent-selected half-port book, including independent
row and column sides, not an uncharged index equivalence. -/
namespace J6R50Leaf
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
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 42000000
set_option maxRecDepth 4200

noncomputable section
variable {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {V : Type} [Fintype V]
variable {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {q ro co d edgew tc tj key prec tw bw own port eW dW tW zW mW : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
variable {P : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (pad : ℕ)
variable (actual : InputFamily P key prec tw bw (pageKeyWidth m+pad))
local notation "ext" => exteriorChild G ell X.centre X.sample X.group
local notation "pg" => pageKeyWidth m+pad
local notation "SP" => printedParams (f:=f) (ell:=ell) s
variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel)
  (exteriorChild G ell X.centre X.sample X.group))]

theorem same_named_child_online_from_selected_book (basePos : 0<base)
    {c : Call (PhysicalHost f ell)} (par : Path sel ext c) (slot : (Plan sel).Slot c)
    (J : NativeJob P (par.ticket slot) port eW dW prec tW zW mW)
    (stop : ((Plan sel).child c slot).edges≤(SP).cutoff)
    (positive : 0<((Plan sel).child c slot).edges)
    (B : PageBank f ell key prec tw bw pg)
    (alive : opened (compileFamily actual) (IsLive (X.seed pad)) (Path.step par slot) B)
    (lines : List (ResidentPort own port)) (table : OriginTable own port key prec pg)
    (roster : List (J6R15ModeCost.Word own))
    (name : Vertex ((Plan sel).child c slot)→J6R15ModeCost.Word own)
    (actualNames : roster=(vertexList ((Plan sel).child c slot).host).map name)
    (validation : ∀ u : Vertex ((Plan sel).child c slot),
      SourceCommand ((Plan sel).child c slot).edges
        (fun j => childKey P (par.ticket slot) J.physical (actualEdgeOrder P (par.ticket slot) J.physical j))
        lines table (name u)
        (sourceLeafRow X pad actual basePos (Path.step par slot)
          (actualEdgeOrder P (par.ticket slot) J.physical) u).code) :
    let leaf := (Plan sel).child c slot
    let p := Path.step par slot
    let F := P.frame p.reached
    let book := selectedEdgeBook J.gWord J.physical.raw
    let D := sourceLeafTape X pad actual basePos p (actualEdgeOrder P (par.ticket slot) J.physical)
    let out := onlineLeaf X.hf F P.vPositive B leaf.edges leaf.edges book lines table roster
    ∃ value, out.result=some value ∧
      F.decode value=(sourceBlueprint sel ext X.hf).program.run leaf ∧
      out.steps≤7+(J.physical.raw.map rowScanFee).sum+leaf.edges*(4*port+5)+
        (4*leaf.edges+12)+
        (D.rows.map (fun u=>(buildOwner leaf.edges leaf.edges book.result lines table (name u.1)).steps+7)).sum+
        rawLeafCap F.words.length ell leaf.prec leaf.edges D.rows.length (prepriced D F B) F.hp := by
  let leaf := (Plan sel).child c slot
  let p := Path.step par slot
  let F := P.frame p.reached
  let ord := actualEdgeOrder P (par.ticket slot) J.physical
  let keys := selectedEdgeBook J.gWord J.physical.raw
  let keyAt (j : Fin leaf.edges) := childKey P (par.ticket slot) J.physical (ord j)
  let rows := sourceLeafRow X pad actual basePos p ord
  obtain ⟨W,_,cost⟩ := exact_child_edge_book P (par.ticket slot) J
  have inj : Function.Injective keyAt :=
    (child_key_injective P (par.ticket slot) J.physical).comp ord.injective
  obtain ⟨val,result,answer,bill⟩ := checked_online_leaf_from_rows X.hf F P.vPositive B
    leaf.edges positive keys keyAt inj W lines table roster name actualNames ord
    (planEdges (T:=P) p) (opened (compileFamily actual) (IsLive (X.seed pad)) p) alive rows validation
  refine ⟨val,result,answer.trans (true_source_stops_on_same_host P p stop),?_⟩
  let D := sourceLeafTape X pad actual basePos p ord
  change keys.steps≤7+(J.physical.raw.map rowScanFee).sum+leaf.edges*(4*port+5) at cost
  change (onlineLeaf X.hf F P.vPositive B leaf.edges leaf.edges keys lines table roster).steps≤
    keys.steps+4*leaf.edges+12+
    (D.rows.map (fun u=>(buildOwner leaf.edges leaf.edges keys.result lines table (name u.1)).steps+7)).sum+
    rawLeafCap F.words.length ell leaf.prec leaf.edges D.rows.length (prepriced D F B) F.hp at bill
  change (onlineLeaf X.hf F P.vPositive B leaf.edges leaf.edges keys lines table roster).steps≤
    7+(J.physical.raw.map rowScanFee).sum+leaf.edges*(4*port+5)+(4*leaf.edges+12)+
    (D.rows.map (fun u=>(buildOwner leaf.edges leaf.edges keys.result lines table (name u.1)).steps+7)).sum+
    rawLeafCap F.words.length ell leaf.prec leaf.edges D.rows.length (prepriced D F B) F.hp
  omega

#print axioms same_named_child_online_from_selected_book
end
end J6R50Leaf
