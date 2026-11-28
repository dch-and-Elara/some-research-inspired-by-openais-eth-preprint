import J6R49LeafRowRecord
import J6R21LeafSerial
import J6R34ChildPathLeafOrder

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option Elab.async false
set_option maxHeartbeats 14000000
set_option maxRecDepth 2700

/-! One checked row of the actual finite leaf entry file and the
proof-side assembly of complete raw tapes from such rows. The literal
source constructors below discharge these receipts by origin;
a receipt type alone is not a source-route existence theorem. -/
namespace J6R49Leaf
open scoped Polynomial Classical BigOperators
open Polynomial AOracleMachineTime A1R10 A1R11 A1R12
open J6ActiveRun J6R9Recursive J6R10Repack J6R10Reachable J6R11Blueprint
open J6R12Blueprint J1PPrinted J6R21Ancestor J6R21Leaf J6R22Active
open J6R24MeteredRecursion J6R30ProducedGateRegistry J6R32StatefulArithmetic
open J6R33StatefulArithmeticPage J6R48Leaf
noncomputable section

variable {f : ℤ[X]} {ell key prec tw bw page : ℕ}
local notation "BankAt" => Bank f ell key prec tw bw page

variable {c : Call (PhysicalHost f ell)} {hf : f.Monic} {F : Frame f c.prec}
variable {pos : 0<ell} {ord : Fin c.edges≃c.host.Edge} {live : PageBank f ell key prec tw bw page→Prop}

def orderedCommands (hEdges : c.host.edgeCount=c.edges)
    (commands : Vertex c→PageReadCode c.edges key page) : PagedLeaf c key page := by
  let clock : List Unit := List.replicate c.edges ()
  have hClock : clock.length=c.edges := List.length_replicate
  exact ⟨hEdges,clock,hClock,vertexList c.host,vertexList_nodup c.host,
    vertexList_complete c.host,commands⟩

set_option maxHeartbeats 35000000 in
def compiledLeaf {f : ℤ[X]} {ell key prec tw bw page : ℕ}
    {c : Call (PhysicalHost f ell)} {hf : f.Monic} {F : Frame f c.prec}
    {pos : 0<ell} {ord : Fin c.edges≃c.host.Edge}
    {live : PageBank f ell key prec tw bw page→Prop}
    (hEdges : c.host.edgeCount=c.edges)
    (rows : ∀ v : Vertex c,@RowAt f ell key prec tw bw page c hf F pos ord v live) :
    PagedLeaf c key page :=
  @orderedCommands f ell key page c hEdges (fun v=>(rows v).code)

theorem compiled_leaf_format (hEdges : c.host.edgeCount=c.edges)
    (rows : ∀ v : Vertex c,@RowAt f ell key prec tw bw page c hf F pos ord v live)
    (B : BankAt) (running : live B) :
    HasResidentFormat (PagedLeaf.toRaw ((@compiledLeaf f ell key prec tw bw page c hf F pos ord live hEdges rows))) B := by
  intro u H
  change u∈(vertexList c.host).map (fun v=>(v,(rows v).code)) at H
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp H
  exact (rows v).format B running

theorem compiled_leaf_each_read (hEdges : c.host.edgeCount=c.edges)
    (rows : ∀ v : Vertex c,@RowAt f ell key prec tw bw page c hf F pos ord v live)
    (B : BankAt) (running : live B) (bits : Fin c.edges→Bool) (v : Vertex c) :
    F.decode (((@compiledLeaf f ell key prec tw bw page c hf F pos ord live hEdges rows)).query hf F pos B v (List.ofFn bits)).result=
      (c.host.file v).read hf c.prec (assignment c.host.network (bits∘ord.symm) v) :=
  (rows v).value B running bits

/-- Only the final all-assignments sum erases the chosen edge order.
No per-read agreement between two different ordinal maps is assumed. -/
theorem compiled_leaf_in_literal_order (hEdges : c.host.edgeCount=c.edges)
    (rows : ∀ v : Vertex c,@RowAt f ell key prec tw bw page c hf F pos ord v live)
    (B : BankAt) (running : live B) :
    F.decode (((@compiledLeaf f ell key prec tw bw page c hf F pos ord live hEdges rows)).execute hf F pos B).result=
      reduce c.prec f ell (c.host.contract hf) := by
  exact J6R34ChildPath.actual_paged_leaf_physical_order ((@compiledLeaf f ell key prec tw bw page c hf F pos ord live hEdges rows)) hf F pos B ord
    (fun bits v=>compiled_leaf_each_read hEdges rows B running bits v)

section Plan
variable {s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {ok : f.Monic}
variable {T : Prepared cfg sel root ok}
local notation "SP" => printedParams (f:=f) (ell:=ell) s
variable (born : Births T key prec tw bw page)
variable (rootLive : PageBank f ell key prec tw bw page→Prop)

def planEdges {c : Call (PhysicalHost f ell)} (p : Path sel root c) :
    c.host.edgeCount=c.edges := (stable_reachable cfg sel p.reached T.rootStable).edgeCount

abbrev planOrder {c : Call (PhysicalHost f ell)} (p : Path sel root c) : Fin c.edges≃c.host.Edge :=
  (c.host.edgeOrder c.edges (planEdges (T:=T) p)).symm

abbrev RowFamily (birth : Births T key prec tw bw page) (alive : BankAt→Prop) :=

  ∀ {c : Call (PhysicalHost f ell)} (p : Path sel root c),c.edges≤(SP).cutoff→
    ∀ v : Vertex c,RowAt ok (T.frame p.reached) T.vPositive (planOrder (T:=T) p) v
      (opened birth alive p)

def residentFromRows (keep : StableBank rootLive) (rows : RowFamily born rootLive) :
    PagedResident T key prec tw bw page where
  births := born
  rootLive := rootLive
  stableRoot := keep
  leaf p stop := compiledLeaf (planEdges (T:=T) p) (rows p stop)
  sourceLeaf p stop B running bits v := compiled_leaf_each_read
    (planEdges (T:=T) p) (rows p stop) B running bits v

theorem resident_from_rows_has_real_format (keep : StableBank rootLive) (rows : RowFamily born rootLive)
    {c : Call (PhysicalHost f ell)} (p : Path sel root c) (stop : c.edges≤(SP).cutoff)
    (B : BankAt) (running : opened born rootLive p B) :
    HasResidentFormat (PagedLeaf.toRaw ((residentFromRows born rootLive keep rows).leaf p stop)) B :=
  compiled_leaf_format (planEdges (T:=T) p) (rows p stop) B running
end Plan

#print axioms compiled_leaf_format
#print axioms compiled_leaf_each_read
#print axioms compiled_leaf_in_literal_order
#print axioms residentFromRows
#print axioms resident_from_rows_has_real_format
end
end J6R49Leaf
