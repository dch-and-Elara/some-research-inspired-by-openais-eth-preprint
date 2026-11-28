import J6R25PreparedSupplyChildStage
import J6R25PreparedSupplyProducer
import J6R24MeteredRecursionNativeLedger

/-! At the literal packet address, install and read a truthful raw child
graph descriptor. The precision is the actual R17 prepared word; the
depth is incremented in its word, the edge count is obtained from the
sequential two-half-port receiver. Descriptor values are not child
answers. A full descendant gate/ancestor-entry registry is separate. -/
namespace J6R25PreparedSupply
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R17ModeTape
open J6ActiveRun J6ActiveSchedule J6R10Reachable J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R16ModeCost J6R14LayoutCost

variable {f : ℤ[X]} {ell s C : ℕ}
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
variable {c : Call (PhysicalHost f ell)}
variable (d : J6R12Blueprint.Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c)
variable (t : Center (printedParams (f:=f) (ell:=ell) s) c)

theorem physical_precision_word (cfg : RootBounds s C f) (L : CallLayout (C:=C) sel d) :
    (rawSite sel d t L).result.precision.val=registerPrecision S c t := by
  have hq : 0<uniformWidth s C := by unfold uniformWidth; omega
  obtain ⟨I,_,_,_,hp,_⟩ := siteTape_from_layout sel hq d t (site_input_width cfg d t)
    (rowTraffic L.leftWidth L.rightWidth (6*(S).levelBits c.depth) (uniformWidth s C) ((S).levelBits c.depth))
    L.layout (L.precision t) (L.exactPrecision t)
  exact (congrArg Word.val hp).trans I.precisionMeaning

set_option maxHeartbeats 4000000 in
theorem acquired_native_child {w b dep wp aw : ℕ}
    (P : PhysicalPorts sel d t w) (z : Probe S c) (β : NativeMenu (N sel) c t) (g : Fin 64)
    (key : Meter (Word aw)) (bank : List (DirRow aw))
    (prec : Word wp) (oldDepth : Word dep)
    (hp : prec.val=registerPrecision S c t)
    (hd : oldDepth.val=c.depth) (hdep : 0<dep) (db : c.depth+1<2^dep)
    (hb : 0<b) (eb : ((Plan sel).child c (addressed d t z β g)).edges<2^b)
    (fresh : ∀ row∈bank,row.id≠key.result) :
    let next := (Plan sel).child c (addressed d t z β g)
    let stage := childStage (b:=b) key (word g.val) prec oldDepth P.raw
    let res := publishThenAcquire stage bank
    let wires := ((P.physicalSelected g).map P.record).flatMap rowBytes
    stage.result.id=key.result ∧
      res.result=(stage.result::bank,some (childHeaderBytes (word (q:=wp) next.prec)
        (word (q:=dep) next.depth) (word (q:=b) next.edges) wires)) ∧
      res.steps≤stage.steps+fetchFee bank+3*stage.result.bytes.length+2*aw+9+
        fetchFee (stage.result::bank)+4 := by
  let next := (Plan sel).child c (addressed d t z β g)
  let G := childPortsWithCount (b:=b) (word g.val) P.raw
  let D := increment oldDepth
  let stage := childStage (b:=b) key (word g.val) prec oldDepth P.raw
  let wires := ((P.physicalSelected g).map P.record).flatMap rowBytes
  have e := child_stage_exact (b:=b) key (word g.val) prec oldDepth P.raw
  obtain ⟨hPorts,hEdges,_⟩ := P.true_child_port_tape hb g z β eb
  have dp : D.result.val=next.depth :=
    ((increment_exact hdep oldDepth (by rw [hd]; exact db)).1.trans
      (congrArg (fun x=>x+1) hd))
  have pp : prec.val=next.prec := hp
  have hPrecW : prec=word (q:=wp) next.prec := (valued_word prec).symm.trans (congrArg word pp)
  have hDepthW : D.result=word (q:=dep) next.depth := (valued_word _).symm.trans (congrArg word dp)
  have hEdgeW : G.result.2=word (q:=b) next.edges := (valued_word _).symm.trans (congrArg word hEdges)
  have bytes : stage.result.bytes= childHeaderBytes (word (q:=wp) next.prec)
      (word (q:=dep) next.depth) (word (q:=b) next.edges) wires := by
    change stage.result.bytes=_
    have e0 : stage.result.bytes=childHeaderBytes prec D.result G.result.2 (G.result.1.flatMap rowBytes) := e.2.1
    rw [e0,hPrecW,hDepthW,hEdgeW,show G.result.1=(P.physicalSelected g).map P.record from hPorts]
  have R := acquired_literal_child stage bank (fun row mem=>by rw [e.1]; exact fresh row mem)
  exact ⟨e.1,R.1.trans (congrArg (fun x=>(stage.result::bank,some x)) bytes),R.2⟩

#print axioms physical_precision_word
#print axioms acquired_native_child
end J6R25PreparedSupply

