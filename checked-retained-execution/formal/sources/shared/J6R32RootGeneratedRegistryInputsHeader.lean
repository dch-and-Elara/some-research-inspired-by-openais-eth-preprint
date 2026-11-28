import J6R32RootGeneratedRegistryInputsHeaderBits
import J6R26StablePreparedRootCalls
import J6R25PreparedSupplyPhysicalPorts

/-! Match the exterior header shape to the true native selected half-port graph. -/
namespace J6R32RootGeneratedRegistryInputs
open scoped Polynomial Classical
open Polynomial AOracleMachineTime AOracleMachineTimeTape
open J6R26DescriptorTree J6R25PreparedSupply J6R30ProducedGateRegistry
open J6R15ModeCost J6R21Ancestor J6R24MeteredRecursion J6R26StablePreparedRoot J6R14ZeroMode
open J6R12Blueprint J6R11Blueprint J6R10Repack J6ActiveRun J1PPrinted P11FullPacking
set_option maxHeartbeats 6500000
set_option maxRecDepth 2200

section Native
variable {f : ℤ[X]} {ell s : ℕ}
variable {c : Call (PhysicalHost f ell)}
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
variable (d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c)
variable (t : Center (printedParams (f:=f) (ell:=ell) s) c)

theorem physical_count_of_external {w : ℕ} (D : @PhysicalPorts f ell s sel c d t w)
    (W : Prescribed f (externalProbeDegree s c))
    (j : Fin (externalProbeDegree s c+1)) (g : Fin 64) :
    (D.physicalSelected g).length=(@externalZeroCall f ell s sel c d t W j g).edges := by
  let O := D.physicalSelected g
  have hD : O.Nodup := D.nodup.filter _
  letI := c.host.finiteEdge
  letI := c.host.finiteRow
  letI := c.host.finiteCol
  let h (p : Port c.host.Edge) := @physicalGroup f ell s sel c d t p=g
  have H : O.toFinset=(Finset.univ : Finset (Port c.host.Edge)).filter h := by
    ext p
    simp only [O,PhysicalPorts.physicalSelected,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,
      Finset.mem_filter,Finset.mem_univ,true_and,D.complete,h]
  let q := @externalZeroCall f ell s sel c d t W j g
  let A := {p : Port c.host.Edge // @physicalGroup f ell s sel c d t p=g}
  have C : O.length=Nat.card A := by
    rw [←List.toFinset_card_of_nodup hD,H,←Fintype.card_subtype,Nat.card_eq_fintype_card]
  have same : q.host.Edge=A := rfl
  calc
    _=Nat.card A := C
    _=Nat.card q.host.Edge := congrArg Nat.card same.symm
    _=q.edges := by
      letI := q.host.finiteEdge
      change Nat.card q.host.Edge=Fintype.card q.host.Edge
      exact Nat.card_eq_fintype_card

theorem external_child_port_count {w b : ℕ} (D : @PhysicalPorts f ell s sel c d t w)
    (hb : 0<b) (W : Prescribed f (externalProbeDegree s c))
    (j : Fin (externalProbeDegree s c+1)) (g : Fin 64)
    (fit : (@externalZeroCall f ell s sel c d t W j g).edges<2^b) :
    let H := childPortsWithCount (b:=b) (word g.val) D.raw
    H.result.1=(D.physicalSelected g).map D.record ∧
      H.result.2.val=(@externalZeroCall f ell s sel c d t W j g).edges ∧
      H.steps=3+(D.raw.map rowScanFee).sum+
        (b+3+(@externalZeroCall f ell s sel c d t W j g).edges*(13*b+8))+4 := by
  let H := childPortsWithCount (b:=b) (word g.val) D.raw
  let child := @externalZeroCall f ell s sel c d t W j g
  have n : (selectPorts (word g.val) D.raw).result.length=child.edges := by
    rw [D.physical_port_select g,List.length_map,physical_count_of_external sel d t D W j g]
  have hFit : (D.raw.filter (fun row=>(J6R21Ancestor.cmpAddr (word g.val) row.group).result)).length<2^b := by
    rw [←(select_ports_exact _ _).1,n]
    exact fit
  obtain ⟨_,hCount,hC⟩ := ports_counted hb (word g.val) D.raw hFit
  have hLen : H.result.1.length=child.edges := n
  exact ⟨D.physical_port_select g,hCount.trans hLen,hC.trans (by rw [hLen])⟩

theorem make_external_header_exact {tc tj pagew w b dep prec key : ℕ}
    (D : @PhysicalPorts f ell s sel c d t w) (W : Prescribed f (externalProbeDegree s c))
    (j : Fin (externalProbeDegree s c+1)) (g : Fin 64)
    (A : ExternalAddress tc tj pagew) (theCentre : (A.center.val:ℤ)=t.val)
    (theProbe : A.sample.val=j.val) (theGroup : A.group.val=g.val)
    (issue : Meter (Word key)) (receive : Word prec)
    (recv : receive.val=registerPrecision (printedParams (f:=f) (ell:=ell) s) c t) (oldDepth : Word dep)
    (old : oldDepth.val=c.depth) (depPos : 0<dep) (depFit : c.depth+1<2^dep)
    (edgePos : 0<b) (edgeFit : (@externalZeroCall f ell s sel c d t W j g).edges<2^b) :
    let J := externalHeaderJob (b:=b) A receive oldDepth D.raw
    let E := J.make issue
    let child := @externalZeroCall f ell s sel c d t W j g
    E.result.id=issue.result ∧
      E.result.bytes=A.bytes++childHeaderBytes receive (word (q:=dep) child.depth)
        (word (q:=b) child.edges) ((D.physicalSelected g).map D.record |>.flatMap rowBytes) ∧
      loadAt prec (externalAddrWidth tc tj pagew) E.result.bytes=
         ⟨some receive,headerReadFee prec (externalAddrWidth tc tj pagew)⟩ ∧
      receive.val=child.prec ∧ (A.center.val:ℤ)=t.val ∧ A.sample.val=j.val ∧ A.group.val=g.val := by
  let J := externalHeaderJob (b:=b) A receive oldDepth D.raw
  let E := J.make issue
  let child := @externalZeroCall f ell s sel c d t W j g
  have gp : A.group=word g.val :=
    (valued_word A.group).symm.trans (congrArg word theGroup)
  let rows := (D.physicalSelected g).map D.record
  let selected := D.raw.filter (fun X=>(cmpAddr A.group X.group).result)
  have m : selected=rows := by
    change D.raw.filter (fun X=>(cmpAddr A.group X.group).result)=_
    rw [←(select_ports_exact A.group D.raw).1,gp]
    exact D.physical_port_select g
  have e : rows.length=child.edges := by
    unfold rows
    rw [List.length_map]
    exact physical_count_of_external sel d t D W j g
  have hDepth : oldDepth.val+1=child.depth :=
    (congrArg (·+1) old)
  have l := literal_header_exact (b:=b) A D.raw receive oldDepth issue depPos
    (by rw [old]; exact depFit) edgePos (show selected.length<2^b by rwa [m,e])
  obtain ⟨who,content,tag⟩ := l
  change E.result.bytes=A.bytes++childHeaderBytes receive (word (q:=dep) (oldDepth.val+1))
      (word (q:=b) selected.length) (selected.flatMap rowBytes) at content
  rw [hDepth,m,e] at content
  exact ⟨who,content,tag,recv,theCentre,theProbe,theGroup⟩
end Native

#print axioms physical_count_of_external
#print axioms external_child_port_count
#print axioms make_external_header_exact
end J6R32RootGeneratedRegistryInputs
