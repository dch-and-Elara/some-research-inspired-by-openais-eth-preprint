import J6R25PreparedSupplyPorts
import J6R12BlueprintReach

/-! The emitted byte rows are the independent half-ports in the same
actual packet child host, not merely a smaller graph with the same bound.
This consumes a resident encoding of the parent half-ports and
their literal group labels. It does not build the whole parent layout. -/
namespace J6R25PreparedSupply
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6ActiveRun J6R10Reachable J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted
open P11FullPacking

variable {f : ℤ[X]} {ell s : ℕ}
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
variable {c : Call (PhysicalHost f ell)}
variable (d : J6R12Blueprint.Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c)
variable (t : Center (printedParams (f:=f) (ell:=ell) s) c)

noncomputable def physicalGroup (p : Port c.host.Edge) : Fin 64 := by
  letI := c.host.finiteEdge
  letI := c.host.finiteRow
  letI := c.host.finiteCol
  exact retainedGroup c.host.network (atGroup (packing sel d) (centerIndex d t)) p

structure PhysicalPorts (w : ℕ) where
  raw : List (PortRow w)
  order : List (Port c.host.Edge)
  nodup : order.Nodup
  complete : ∀ p,p∈order
  record : Port c.host.Edge→PortRow w
  source : raw=order.map record
  labelled : ∀ p,(record p).group.val=(physicalGroup sel d t p).val
  distinct : Function.Injective (fun p=>(record p).address)

namespace PhysicalPorts

variable {sel d t} {w : ℕ} (D : PhysicalPorts sel d t w)

theorem physical_record_hits (g : Fin 64) (p : Port c.host.Edge) :
    (cmpAddr (word g.val) (D.record p).group).result=true ↔ physicalGroup sel d t p=g := by
  have hc : (word (q:=6) g.val).val=g.val := word_val g.isLt
  rw [(cmpAddr_exact _ _).1]
  constructor
  · intro e
    exact Fin.ext ((D.labelled p).symm.trans ((congrArg Word.val e).symm.trans hc))
  · intro eq
    have h := (D.labelled p).trans ((congrArg Fin.val eq).trans hc.symm)
    exact (valued_word (word g.val)).symm.trans ((congrArg word h.symm).trans (valued_word _))

noncomputable def physicalSelected (g : Fin 64) : List (Port c.host.Edge) :=
  D.order.filter (fun p=>decide (physicalGroup sel d t p=g))

theorem physical_port_select (g : Fin 64) :
    (selectPorts (word g.val) D.raw).result=(D.physicalSelected g).map D.record := by
  rw [(select_ports_exact _ _).1,D.source,List.filter_map]
  unfold physicalSelected
  congr 1
  apply List.filter_congr
  intro p _
  exact Bool.eq_iff_iff.mpr (by
    rw [decide_eq_true_eq]
    exact D.physical_record_hits g p)

set_option maxHeartbeats 2500000 in
theorem physical_count_is_child (g : Fin 64) (z : Probe S c) (β : NativeMenu (N sel) c t) :
    (D.physicalSelected g).length=((Plan sel).child c ⟨⟨t,z,β,g⟩,d.active⟩).edges := by
  classical
  let h (p : Port c.host.Edge) := physicalGroup sel d t p=g
  let O := D.physicalSelected g
  have hD : O.Nodup := D.nodup.filter _
  letI := c.host.finiteEdge
  letI := c.host.finiteRow
  letI := c.host.finiteCol
  have hSet : O.toFinset=(Finset.univ : Finset (Port c.host.Edge)).filter h := by
    ext p
    simp only [O,physicalSelected,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,Finset.mem_filter,
      Finset.mem_univ,true_and,D.complete,h]
  let W : NativeAddress (N sel) c := ⟨t,z,β,g⟩
  rw [child_exact sel d W]
  change O.length= (packetOfSite sel d t z (siteTuple sel d W) g).edgeCount
  rw [←List.toFinset_card_of_nodup hD,hSet,←Fintype.card_subtype]
  rfl

set_option maxHeartbeats 3000000 in
theorem true_child_port_tape {b : ℕ} (hb : 0<b) (g : Fin 64) (z : Probe S c)
    (β : NativeMenu (N sel) c t)
    (fit : ((Plan sel).child c ⟨⟨t,z,β,g⟩,d.active⟩).edges<2^b) :
    let R := childPortsWithCount (b:=b) (word g.val) D.raw
    R.result.1=(D.physicalSelected g).map D.record ∧
    R.result.2.val=((Plan sel).child c ⟨⟨t,z,β,g⟩,d.active⟩).edges ∧
    R.steps=3+(D.raw.map rowScanFee).sum+
      (b+3+((Plan sel).child c ⟨⟨t,z,β,g⟩,d.active⟩).edges*(13*b+8))+4 := by
  let Nxt := ((Plan sel).child c ⟨⟨t,z,β,g⟩,d.active⟩).edges
  have hL : (selectPorts (word g.val) D.raw).result.length=Nxt := by
    rw [D.physical_port_select g,List.length_map,D.physical_count_is_child g z β]
  have hFit : ((D.raw).filter (fun row=>(cmpAddr (word g.val) row.group).result)).length<2^b := by
    rw [←(select_ports_exact _ _).1,hL]
    exact fit
  obtain ⟨_,hCount,hC⟩ := ports_counted hb (word g.val) D.raw hFit
  have hWidth : (childPortsWithCount (b:=b) (word g.val) D.raw).result.1.length=Nxt := hL
  exact ⟨D.physical_port_select g,hCount.trans hWidth,hC.trans (by rw [hWidth])⟩

#print axioms physical_record_hits
#print axioms physical_port_select
#print axioms physical_count_is_child
#print axioms true_child_port_tape
end PhysicalPorts
end J6R25PreparedSupply


