import J6R51PeakOnlineDirectory
import J6R51PeakSidecar

/-! The actual R26 entry writer takes two-ported parent words and
one genuinely selected child record per edge. Its bit-scans, word
increments, and serialization are bounded from those data, not
assumed as another per-address fee promise. -/
namespace J6R57ScopeFee
open scoped Polynomial BigOperators Classical
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R21Ancestor J6R25PreparedSupply J6R26DescriptorTree
open J6ActiveRun J6ActiveSchedule J6R12Blueprint J6R11Blueprint J1PPrinted J6R16ModeCost
open J6R10Repack J6R24MeteredRecursion J6R34ChildPath
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R48DFS J6R49DFS J6R50SourceProducer J6R50Peak J6R51Peak J6R51Online
open J6R25PreparedSupply J6R41StructuredAllPaths J6R36ChildFramedRoute
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 24000000
set_option maxRecDepth 4800
set_option Elab.async false
noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "P" => (Plan sel)
local notation "L" => (PageBank f ell key prec tw bw page)

def entryGeometry (parentEdges childEdges fixed addr body key : ℕ) : ℕ :=
  3+(2*parentEdges)*(2*addr+3*body+81)+(fixed+3+childEdges*(13*fixed+8))+4+
  (13*fixed+4)+(2+childEdges*(6*(addr+body)+5))+
  (6*fixed+3*(childEdges*(addr+body))+2*key+9)+6+
  (3*(fixed+childEdges*(addr+body))+1)+3*fixed+5

theorem descriptor_writer_exact_charge {port edge dep prec key : ℕ}
    (J : J6R26DescriptorTree.Job port edge dep prec) (iss : Meter (Word key)) :
    (J.make iss).steps=(childStage (b:=edge) iss J.group J.precision J.parentDepth J.ports).steps+
      (3*(J.make iss).result.bytes.length+1)+3*J.coordinates.length+5 := by
  let old := childStage (b:=edge) iss J.group J.precision J.parentDepth J.ports
  have hLen : (J.coordinates++old.result.bytes).length=(J.make iss).result.bytes.length :=
    congrArg List.length (J.make_bytes iss).symm
  change old.steps+(copyBytes (J.coordinates++old.result.bytes)).steps+3*J.coordinates.length+5=_
  rw [copyBytes_exact,hLen]

theorem actual_born_entry_geometry {v : Ticket sel r}
    (B : Birth T v key prec tw bw page) (fixed addr body : ℕ)
    (hFixed : fixedWords B≤fixed) (hAddr : B.port+6≤addr)
    (hBody : ∀ row∈B.native.physical.raw,row.body.length≤body)
    (hRows : B.native.physical.raw.length=2*v.parent.edges) :
    B.job.entry.steps≤B.issuance.steps+entryGeometry v.parent.edges v.child.edges fixed addr body key := by
  let D := B.native
  let G := childPortsWithCount (b:=B.edge) D.gWord D.physical.raw
  let S := selectedSourceRows B
  let stage := childStage (b:=B.edge) B.issuance D.gWord D.receiving D.oldDepth D.physical.raw
  have phase := (child_stage_exact (b:=B.edge) B.issuance D.gWord D.receiving D.oldDepth D.physical.raw).2.2
  change stage.steps=B.issuance.steps+G.steps+(increment D.oldDepth).steps+serializeFee G.result.1+
    (6*(prec+B.dep+B.edge)+3*(G.result.1.flatMap rowBytes).length+2*key+9)+6 at phase
  have gWord : D.gWord=word v.groupAt.val :=
    (valued_word D.gWord).symm.trans (congrArg word D.gExact)
  have counted := D.physical.true_child_port_tape (b:=B.edge)
    D.edgePos v.groupAt v.probeAt v.modeAt D.edgeFit
  rw [←gWord] at counted
  have groupRows : G.result.1=S := counted.1
  have groupCost : G.steps=3+(D.physical.raw.map rowScanFee).sum+
       (B.edge+3+v.child.edges*(13*B.edge+8))+4 := counted.2.2
  have src : D.physical.raw=D.physical.order.map D.physical.record := D.physical.source
  have goodS (row : PortRow B.port) (h : row∈S) : row.body.length≤body := by
    obtain ⟨x,hx,e⟩ := List.mem_map.mp h
    apply hBody row
    rw [src]
    exact List.mem_map.mpr ⟨x,D.physical.complete x,e⟩
  have wordFix : prec+B.dep+B.edge≤fixed := by
    unfold fixedWords at hFixed
    omega
  have coordinateFix : D.coordinates.length≤fixed := by
    rw [D.address_field_width]
    unfold fixedWords at hFixed
    omega
  have edgeFix : B.edge≤fixed := by omega
  have depthFix : B.dep≤fixed := by omega
  have scan : (D.physical.raw.map rowScanFee).sum≤(2*v.parent.edges)*(2*addr+3*body+81) := by
    change D.physical.raw.length=_ at hRows
    rw [←hRows]
    refine uniform_sum_bound _ _ _ (fun x hx=>?_)
    have hh := hBody x hx
    unfold rowScanFee
    omega
  have countMul : v.child.edges*(13*B.edge+8)≤v.child.edges*(13*fixed+8) :=
    Nat.mul_le_mul_left _ (by omega)
  have graph : G.steps≤3+(2*v.parent.edges)*(2*addr+3*body+81)+
       (fixed+3+v.child.edges*(13*fixed+8))+4 := by
    rw [groupCost]
    omega
  have depth : (increment D.oldDepth).steps≤13*fixed+4 := by
    have valid : D.oldDepth.val+1<2^B.dep := by rw [D.depthExact]; exact D.depthFit
    rw [(increment_exact D.depthPos D.oldDepth valid).2]
    omega
  have selectLen : S.length=v.child.edges := native_header_count_is_actual_child B
  have linear : ∀ row∈S,B.port+6+row.body.length≤addr+body :=
    fun x hx=>Nat.add_le_add hAddr (goodS x hx)
  have wires : (G.result.1.flatMap rowBytes).length≤v.child.edges*(addr+body) := by
    rw [groupRows,encoded_rows_exact,←selectLen]
    exact uniform_sum_bound _ _ _ linear
  have serial : serializeFee G.result.1≤2+v.child.edges*(6*(addr+body)+5) := by
    rw [groupRows,serializeFee,←selectLen]
    exact Nat.add_le_add_left (uniform_sum_bound _ _ _ (fun x hx=>by
      have h := linear x hx
      omega)) _
  have entryBytes : B.job.entry.result.bytes.length≤fixed+v.child.edges*(addr+body) :=
    actual_child_header_width B fixed addr body hFixed hAddr goodS
  have entry := descriptor_writer_exact_charge D.job B.issuance
  change B.job.entry.steps=stage.steps+(3*B.job.entry.result.bytes.length+1)+
    3*D.coordinates.length+5 at entry
  rw [entry,phase,entryGeometry]
  omega

theorem actual_online_entry_ceiling
    (M : OnlineMachine T key prec tw bw page q) (fixed addr seed : ℕ)
    (sizes : EntryWidths M fixed addr) (boot : BootBodyWidth M seed)
    (p : Path sel r c) (w : (P).Slot c) :
    let B := borns M p w
    B.job.entry.steps≤B.issuance.steps+
      entryGeometry c.edges (p.ticket w).child.edges fixed addr (sourceBodyCap s C seed) key := by
  let X := sourceState M p w
  let B := X.birth
  have rawLen : B.native.physical.raw.length=2*c.edges := by
    have h := (actual_addon_tapes_count_both_half_ports X.site).1
    rw [X.site.aligned,List.length_map] at h
    change B.native.physical.order.length=2*c.edges at h
    rw [B.native.physical.source,List.length_map,h]
  have bodies : ∀ x∈B.native.physical.raw,x.body.length≤sourceBodyCap s C seed := by
    intro x hx
    rw [B.native.physical.source] at hx
    obtain ⟨h,_,e⟩ := List.mem_map.mp hx
    rw [←e]
    exact actual_demanded_body_fits M seed boot p w h
  exact actual_born_entry_geometry B fixed addr (sourceBodyCap s C seed) (sizes p w).1 (sizes p w).2 bodies rawLen

end
#print axioms descriptor_writer_exact_charge
#print axioms actual_born_entry_geometry
#print axioms actual_online_entry_ceiling
end J6R57ScopeFee
