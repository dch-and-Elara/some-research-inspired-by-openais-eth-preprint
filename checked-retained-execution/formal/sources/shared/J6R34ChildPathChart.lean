import J6R33GeneratedChildSiteSource
import J6R21AncestorRun

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 2800
set_option maxHeartbeats 17500000

/-! Unfold one real active Appendix D slot. The exact child graph,
entry file, group and page are given by that slot; retention is not a
synthetic move to a graph that merely has the same degrees. -/
namespace J6R34ChildPath
open scoped Polynomial Classical
open Polynomial
open J6ActiveRun J6R9Recursive J6R10Reachable J6R10Repack J6R11Blueprint J6R12Blueprint
open J1PPrinted J6R16ModeCost J6R26DescriptorTree J6R24MeteredRecursion
open J6R21Ancestor J6R20Ancestor J6R9PacketScopes P11FullPacking

variable {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable (T : Prepared cfg sel r hf) (v : Ticket sel r)

local notation "SP" => printedParams (f:=f) (ell:=ell) s

abbrev layout := packing sel (ticketReady T v)
abbrev axis := centerIndex (ticketReady T v) v.centerAt
abbrev stateWidth := registerPrecision SP v.parent v.centerAt

abbrev OldAt := Old (atGroup (layout T v) (axis T v)) v.groupAt

abbrev PageAt := Page ((SP).levelBits v.parent.depth) (layout T v).copies (Fin 64)

abbrev HalfAt := ChildEdge v.parent.host.network (atGroup (layout T v) (axis T v)) v.groupAt

noncomputable abbrev exponent :=
  siteTuple sel (ticketReady T v) v.slot.val

noncomputable abbrev nativeProbe :=
  sampleNode SP f ell v.parent (ticketReady T v).fit v.centerAt v.probeAt

noncomputable abbrev literalHost :=
  packetOfSite sel (ticketReady T v) v.centerAt v.probeAt (exponent T v) v.groupAt

theorem actual_ticket_host : v.child.host=literalHost T v := by
  exact congrArg Call.host (child_exact sel (ticketReady T v) v.slot.val)

/-- The actual native child chart, not any other packing with equal
size. This is a proof-side dependent transport, with no raw lookup. -/
noncomputable def childVertices : (v.child.host.Row ⊕ v.child.host.Col) ≃ (OldAt T v ⊕ PageAt T v) :=
  Equiv.cast (congrArg (fun H : PhysicalHost f ell => H.Row ⊕ H.Col) (actual_ticket_host T v))

noncomputable def childHalves : v.child.host.Edge ≃ HalfAt T v :=
  Equiv.cast (congrArg PhysicalHost.Edge (actual_ticket_host T v))

def point (H : PhysicalHost f ell) (u : H.Row ⊕ H.Col) : Point f ell := ⟨H,u⟩

private theorem point_change_host {H K : PhysicalHost f ell} (h : H=K) (u : H.Row ⊕ H.Col) :
    point H u=point K (Equiv.cast (congrArg (fun V : PhysicalHost f ell=>V.Row⊕V.Col) h) u) := by
  subst K
  rfl

theorem actual_child_vertex_chart (u : v.child.host.Row ⊕ v.child.host.Col) :
    point v.child.host u=point (literalHost T v) (childVertices T v u) :=
  point_change_host (actual_ticket_host T v) u

private theorem transport_endpoints {H K : PhysicalHost f ell} (h : H=K) (u : H.Edge) :
    Equiv.cast (congrArg (fun V : PhysicalHost f ell=>V.Row⊕V.Col) h) (.inl (H.network.row u))=
      .inl (K.network.row (Equiv.cast (congrArg PhysicalHost.Edge h) u)) ∧
    Equiv.cast (congrArg (fun V : PhysicalHost f ell=>V.Row⊕V.Col) h) (.inr (H.network.col u))=
      .inr (K.network.col (Equiv.cast (congrArg PhysicalHost.Edge h) u)) := by
  subst K
  exact ⟨rfl,rfl⟩

theorem actual_child_half_endpoints (u : v.child.host.Edge) :
    childVertices T v (.inl (v.child.host.network.row u))=
      .inl ((child v.parent.host.network (atGroup (layout T v) (axis T v))
        (atPacket (layout T v)) v.groupAt).row (childHalves T v u)) ∧
    childVertices T v (.inr (v.child.host.network.col u))=
      .inr (atPacket (layout T v) (edge (childHalves T v u).val)) :=
  transport_endpoints (actual_ticket_host T v) u

/-- The retained move uses the actual source siblings and their
creation precision, so its destination host is precisely the native
child, not even a replacement sibling file with same retained entry. -/
noncomputable def retainedMove (u : OldAt T v) :
    Move (point v.parent.host u.val) := by
  letI := v.parent.host.finiteEdge
  letI := v.parent.host.finiteRow
  letI := v.parent.host.finiteCol
  let p := stateWidth v
  let P := layout T v
  let i := axis T v
  let g := v.groupAt
  exact ⟨Fin 64,PageAt T v,inferInstance,inferInstance,atGroup P i,atPacket P,g,u.property,p,
    compiledPacket P i g p (actualPacket P i (centerNonzero v.centerAt) rfl p
      (J6R10Integral.box_two_nil p f ell) (nativeProbe T v) (exponent T v) g)⟩

theorem actual_retained_point (u : OldAt T v) :
    (retainedMove T v u).next=point (literalHost T v) (.inl u) := rfl

theorem actual_retained_port (u : OldAt T v) (x : PortAt (retainedMove T v u).next) :
    side x.val=false ∧
      ((retainedMove T v u).back x).val=(edge x.val).val ∧
      (entry (retainedMove T v u).next).created=(v.parent.host.file u.val).created :=
  ⟨(retainedMove T v u).side_left x,(retainedMove T v u).back_val x,rfl⟩

noncomputable def bornPoint (k : PageAt T v) : Point f ell :=
  point (literalHost T v) (.inr k)

theorem actual_fresh_point (k : PageAt T v) :
    letI := v.parent.host.finiteEdge
    letI := v.parent.host.finiteRow
    letI := v.parent.host.finiteCol
    bornPoint T v k=generatedPoint (layout T v) (axis T v)
      (centerNonzero v.centerAt) rfl (nativeProbe T v) v.parent.host.file (exponent T v)
      v.groupAt k := rfl

theorem actual_fresh_port (k : PageAt T v) (x : PortAt (bornPoint T v k)) :
    side x.val=true ∧
      (atPacket (layout T v) (edge (edge x.val).val))=k ∧
      (entry (bornPoint T v k)).created=v.child.prec := by
  obtain ⟨x,h⟩ := x
  cases x with
  | inl e => cases h
  | inr e =>
    refine ⟨rfl,?_,rfl⟩
    exact Sum.inr.inj h

#print axioms actual_ticket_host
#print axioms actual_child_vertex_chart
#print axioms actual_child_half_endpoints
#print axioms actual_retained_point
#print axioms actual_retained_port
#print axioms actual_fresh_point
#print axioms actual_fresh_port
end J6R34ChildPath
