import J6R41StructuredAllPathsStream

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 15000000
set_option maxRecDepth 3600

/-! The adjacent-byte equality, together with the old typed receipt,
is sufficient for the *actual new published row* to have the correct
body. There is no premise about the sought child body. New native
pages start from their own paid creation record. -/
namespace J6R41StructuredAllPaths
open scoped Polynomial Classical
open Polynomial J6R21Ancestor J6R20Ancestor J6R34ChildPath J6R26DescriptorTree J6R15ModeCost
open J6R36ChildFramedRoute J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted
open J6ActiveRun J6R24MeteredRecursion J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R25PreparedSupply J6R30ProducedGateRegistry

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
variable {born : Births T key prec tw bw page}
variable {keys : PageKeys born} {rootTags : r.host.Row⊕r.host.Col→Origin key prec page}
variable {files : SiteFiles born keys rootTags} {rootPorts : Port r.host.Edge→Payload key prec page}
variable (L : Linked files rootPorts)

include L in
theorem carried_retention_publishes_correct_body {c : Call (PhysicalHost f ell)}
    (p : Path sel r c) (w : (Plan sel).Slot c)
    (u : (p.ticket w).child.host.Row⊕(p.ticket w).child.host.Col)
    (old : OldAt T (p.ticket w)) (h : childVertices T (p.ticket w) u=.inl old)
    {ancestor : Point f ell} (seed : PortAt ancestor→List Bool)
    (tr : Trace ancestor (point c.host old.val)) (tag : Origin key prec page)
    (hTag : expectedOrigin born keys rootTags p old.val=tag)
    (earlier : ∀ x : PortAt (point c.host old.val),
      publishedPayload files rootPorts p x.val=(tag,tr.literal seed x)) :
    let E := selected_retained_chart T (p.ticket w) u old h
    let childTrace : Trace ancestor (point (p.ticket w).child.host u) :=
      E.symm ▸ tr.keep (retainedMove T (p.ticket w) old)
    expectedOrigin born keys rootTags (.step p w) u=tag ∧
      ∀ y : PortAt (point (p.ticket w).child.host u),
        publishedPayload files rootPorts (.step p w) y.val=(tag,childTrace.literal seed y) := by
  let v := p.ticket w
  let S := files p w
  let move := retainedMove T v old
  let E := selected_retained_chart T v u old h
  refine ⟨(expected_old_origin (born:=born) (keys:=keys) (rootTags:=rootTags) p w u old h).trans hTag,?_⟩
  intro y
  let z := castPort E y
  let back := move.back z
  have parentBody : ((born p w).native.physical.record back.val).body=tr.literal seed back :=
    (L.copiedBody p w back.val).trans (congrArg Prod.snd (earlier back))
  obtain ⟨_,body,origin⟩ := native_retained_body_at_issue S old tr seed z
    ((born p w).native.physical.record back.val).group parentBody
  obtain ⟨same,side⟩ := retained_chart_uses_given_half T v u old E y
  change lanePayload (S.issuedLane (childHalves T v (edge y.val)) (J6R10Repack.side y.val))=_
  rw [←same,side]
  exact Prod.ext (origin.trans hTag) (body.trans (move_cast_literal E (tr.keep move) seed y).symm)

include L in
theorem actual_new_page_publishes_correct_body {c : Call (PhysicalHost f ell)}
    (p : Path sel r c) (w : (Plan sel).Slot c)
    (u : (p.ticket w).child.host.Row⊕(p.ticket w).child.host.Col)
    (k : PageAt T (p.ticket w)) (h : childVertices T (p.ticket w) u=.inr k) :
    let v := p.ticket w
    let E := selected_packet_chart T v u k h
    let childTrace : Trace (bornPoint T v k) (point v.child.host u) := E.symm ▸ Trace.start
    expectedOrigin born keys rootTags (.step p w) u=nativeOrigin (files p w) k ∧
      ∀ y : PortAt (point v.child.host u),
        publishedPayload files rootPorts (.step p w) y.val=
          (nativeOrigin (files p w) k,childTrace.literal (originSeed (layout T v) (axis T v) v.groupAt k) y) := by
  let v := p.ticket w
  let S := files p w
  let E := selected_packet_chart T v u k h
  refine ⟨expected_new_origin files rootPorts p w u k h L,?_⟩
  intro y
  let z := castPort E y
  obtain ⟨_,body,origin,_⟩ := native_page_body_at_issue S k z (born p w).native.gWord
  obtain ⟨same,side⟩ := fresh_chart_uses_given_half T v u k E y
  change lanePayload (S.issuedLane (childHalves T v (edge y.val)) (J6R10Repack.side y.val))=_
  rw [←same,side]
  have moved := move_cast_literal E (Trace.start : Trace (bornPoint T v k) (bornPoint T v k))
    (originSeed (layout T v) (axis T v) v.groupAt k) y
  exact Prod.ext origin (body.trans moved.symm)

#print axioms carried_retention_publishes_correct_body
#print axioms actual_new_page_publishes_correct_body
end J6R41StructuredAllPaths