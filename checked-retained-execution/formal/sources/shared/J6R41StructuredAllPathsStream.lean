import J6R41StructuredAllPathsLocal
import J6R41StructuredAllPathsRoot
import J6R32StatefulArithmeticPath

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 14000000
set_option maxRecDepth 3200

/-! A link is an equality about actual finite bytes at two adjacent
stages. It says the next raw physical file copied the body from the
same actual previously framed half-occurrence and side. No semantic
leaf correctness, trace, or routing oracle is a field. The next
chart's address and group words remain those of its NativeJob. -/
namespace J6R41StructuredAllPaths
open scoped Polynomial Classical
open Polynomial J6R21Ancestor J6R34ChildPath J6R26DescriptorTree J6R15ModeCost
open J6R36ChildFramedRoute J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted
open J6ActiveRun J6R24MeteredRecursion J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R25PreparedSupply J6R30ProducedGateRegistry

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
variable (born : Births T key prec tw bw page)

abbrev PageKeys (_born : Births T key prec tw bw page) :=
  ∀ {c : Call (PhysicalHost f ell)} (p : Path sel r c) (w : (Plan sel).Slot c),
    PageAt T (p.ticket w)→Word page

variable (keys : PageKeys born)
variable (rootTags : r.host.Row⊕r.host.Col→Origin key prec page)

noncomputable def expectedOrigin :
    {c : Call (PhysicalHost f ell)}→Path sel r c→c.host.Row⊕c.host.Col→Origin key prec page
  | _,.root,u => rootTags u
  | _,.step p w,u =>
    match childVertices T (p.ticket w) u with
    | .inl old=> expectedOrigin p old.val
    | .inr k=>⟨(born p w).job.immutable.payload.stamp,some (keys p w k)⟩

abbrev SiteFiles :=
  ∀ {c : Call (PhysicalHost f ell)} (p : Path sel r c) (w : (Plan sel).Slot c),
    SiteInputs (born p w) (expectedOrigin born keys rootTags p)

variable {born keys rootTags}
variable (files : SiteFiles born keys rootTags)
variable (rootPorts : Port r.host.Edge→Payload key prec page)

noncomputable def publishedPayload :
    {c : Call (PhysicalHost f ell)}→Path sel r c→Port c.host.Edge→Payload key prec page
  | _,.root,h => rootPorts h
  | _,.step p w,h =>
    lanePayload ((files p w).issuedLane (childHalves T (p.ticket w) (edge h)) (side h))

structure Linked : Prop where
  canonicalPages : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel r c) (w : (Plan sel).Slot c),
    (files p w).pageKey=keys p w
  copiedBody : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel r c) (w : (Plan sel).Slot c)
    (h : Port c.host.Edge),((born p w).native.physical.record h).body=(publishedPayload files rootPorts p h).2

theorem expected_old_origin {c : Call (PhysicalHost f ell)}
    (p : Path sel r c) (w : (Plan sel).Slot c)
    (u : (p.ticket w).child.host.Row⊕(p.ticket w).child.host.Col)
    (old : OldAt T (p.ticket w)) (h : childVertices T (p.ticket w) u=.inl old) :
    expectedOrigin born keys rootTags (.step p w) u=expectedOrigin born keys rootTags p old.val := by
  rw [expectedOrigin,h]

theorem expected_new_origin {c : Call (PhysicalHost f ell)} (p : Path sel r c) (w : (Plan sel).Slot c)
    (u : (p.ticket w).child.host.Row⊕(p.ticket w).child.host.Col)
    (k : PageAt T (p.ticket w)) (h : childVertices T (p.ticket w) u=.inr k)
    (L : Linked files rootPorts) :
    expectedOrigin born keys rootTags (.step p w) u=nativeOrigin (files p w) k := by
  rw [expectedOrigin,h,nativeOrigin,L.canonicalPages]

theorem published_step_is_actual_issue {c : Call (PhysicalHost f ell)} (p : Path sel r c) (w : (Plan sel).Slot c)
    (h : Port (p.ticket w).child.host.Edge) :
    let x := childHalves T (p.ticket w) (edge h)
    let S := files p w
    S.inWrite (S.frame x) ∧
      publishedPayload files rootPorts (.step p w) h=lanePayload (S.issuedLane x (side h)) ∧
      S.write.result.header=(born p w).job.entry.result :=
  ⟨same_selected_half_written _ _,rfl,(true_site_issuance _).1⟩

#print axioms expected_old_origin
#print axioms expected_new_origin
#print axioms published_step_is_actual_issue
end J6R41StructuredAllPaths