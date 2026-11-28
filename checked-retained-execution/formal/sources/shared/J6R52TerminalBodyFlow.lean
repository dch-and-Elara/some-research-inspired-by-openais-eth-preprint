import J6R51OnlineCore
import J6R41StructuredAllPathsInduct
import J6R34ChildPathChart

/-! Link the actual online publication driver to the true incoming
retained bodies. There is no all-path lineage table parameter:
after the real exterior base anchors, successive links are the
verified copies produced by the actual demand operation. -/
namespace J6R52Terminal
open scoped Polynomial
open Polynomial AOracleMachineTime J6R21Ancestor J6R15ModeCost
open J6R26DescriptorTree J6R34ChildPath J6R41StructuredAllPaths
open J6R33StatefulArithmeticPage J6R36ChildFramedRoute J6R10Repack J6R11Blueprint
open J6R12Blueprint J1PPrinted J6R24MeteredRecursion J6ActiveRun J6R32StatefulArithmetic
open J6R50SourceProducer J6R51Online
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 21000000
set_option maxRecDepth 3800
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page rate : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
variable (M : OnlineMachine T key prec tw bw page rate)
variable (tags : r.host.Row⊕r.host.Col→Origin key prec page)
variable (ports : Port r.host.Edge→Payload key prec page)
variable (bootTags : ∀ w,(M.initial w).result.origins=tags)
variable (bootBody : ∀ w h,((M.initial w).result.birth.native.physical.record h).body=(ports h).2)

def fromOnline : LiveProducer T (tw:=tw) (bw:=bw) tags ports where
  start w := (M.initial w).result
  startOrigins := bootTags
  startBody := bootBody
  advance site w := (M.demand site w).result.advance

theorem generated_site_has_no_lineage_table :
    ∀ {c : Call (PhysicalHost f ell)} (p : Path sel r c) (w : (Plan sel).Slot c),
      buildAlong (fromOnline M tags ports bootTags bootBody) p w=sourceState M p w := by
  intro c p
  induction p with
  | root => intro w; rfl
  | step p x ih =>
    intro w
    rw [buildAlong,ih x]
    all_goals rfl

structure IncomingProof {v : Ticket sel r}
    (site : StoredSite T v key prec tw bw page)
    (u : v.parent.host.Row⊕v.parent.host.Col) where
  source : Point f ell
  seed : PortAt source→List Bool
  trace : Trace source (point v.parent.host u)
  tag : Origin key prec page
  actualTag : site.origins u=tag
  actualBody : ∀ x : PortAt (point v.parent.host u),
    (site.birth.native.physical.record x.val).body=trace.literal seed x

include bootTags bootBody in
theorem actual_online_incoming_proof
    (base : ∀ (u : r.host.Row⊕r.host.Col) (h : PortAt (point r.host u)),(ports h.val).1=tags u)
    {c : Call (PhysicalHost f ell)} (p : Path sel r c) (w : (Plan sel).Slot c)
    (u : c.host.Row⊕c.host.Col) :
    Nonempty (IncomingProof (sourceState M p w) u) := by
  let L := fromOnline M tags ports bootTags bootBody
  let D := buildAlong L p w
  have same : D=sourceState M p w := generated_site_has_no_lineage_table M tags ports bootTags bootBody p w
  have lines := linked_paths_use_original_payload (files L) ports
    (online_paths_have_no_supplied_link_table L) base p u
  have body (p0 : Port c.host.Edge) :
      (D.birth.native.physical.record p0).body=(publishedPayload (files L) ports p p0).2 :=
    (online_paths_have_no_supplied_link_table L).copiedBody p w p0
  have tag := congrFun (built_origin_table_is_the_actual_path L p w) u
  suffices e : Nonempty (IncomingProof D u) from same ▸ e
  rcases lines with root|inner
  · obtain ⟨a,tr,actualTag,actualBody⟩ := root
    refine ⟨⟨point r.host a,(fun x=>(ports x.val).2),tr,tags a,tag.trans actualTag,?_⟩⟩
    intro p0
    exact (body p0.val).trans (congrArg Prod.snd (actualBody p0))
  · obtain ⟨start,path,slot,k,_,tr,actualTag,actualBody⟩ := inner
    refine ⟨⟨bornPoint T (path.ticket slot) k, originSeed (layout T (path.ticket slot))
      (axis T (path.ticket slot)) (path.ticket slot).groupAt k,tr,
      nativeOrigin (files L path slot) k,tag.trans actualTag,?_⟩⟩
    intro p0
    exact (body p0.val).trans (congrArg Prod.snd (actualBody p0))

end
#print axioms generated_site_has_no_lineage_table
#print axioms actual_online_incoming_proof
end J6R52Terminal
