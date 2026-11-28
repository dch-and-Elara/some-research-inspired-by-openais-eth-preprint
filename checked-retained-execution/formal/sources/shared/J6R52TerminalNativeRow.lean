import J6R52TerminalAncestorOrigin
import J6R52TerminalAncestorRead
import J6R52TerminalAncestorFrames

/-! An inherited native Page, even after an arbitrary number of real
retentions, is read from the exact scoped producer selected by the
online trace and not by a supplied Gate-value or chart equality. -/
namespace J6R52Terminal
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R26DescriptorTree J6R34ChildPath J6R41StructuredAllPaths
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R36ChildFramedRoute J6R22Active
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion J6ActiveRun
open J6R50SourceProducer J6R50Leaf J6R51Online J6R51ParentFrames
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 26000000
set_option maxRecDepth 4200
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page rate : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
variable (M : OnlineMachine T key prec tw bw page rate)

theorem actual_compiled_native_ancestor_page
    {c : Call (PhysicalHost f ell)} (p : Path sel r c) (w : (Plan sel).Slot c)
    (u : OldAt T (p.ticket w))
    (A : AncestorOrigin M p w u.val)
    (saved : CachedParentFrames (sourceState M p w).site)
    (inj : Function.Injective (sourceState M p w).site.oldKey)
    (rootLive : PageBank f ell key prec tw bw page→Prop)
    (B : PageBank f ell key prec tw bw page) (live : opened (borns M) rootLive p B)
    (F : Frame f (p.ticket w).child.prec) (bits : Fin (p.ticket w).child.edges→Bool) :
    let v := p.ticket w
    let site := sourceState M p w
    let op := compileKeptPage (site.site.oldKey u.val) (site.origins u.val)
      (cachedBook site saved).result saved.rows
    let cur := (retainedMove T v u).next
    let ord := retainedEdgeOrder T v site.birth.native.physical u
    ∃ cmd,op.result=some cmd ∧
      F.decode ((cmd : ReadCmd key page).read hf F T.vPositive B (List.ofFn bits)).result=
      (entry cur).read hf v.child.prec
        (assignment cur.host.network (bits∘ord.symm) cur.vertex) := by
  let v := p.ticket w
  let site := sourceState M p w
  let source := sourceState M A.atHome A.slot
  let whereBorn := A.atHome.ticket A.slot
  let seed := originSeed (layout T whereBorn) (axis T whereBorn) whereBorn.groupAt A.pageId
  let pg := J6R49SourceLayout.occurrencePageWord source.input A.pageId
  let tr := A.trace.keep (retainedMove T v u)
  let ports := keptPorts T v site.birth.native.physical u
  let ord := retainedEdgeOrder T v site.birth.native.physical u
  let wires : List WireRead := ports.map (fun h=>⟨tr.literal seed h,List.replicate (ord.symm (edge h.val)).val true⟩)
  have marker : ∀ x,∃ rest,seed x=true::rest := by
    intro x
    exact ⟨_,originSeed_right (layout T whereBorn) (axis T whereBorn) whereBorn.groupAt A.pageId x⟩
  have hp : (site.origins u.val).pageKey=some pg := congrArg J6R36ChildFramedRoute.Origin.pageKey A.tag
  have stamp := congrArg Stamp.creator (full_native_creation_stamp source.birth)
  have baked : (site.origins u.val).stamp.creator=source.birth.job.identifier := by
    have e := congrArg (fun x : J6R36ChildFramedRoute.Origin key prec page => x.stamp.creator) A.tag
    exact (e.trans stamp.symm).trans source.birth.tag.1.symm
  have made := (compiled_retained_page_from_actual_fields site saved inj u A.trace seed marker A.body pg hp).1
  let issued := retainedSourceDepth site u A.trace
  let cmd : ReadCmd key page := .packet source.birth.job.identifier pg issued wires
  change (compileKeptPage (site.site.oldKey u.val) (site.origins u.val) (cachedBook site saved).result saved.rows).result=
    some (ReadCmd.packet (site.origins u.val).stamp.creator pg issued wires) at made
  rw [baked] at made
  have value := real_compiled_inherited_read T whereBorn source.input A.pageId p (borns M) A.own
    rootLive B live F tr ord bits ports (kept_ports_exact T v site.birth.native.physical u).2
  change F.decode ((ReadCmd.packet source.birth.job.identifier pg tr.depth wires).read hf F T.vPositive B
    (List.ofFn bits)).result=_ at value
  refine ⟨cmd,made,?_⟩
  change F.decode ((ReadCmd.packet source.birth.job.identifier pg issued wires).read hf F T.vPositive B
    (List.ofFn bits)).result=_
  by_cases notWired : ports.isEmpty=true
  · have z : ports=[] := List.isEmpty_iff.mp notWired
    have noWire : wires=[] := by simp only [wires,z,List.map_nil]
    rw [noWire] at value ⊢
    exact (congrArg (fun z=>F.decode z.result)
      (empty_leaf_page_ignores_depth hf F T.vPositive B source.birth.job.identifier pg issued tr.depth
        (List.ofFn bits))).trans value
  · have nz : issued=tr.depth := by
      unfold issued retainedSourceDepth
      exact if_neg notWired
    rw [nz]
    exact value
end
#print axioms actual_compiled_native_ancestor_page
end J6R52Terminal
