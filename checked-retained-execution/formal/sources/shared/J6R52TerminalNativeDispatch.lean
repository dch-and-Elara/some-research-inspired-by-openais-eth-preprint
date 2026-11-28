import J6R52TerminalNativeRow
import J6R49SourceLayoutFrames

/-! The actual old physical row either has original exterior provenance,
or the native job path constructs and reads its correct leaf command.
In the native branch there is no caller-supplied per-row trace or
semantics hypothesis. The exterior branch is intentionally explicit. -/
namespace J6R52Terminal
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R26DescriptorTree J6R34ChildPath J6R41StructuredAllPaths
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R36ChildFramedRoute J6R22Active
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion J6ActiveRun
open J6R50SourceProducer J6R50Leaf J6R51Online J6R51ParentFrames J6R49SourceLayout
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 30000000
set_option maxRecDepth 4200
set_option Elab.async false

theorem literal_row_value_transport {f : ℤ[X]} {ell p M : ℕ} (hf : f.Monic)
    (H K : PhysicalHost f ell) (same : H=K) (row : H.Row)
    (ord : Fin M≃H.Edge) (bits : Fin M→Bool) :
    let idx := (Equiv.cast (congrArg PhysicalHost.Row same)) row
    let old := (Sum.inl idx : K.Row⊕K.Col)
    let o := ord.trans (Equiv.cast (congrArg PhysicalHost.Edge same))
    (K.file old).read hf p (assignment K.network (bits∘o.symm) old)=
      (H.file (.inl row)).read hf p (assignment H.network (bits∘ord.symm) (.inl row)) := by
  subst K
  rfl

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page rate : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
variable (M : OnlineMachine T key prec tw bw page rate)

theorem actual_online_old_row_evaluator_or_exterior
    (tags : r.host.Row⊕r.host.Col→J6R36ChildFramedRoute.Origin key prec page)
    (ports : Port r.host.Edge→Payload key prec page)
    (bootTags : ∀ w,(M.initial w).result.origins=tags)
    (bootBody : ∀ w h,((M.initial w).result.birth.native.physical.record h).body=(ports h).2)
    (base : ∀ (u : r.host.Row⊕r.host.Col) (h : PortAt (point r.host u)),(ports h.val).1=tags u)
    {c : Call (PhysicalHost f ell)} (p : Path sel r c) (w : (Plan sel).Slot c)
    (row : (p.ticket w).child.host.Row)
    (saved : CachedParentFrames (sourceState M p w).site)
    (inj : Function.Injective (sourceState M p w).site.oldKey)
    (rootLive : PageBank f ell key prec tw bw page→Prop)
    (B : PageBank f ell key prec tw bw page) (live : opened (borns M) rootLive p B)
    (F : Frame f (p.ticket w).child.prec) (bits : Fin (p.ticket w).child.edges→Bool) :
    let v := p.ticket w
    let site := sourceState M p w
    let u := physicalChildRows (T:=T) (v:=v) row
    let op := compileKeptPage (site.site.oldKey u.val) (site.origins u.val)
      (cachedBook site saved).result saved.rows
    let order := actualEdgeOrder T v site.birth.native.physical
    Nonempty (ExteriorOrigin M tags ports p w u.val) ∨
      ∃ cmd,op.result=some cmd ∧
        F.decode ((cmd : ReadCmd key page).read hf F T.vPositive B (List.ofFn bits)).result=
          (v.child.host.file (.inl row)).read hf v.child.prec
            (assignment v.child.host.network (bits∘order.symm) (.inl row)) := by
  let v := p.ticket w
  let site := sourceState M p w
  let u := physicalChildRows (T:=T) (v:=v) row
  let order := actualEdgeOrder T v site.birth.native.physical
  rcases actual_online_origin_and_native_key M tags ports bootTags bootBody base p w u.val with ext|inner
  · exact Or.inl ext
  · obtain ⟨A⟩ := inner
    obtain ⟨cmd,eq,value⟩ := actual_compiled_native_ancestor_page M p w u A saved inj rootLive B live F bits
    have transport := literal_row_value_transport (p:=v.child.prec) hf v.child.host
      (literalHost T v) (actual_ticket_host T v) row order bits
    exact Or.inr ⟨cmd,eq,value.trans transport⟩
end
#print axioms literal_row_value_transport
#print axioms actual_online_old_row_evaluator_or_exterior
end J6R52Terminal
