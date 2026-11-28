import J6R52TerminalAncestorFrames
import J6R35RootOriginsReader

/-! The retained Page may be born in the genuine printed exterior,
not in a deeper online ticket. It uses that same paid exterior header
and widened Page. The native terminal emitter is reused without new
command words or a specified depth input. -/
namespace J6R53TerminalExterior
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6Mesh J6OrientedHost J6R35RootOrigins J6R34RootAtlas J6R31RootResidentTables
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R32RootGeneratedRegistryInputs
open J6R26DescriptorTree J6R34ChildPath J6R36ChildFramedRoute
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R22Active J6R24MeteredRecursion
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun
open J6R50SourceProducer J6R50Leaf J6R51ParentFrames J6R52Terminal
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 36000000
set_option maxRecDepth 4800
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q r c d edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q r c d edgew tc tj key prec tw bw)
variable {pad s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable {v : Ticket sel (exteriorChild G ell X.centre X.sample X.group)}

theorem actual_cached_exterior_page_read
    (site : StoredSite T v key prec tw bw (pageKeyWidth m+pad)) (saved : CachedParentFrames site.site)
    (inj : Function.Injective site.site.oldKey) (u : OldAt T v) (k : CanonicalPage m)
    (trace : Trace (stableBorn X k) (J6R34ChildPath.point v.parent.host u.val))
    (actualTag : site.origins u.val=⟨(X.seed pad).immutable.payload.stamp,
      some (widened pad (residentPageKey m k)).result⟩)
    (actualBody : ∀ p : PortAt (J6R34ChildPath.point v.parent.host u.val),
      (site.birth.native.physical.record p.val).body=trace.literal (originSeed (rootChart P) (oddAxis m) X.group k) p)
    (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad)) (live : IsLive (X.seed pad) B)
    (F : Frame f v.child.prec) (bits : Fin v.child.edges→Bool) :
    let op := compileKeptPage (site.site.oldKey u.val) (site.origins u.val)
      (cachedBook site saved).result saved.rows
    let cur := (retainedMove T v u).next
    let ord := retainedEdgeOrder T v site.birth.native.physical u
    ∃ cmd,op.result=some cmd ∧
      F.decode ((cmd : ReadCmd key (pageKeyWidth m+pad)).read X.hf F X.positive B (List.ofFn bits)).result =
        (entry cur).read X.hf v.child.prec (assignment cur.host.network (bits∘ord.symm) cur.vertex) := by
  let seed := originSeed (rootChart P) (oddAxis m) X.group k
  let pg := (widened pad (residentPageKey m k)).result
  let job := X.seed pad
  let tr := trace.keep (retainedMove T v u)
  let ps := keptPorts T v site.birth.native.physical u
  let ord := retainedEdgeOrder T v site.birth.native.physical u
  let wires : List WireRead := ps.map (fun h=>⟨tr.literal seed h,List.replicate (ord.symm (edge h.val)).val true⟩)
  have marker : ∀ x : PortAt (stableBorn X k),∃ rest,seed x=true::rest := by
    intro x
    exact ⟨_,originSeed_right (rootChart P) (oddAxis m) X.group k x⟩
  have hp : (site.origins u.val).pageKey=some pg := congrArg Origin.pageKey actualTag
  have creator : (site.origins u.val).stamp.creator=job.identifier :=
    congrArg (fun x : Origin key prec (pageKeyWidth m+pad)=>x.stamp.creator) actualTag
  have built := (compiled_retained_page_from_actual_fields site saved inj u trace seed marker actualBody pg hp).1
  let depth := retainedSourceDepth site u trace
  let out : ReadCmd key (pageKeyWidth m+pad) := .packet job.identifier pg depth wires
  change (compileKeptPage (site.site.oldKey u.val) (site.origins u.val)
      (cachedBook site saved).result saved.rows).result=
    some (ReadCmd.packet (site.origins u.val).stamp.creator pg depth wires) at built
  rw [creator] at built
  have value := (true_exterior_seed_entry X pad k B live tr F ord bits ps
    (kept_ports_exact T v site.birth.native.physical u).2 wires rfl).1
  change F.decode ((ReadCmd.packet job.identifier pg tr.depth wires).read X.hf F X.positive B
    (List.ofFn bits)).result=_ at value
  refine ⟨out,built,?_⟩
  change F.decode ((ReadCmd.packet job.identifier pg depth wires).read X.hf F X.positive B
    (List.ofFn bits)).result=_
  by_cases noPort : ps.isEmpty=true
  · have zero : ps=[] := List.isEmpty_iff.mp noPort
    have noWire : wires=[] := by simp only [wires,zero,List.map_nil]
    rw [noWire] at value ⊢
    exact (congrArg (fun x=>F.decode x.result)
      (empty_leaf_page_ignores_depth X.hf F X.positive B job.identifier pg depth tr.depth
        (List.ofFn bits))).trans value
  · have depthEq : depth=tr.depth := by
      unfold depth retainedSourceDepth
      exact if_neg noPort
    rw [depthEq]
    exact value

end
#print axioms actual_cached_exterior_page_read
end J6R53TerminalExterior
