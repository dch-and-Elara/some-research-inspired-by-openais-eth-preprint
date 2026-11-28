import J6R52DispatchShell
import J6R52FreshExteriorWordsRetained

/-! Local numerical inputs to the fixed-shell constructor. Its
depth and issuer come from the current physical occurrence; the
new precision is read from the same selected replay input. The
arithmetic frame/probe plane is a separate measured input, not a
supplier of a child birth or of the dispatcher. -/
namespace J6R58RequestSource
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R16ModeCost J6R27OriginalGate
open P11FullPacking J6R9PacketScopes J6R10Repack J6R12CollisionEdges
open J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R26DescriptorTree J6R24MeteredRecursion J6R33GeneratedChildSite
open J6R34ChildPath J6R41StructuredAllPaths J6R48GeneratedAddons J6R48RawRoute
open J6R30ProducedGateRegistry J6R32ChildResidentTransfer J6R33StatefulArithmeticPage
open J6R49SourceLayout J6R50SourceProducer J6R51Online J6R52Dispatch J6R52FreshExterior
open J6R21Ancestor J6R36ChildFramedRoute J6R34RootAtlas
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 22000000
set_option maxRecDepth 4300
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel root hf}
variable {v : Ticket sel root}
variable (X : StoredSite T v key prec tw bw page)
variable {u : (Plan sel).Slot v.child} {q : ℕ}
variable {U : ExplicitSelectedWords X.site u q}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "A" => (J6ActiveRun.Shape.levelBits (printedParams (f:=f) (ell:=ell) s) v.child.depth)
local notation "nx" => (successorTicket v u)
local notation "d" => (ticketReady T (successorTicket v u))
local notation "t" => (Ticket.centerAt (successorTicket v u))
local notation "P" => (registerPrecision SP v.child t)

def actualDepthOfParent : Meter (Word X.input.dep) :=
  increment X.input.native.result.oldDepth

theorem actual_parent_depth_after_count :
    (actualDepthOfParent X).result.val=v.child.depth ∧
      (actualDepthOfParent X).steps=13*X.input.dep+4 := by
  let left := X.input.native.result
  have fit : left.oldDepth.val+1<2^X.input.dep := by rw [left.depthExact]; exact left.depthFit
  have count := increment_exact left.depthPos left.oldDepth fit
  have dpt : v.child.depth=v.parent.depth+1 := rfl
  exact ⟨count.1.trans (by rw [left.depthExact,dpt]),count.2⟩

theorem real_next_edge_fits_parent_width (u : (Plan sel).Slot v.child) :
    0<X.input.edge ∧ (successorTicket v u).child.edges<2^X.input.edge :=
  ⟨X.input.native.result.edgePos,
    ((Plan sel).smaller v.child u).trans X.input.native.result.edgeFit⟩

variable (R : Replayed X.site u q U)

def actualReceiving (selected : ExplicitSelectedWords X.site u q) : Meter (Word prec) :=
  retainAtWidth prec selected.precision

theorem actual_receiving_from_selected_precision (selected : ExplicitSelectedWords X.site u q)
    (fit : (nx).child.prec<2^prec) :
    (actualReceiving X selected).result.val=(nx).child.prec ∧
      (actualReceiving X selected).steps=2*(q+1)+4*prec+5 := by
  have p : selected.precision.val=(nx).child.prec := selected.precisionExact
  have width : selected.precision.val<2^prec := p.symm ▸ fit
  obtain ⟨el,steps⟩ := retain_at_width_exact prec selected.precision width
  exact ⟨el.trans p,steps⟩

structure LoadedPlane (R : Replayed X.site u q U) where
  code : ℕ
  fw : List (A1R10.Word P)
  hOld : 0<fw.length
  hMod : A1R10.Modulus P (register_positive d t) fw=NativeProbeRing.liftPoly P f
  context : CentreContext tw bw
  axis : List Bool
  coordinates : {bs : List Bool // bs.length=fw.length}
  clock : axis.length=(centerIndex d t).val
  centre : context.center=(t).val
  codeExact : context.codeWidth.val=code
  codePos : 0<code
  codeFit : 1+R.certificate.modes.length<2^code
  probe : coordinates.val=List.ofFn (NativeProbeRing.chosenRep f.natDegree
    (realProbeCount (S:=SP) (c:=v.child)) (d).fit (nx).probeAt)
  width : (q-A)+13*A=page

def localFixedShell (body : Meter (LoadedPlane X R))
    (fitDepth : v.child.depth+1<2^X.input.dep) (fitPrec : (nx).child.prec<2^prec) :
    Meter (PayloadShell R) :=
  let depth := actualDepthOfParent X
  let receive := actualReceiving X U
  let plane := body.result
  let shell : PayloadShell R := {
      dep := X.input.dep
      edge := X.input.edge
      code := plane.code
      issued := increment X.birth.job.identifier
      oldDepth := depth.result
      depthExact := (actual_parent_depth_after_count X).1
      depthPos := X.input.native.result.depthPos
      depthFit := fitDepth
      receiving := receive.result
      receiveExact := (actual_receiving_from_selected_precision X U fitPrec).1
      edgePos := (real_next_edge_fits_parent_width X u).1
      edgeFit := (real_next_edge_fits_parent_width X u).2
      fw := plane.fw
      hOld := plane.hOld
      hMod := plane.hMod
      context := plane.context
      axis := plane.axis
      coordinates := plane.coordinates
      clock := plane.clock
      centre := plane.centre
      codeExact := plane.codeExact
      codePos := plane.codePos
      codeFit := plane.codeFit
      outerPos := X.input.outerPos
      centreFit := Nat.succ_le_succ ((centerIndex d t).isLt.le.trans U.widthFit)
      probe := plane.probe
      width := plane.width }
  ⟨shell,body.steps+depth.steps+receive.steps+6⟩

theorem actual_shell_uses_parent_words_only_once
    (body : Meter (LoadedPlane X R)) (fitDepth : v.child.depth+1<2^X.input.dep)
    (fitPrec : (nx).child.prec<2^prec) :
    let S := localFixedShell X R body fitDepth fitPrec
    S.result.issued=increment X.birth.job.identifier ∧
      S.result.dep=X.input.dep ∧
      S.result.oldDepth.bits=(increment X.input.native.result.oldDepth).result.bits ∧
      S.result.receiving=(retainAtWidth prec U.precision).result ∧
      S.result.coordinates.val=body.result.coordinates.val ∧
      S.steps=body.steps+(13*X.input.dep+4)+(2*(q+1)+4*prec+5)+6 := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
  change body.steps+(actualDepthOfParent X).steps+(actualReceiving X U).steps+6=_
  rw [(actual_parent_depth_after_count X).2,(actual_receiving_from_selected_precision X U fitPrec).2]

#print axioms actual_parent_depth_after_count
#print axioms real_next_edge_fits_parent_width
#print axioms actual_receiving_from_selected_precision
#print axioms localFixedShell
#print axioms actual_shell_uses_parent_words_only_once
end
end J6R58RequestSource
