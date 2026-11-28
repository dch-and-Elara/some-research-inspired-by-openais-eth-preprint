import J6R36ChildFramedRouteBatch
import J6R36ChildFramedRouteCarry

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 16000000

/-! One actual selected half-port advances its structured record.
The old branch copies the previous creator, page and precision; the
fresh branch takes this occurrence's issued creator and precision.
Both branches can subsequently be scanned as R26 structured rows. -/
namespace J6R36ChildFramedRoute
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J6R26DescriptorTree J6R27OriginalGate J6R34ChildPath
open J6ActiveRun J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open P11FullPacking J6R20Ancestor

def forwardRecord {w owner a key prec page : ℕ}
    (bank : List (RefRow w (Addon owner a key prec page))) (issue : Word key) (receive : Word prec)
    (raw : PortRow w) (nextColumn : Bool) (nextGroup : Word 6) :
    Meter (Option (PortRow (w+1)×Origin key prec page)) :=
  let F := attachRoute bank issue receive raw
  match F.result with
  | none=>⟨none,F.steps+3⟩
  | some f=>
    let out := carryLane (if nextColumn then f.right else f.left) nextGroup
    ⟨some out.result,F.steps+out.steps+4⟩

theorem forward_bought_row {w owner a key prec page : ℕ}
    (bank : List (RefRow w (Addon owner a key prec page))) (issue : Word key) (receive : Word prec)
    (raw : PortRow w) (aux : Addon owner a key prec page)
    (found : (locate raw.address bank).result=some aux)
    (nextColumn : Bool) (nextGroup : Word 6) :
    let op := forwardRecord bank issue receive raw nextColumn nextGroup
    let f := frameView issue receive raw aux
    let lane := if nextColumn then f.right else f.left
    let copied := carryLane lane nextGroup
    op.result=some copied.result ∧
      op.steps≤locateFee w bank.length+
        frameFee w owner a key prec page raw.body.length aux.oldOrigin.pageKey.isSome+copied.steps+9 := by
  obtain ⟨e,m⟩ := exact_attached_route bank issue receive raw aux found
  unfold forwardRecord
  dsimp only
  rw [e]
  dsimp only
  refine ⟨rfl,?_⟩
  let f := frameView issue receive raw aux
  let price := (carryLane (if nextColumn then f.right else f.left) nextGroup).steps
  change (attachRoute bank issue receive raw).steps+price+4≤
    locateFee w bank.length+
      frameFee w owner a key prec page raw.body.length aux.oldOrigin.pageKey.isSome+price+9
  omega

variable {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable (T : Prepared cfg sel r hf) (v : Ticket sel r)
variable {port eW dW prec tW zW mW key ownerW page : ℕ}
variable (J : NativeJob T v port eW dW prec tW zW mW) (issued : Meter (Word key))
variable (K : v.parent.host.Row⊕v.parent.host.Col→Word ownerW)
variable (before : v.parent.host.Row⊕v.parent.host.Col→Origin key prec page)
variable (pageKey : PageAt T v→Word page)
variable (bank : List (RefRow port (Addon ownerW (dim v) key prec page)))
variable (represent : bank=J.physical.order.map (fun h=>⟨(J.physical.record h).address,addonAt T v K before pageKey h⟩))

include represent in
theorem actual_fresh_route_start
    (k : PageAt T v) (x : PortAt (bornPoint T v k)) (nextGroup : Word 6) :
    let h := (edge x.val).val
    let op := forwardRecord bank issued.result J.receiving (J.physical.record h) true nextGroup
    op.result=some
      (⟨routeWord ⟨(J.physical.record h).address,true⟩,nextGroup,
         originSeed (layout T v) (axis T v) v.groupAt k x⟩,
         ⟨⟨issued.result,J.receiving⟩,some (pageKey k)⟩) ∧
      J.receiving.val=(entry (bornPoint T v k)).created := by
  let h := (edge x.val).val
  let aux := addonAt T v K before pageKey h
  have hit := read_true_addon T v J.physical (addonAt T v K before pageKey) bank represent h
  have ap := (forward_bought_row bank issued.result J.receiving (J.physical.record h) aux hit true nextGroup).1
  dsimp only
  rw [ap,carry_keeps_body_and_stamp]
  have realised := actual_fresh_port T v k x
  have pg : aux.newPage=pageKey k := congrArg pageKey realised.2.1
  have hraw : true::(side h)::(slotWord (layout T v) (edge h)).bits=
      originSeed (layout T v) (axis T v) v.groupAt k x := by
    obtain ⟨x,hx⟩ := x
    cases x with
    | inl e => cases hx
    | inr e => rfl
  constructor
  · have body :
        (frameView issued.result J.receiving (J.physical.record h) aux).right.body=
          originSeed (layout T v) (axis T v) v.groupAt k x := hraw
    change some
      (PortRow.mk (routeWord ⟨(J.physical.record h).address,true⟩) nextGroup
        (frameView issued.result J.receiving (J.physical.record h) aux).right.body,
        Origin.mk (Stamp.mk issued.result J.receiving) (some aux.newPage))=_
    rw [body,pg]
  · exact J.receiveExact.trans realised.2.2.symm

include represent in
theorem actual_retained_route_step
    (u : OldAt T v) {root : Point f ell}
    (tr : Trace root (point v.parent.host u.val)) (seed : PortAt root→List Bool)
    (x : PortAt (retainedMove T v u).next) (nextGroup : Word 6)
    (body : (J.physical.record ((retainedMove T v u).back x).val).body=
      tr.literal seed ((retainedMove T v u).back x)) :
    let h := ((retainedMove T v u).back x).val
    let op := forwardRecord bank issued.result J.receiving (J.physical.record h) false nextGroup
    op.result=some
      (⟨routeWord ⟨(J.physical.record h).address,false⟩,nextGroup,
        (tr.keep (retainedMove T v u)).literal seed x⟩,before u.val) := by
  let h := ((retainedMove T v u).back x).val
  let aux := addonAt T v K before pageKey h
  have hit := read_true_addon T v J.physical (addonAt T v K before pageKey) bank represent h
  have ap := (forward_bought_row bank issued.result J.receiving (J.physical.record h)
    aux hit false nextGroup).1
  dsimp only
  rw [ap,carry_keeps_body_and_stamp]
  have oldOwner : owner v.parent.host.network h=u.val := ((retainedMove T v u).back x).property
  have kept : aux.oldOrigin=before u.val := congrArg before oldOwner
  have R := native_retained_prefix T v u tr seed x (J.physical.record h).body body
  have H := congrArg Meter.result R
  rw [retain_header_exact] at H
  change false::(J.physical.record h).body=(tr.keep (retainedMove T v u)).literal seed x at H
  change some
    (PortRow.mk (routeWord ⟨(J.physical.record h).address,false⟩) nextGroup
      (false::(J.physical.record h).body),aux.oldOrigin)=_
  rw [H,kept]

#print axioms forward_bought_row
#print axioms actual_fresh_route_start
#print axioms actual_retained_route_step
end J6R36ChildFramedRoute
