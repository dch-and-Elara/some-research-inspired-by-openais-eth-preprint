import J6R36ChildFramedRouteCore

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 12600000

/-! Exact handoff of the same selected R26 rows. The writer reads
structured resident metadata by the actual raw address and never
infers variable body contents or boundaries from the old flat log. -/
namespace J6R36ChildFramedRoute
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J6R26DescriptorTree J6R27OriginalGate J6R34ChildPath
open J6ActiveRun J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open P11FullPacking J6R20Ancestor

theorem exact_attached_route {w owner a key prec page : ℕ}
    (bank : List (RefRow w (Addon owner a key prec page))) (id : Word key) (recv : Word prec)
    (raw : PortRow w) (aux : Addon owner a key prec page)
    (hit : (locate raw.address bank).result=some aux) :
    let op := attachRoute bank id recv raw
    op.result=some (frameView id recv raw aux) ∧
      op.steps≤locateFee w bank.length+
        frameFee w owner a key prec page raw.body.length aux.oldOrigin.pageKey.isSome+5 := by
  unfold attachRoute
  dsimp only
  rw [hit]
  dsimp only
  rw [write_frame_exact]
  exact ⟨rfl,Nat.add_le_add_right (Nat.add_le_add_right (locate_bound _ _) _) _⟩

def visitFee (w owner a key prec page n body : ℕ) (present : Bool) :=
  locateFee w n+frameFee w owner a key prec page body present+9

theorem framed_batch_exact {X : Type*} {w owner a key prec page : ℕ}
    (bank : List (RefRow w (Addon owner a key prec page))) (id : Word key) (recv : Word prec)
    (xs : List X) (raw : X→PortRow w) (aux : X→Addon owner a key prec page)
    (read : ∀ x∈xs,(locate (raw x).address bank).result=some (aux x)) :
    let op := frameBatch bank id recv (xs.map raw)
    op.result=some (xs.map (fun x=>frameView id recv (raw x) (aux x))) ∧
      op.steps≤3+(xs.map (fun x=>visitFee w owner a key prec page bank.length
        (raw x).body.length (aux x).oldOrigin.pageKey.isSome)).sum := by
  induction xs with
  | nil => exact ⟨rfl,le_rfl⟩
  | cons x xs ih =>
    let one := attachRoute bank id recv (raw x)
    let rest := frameBatch bank id recv (xs.map raw)
    obtain ⟨hOne,cOne⟩ := exact_attached_route bank id recv (raw x) (aux x) (read x List.mem_cons_self)
    obtain ⟨hRest,cRest⟩ := ih (fun y hy=>read y (List.mem_cons_of_mem x hy))
    change one.result=some _ at hOne
    dsimp only
    rw [List.map_cons,frameBatch,show one.result=_ from hOne]
    change rest.result.map (frameView id recv (raw x) (aux x)::·)=_ ∧
      one.steps+rest.steps+4≤_
    change rest.result=_ at hRest
    rw [hRest]
    simp only [Option.map_some,List.map_cons,List.sum_cons,true_and]
    change one.steps≤_ at cOne
    change rest.steps≤_ at cRest
    have first : one.steps+4≤visitFee w owner a key prec page bank.length
        (raw x).body.length (aux x).oldOrigin.pageKey.isSome := Nat.add_le_add_right cOne 4
    omega

variable {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable (T : Prepared cfg sel r hf) (v : Ticket sel r)

abbrev dim := (printedParams (f:=f) (ell:=ell) s).levelBits v.parent.depth
variable {w ownerW creator prec page : ℕ}

noncomputable def addonAt
    (oldKey : v.parent.host.Row⊕v.parent.host.Col→Word ownerW)
    (prior : v.parent.host.Row⊕v.parent.host.Col→Origin creator prec page)
    (pageKey : PageAt T v→Word page) (p : Port v.parent.host.Edge) :
    Addon ownerW (dim v) creator prec page :=
  let u := owner v.parent.host.network p
  let s := physicalSeatField (layout T v) (axis T v) pageKey (edge p)
  ⟨oldKey u,prior u,side p,s.slot,s.page⟩

theorem read_true_addon
    (D : PhysicalPorts sel (ticketReady T v) v.centerAt w)
    (aux : Port v.parent.host.Edge→Addon ownerW (dim v) creator prec page)
    (bank : List (RefRow w (Addon ownerW (dim v) creator prec page)))
    (actual : bank=D.order.map (fun h=>⟨(D.record h).address,aux h⟩))
    (h : Port v.parent.host.Edge) :
    (locate (D.record h).address bank).result=some (aux h) := by
  rw [actual]
  apply locate_hit
  · exact List.mem_map.mpr ⟨h,D.complete h,rfl⟩
  · intro row hm he
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp hm
    have pEq : p=h := D.distinct he
    rw [pEq]

theorem native_frames_from_actual_selection
    {port edgeW dW tW zW mW : ℕ} (J : NativeJob T v port edgeW dW prec tW zW mW)
    (issuance : Meter (Word creator))
    (aux : Port v.parent.host.Edge→Addon ownerW (dim v) creator prec page)
    (bank : List (RefRow port (Addon ownerW (dim v) creator prec page)))
    (actual : bank=J.physical.order.map (fun h=>⟨(J.physical.record h).address,aux h⟩)) :
    let rows := halfOrder T v J.physical
    let op := selectedFrame J.gWord J.physical.raw bank issuance.result J.receiving
    op.result=some (rows.map (fun h=>
      frameView issuance.result J.receiving (J.physical.record h.val) (aux h.val))) ∧
      op.steps≤11+(J.physical.raw.map rowScanFee).sum+
        (rows.map (fun h=>visitFee port ownerW (dim v) creator prec page bank.length
          (J.physical.record h.val).body.length (aux h.val).oldOrigin.pageKey.isSome)).sum := by
  let selected := selectPorts J.gWord J.physical.raw
  let rows := halfOrder T v J.physical
  have group : J.gWord=word v.groupAt.val :=
    (valued_word J.gWord).symm.trans (congrArg word J.gExact)
  have ordered : selected.result=rows.map (fun h=>J.physical.record h.val) := by
    dsimp only [selected]
    rw [group,J.physical.physical_port_select,half_order_is_selected T v J.physical,List.map_map]
    rfl
  have rawFee : selected.steps=3+(J.physical.raw.map rowScanFee).sum :=
    (select_ports_exact J.gWord J.physical.raw).2
  obtain ⟨hit,fee⟩ := framed_batch_exact bank issuance.result J.receiving rows
     (fun h=>J.physical.record h.val) (fun h=>aux h.val)
      (fun h _=>read_true_addon T v J.physical aux bank actual h.val)
  unfold selectedFrame
  dsimp only
  change (frameBatch bank issuance.result J.receiving selected.result).result=_ ∧
    selected.steps+(frameBatch bank issuance.result J.receiving selected.result).steps+5≤_
  rw [ordered,rawFee]
  refine ⟨hit,?_⟩
  let price := (rows.map (fun (h : HalfAt T v)=>visitFee port ownerW (dim v) creator prec page
    bank.length (J.physical.record h.val).body.length (aux h.val).oldOrigin.pageKey.isSome)).sum
  change (frameBatch bank issuance.result J.receiving (rows.map (fun h=>J.physical.record h.val))).steps
    ≤3+price at fee
  change 3+(J.physical.raw.map rowScanFee).sum+_+5≤11+(J.physical.raw.map rowScanFee).sum+price
  omega

#print axioms exact_attached_route
#print axioms framed_batch_exact
#print axioms read_true_addon
#print axioms native_frames_from_actual_selection
end J6R36ChildFramedRoute
