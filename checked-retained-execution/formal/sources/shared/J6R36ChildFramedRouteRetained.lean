import J6R36ChildFramedRouteRequests

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 2500
set_option maxHeartbeats 16500000

/-! On an actual retained vertex, its old *parent* body receipt is
enough to generate the new child's complete incoming wire requests.
In particular the child request equality is a conclusion, not a
separate caller-supplied read law. -/
namespace J6R36ChildFramedRoute
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J6R26DescriptorTree J6R27OriginalGate J6R34ChildPath
open J6ActiveRun J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open P11FullPacking

variable {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable (T : Prepared cfg sel r hf) (v : Ticket sel r)

def keptCond (u : OldAt T v) (h : HalfAt T v) : Prop :=
  owner v.parent.host.network h.val=u.val

abbrev KeptHalf (u : OldAt T v) := {h : HalfAt T v // keptCond T v u h}

noncomputable def asKeptPort (u : OldAt T v) (x : KeptHalf T v u) :
    PortAt (retainedMove T v u).next :=
  ⟨.inl x.val,congrArg Sum.inl (Subtype.ext x.property)⟩

theorem retained_output_port_is_same_half (u : OldAt T v) (x : KeptHalf T v u) :
    edge (asKeptPort T v u x).val=x.val ∧
      ((retainedMove T v u).back (asKeptPort T v u x)).val=x.val.val := ⟨rfl,rfl⟩

theorem as_kept_port_inj (u : OldAt T v) : Function.Injective (asKeptPort T v u) := by
  intro h j e
  apply Subtype.ext
  exact congrArg (fun p=>edge p.val) e

theorem as_kept_port_surj (u : OldAt T v) : Function.Surjective (asKeptPort T v u) := by
  intro q
  have e := ((retainedMove T v u).back q).property
  rw [(retainedMove T v u).back_val] at e
  let h : KeptHalf T v u := ⟨edge q.val,e⟩
  refine ⟨h,Subtype.ext ?_⟩
  rcases q with ⟨q,hq⟩
  cases q with
  | inl e => rfl
  | inr e => cases hq

variable {w ownerW key prec page : ℕ}

noncomputable def keptPorts
    (D : PhysicalPorts sel (ticketReady T v) v.centerAt w) (u : OldAt T v) :
    List (PortAt (retainedMove T v u).next) :=
  (scanSubtype (keptCond T v u) (halfOrder T v D)).map (asKeptPort T v u)

theorem kept_ports_exact
    (D : PhysicalPorts sel (ticketReady T v) v.centerAt w) (u : OldAt T v) :
    (keptPorts T v D u).Nodup ∧ ∀ p,p∈keptPorts T v D u := by
  obtain ⟨nd,all⟩ := half_order_complete T v D
  refine ⟨(scan_subtype_nodup _ _ nd).map (as_kept_port_inj T v u),?_⟩
  intro p
  obtain ⟨x,hx⟩ := as_kept_port_surj T v u p
  exact List.mem_map.mpr ⟨x,(scan_subtype_mem _ _ x).mpr (all x.val),hx⟩

theorem actual_retained_request_file {port edgeW dW tW zW mW : ℕ}
    (J : NativeJob T v port edgeW dW prec tW zW mW) (issued : Meter (Word key))
    (oldKey : v.parent.host.Row⊕v.parent.host.Col→Word ownerW) (inj : Function.Injective oldKey)
    (prior : v.parent.host.Row⊕v.parent.host.Col→Origin key prec page)
    (pageKey : PageAt T v→Word page)
    (bank : List (RefRow port (Addon ownerW (dim v) key prec page)))
    (represent : bank=J.physical.order.map (fun h=>⟨(J.physical.record h).address,
      addonAt T v oldKey prior pageKey h⟩))
    (u : OldAt T v) {root : Point f ell}
    (tr : Trace root (point v.parent.host u.val))
    (seed : PortAt root→List Bool)
    (body : ∀ p : PortAt (point v.parent.host u.val), (J.physical.record p.val).body=tr.literal seed p) :
    let op := retainedInput J.gWord J.physical.raw bank issued.result J.receiving (oldKey u.val)
    let ports := keptPorts T v J.physical u
    let extend := tr.keep (retainedMove T v u)
    let rows := halfOrder T v J.physical
    let F := fun h : HalfAt T v=>frameView issued.result J.receiving (J.physical.record h.val)
      (addonAt T v oldKey prior pageKey h.val)
    op.result=some (ports.map (fun p=>⟨(J.physical.record (edge p.val).val).address,extend.literal seed p⟩)) ∧
      op.steps=(selectedFrame J.gWord J.physical.raw bank issued.result J.receiving).steps+
        (collectRetained (oldKey u.val) (rows.map F)).steps+4 := by
  let before := selectedFrame J.gWord J.physical.raw bank issued.result J.receiving
  let rows := halfOrder T v J.physical
  let F (h : HalfAt T v) := frameView issued.result J.receiving (J.physical.record h.val)
    (addonAt T v oldKey prior pageKey h.val)
  let extension := tr.keep (retainedMove T v u)
  have hBefore : before.result=some (rows.map F) :=
    (native_frames_from_actual_selection T v J issued (addonAt T v oldKey prior pageKey)
      bank represent).1
  have correct (h : HalfAt T v) : oldKey u.val=(F h).oldOwner ↔ keptCond T v u h := by
    change oldKey u.val=oldKey (owner v.parent.host.network h.val) ↔
      owner v.parent.host.network h.val=u.val
    exact ⟨fun e=>(inj e).symm,fun e=>congrArg oldKey e.symm⟩
  have picked := structured_requests_for_subtype (oldKey u.val) rows F (keptCond T v u) correct
  have endShape : (collectRetained (oldKey u.val) (rows.map F)).result=
      (keptPorts T v J.physical u).map (fun p=>⟨(J.physical.record (edge p.val).val).address,
        extension.literal seed p⟩) := by
    rw [picked]
    unfold keptPorts
    rw [List.map_map]
    apply List.map_congr_left
    intro h _
    let p := asKeptPort T v u h
    change requestView (F h.val).left=⟨(J.physical.record (edge p.val).val).address,
      extension.literal seed p⟩
    have E := retained_output_port_is_same_half T v u h
    rw [E.1]
    have alpha : (J.physical.record h.val.val).body=
        tr.literal seed ((retainedMove T v u).back p) := by
      rw [← E.2]
      exact body _
    have step := native_retained_prefix T v u tr seed p (J.physical.record h.val.val).body alpha
    have hE := congrArg Meter.result step
    rw [retain_header_exact] at hE
    change (⟨(J.physical.record h.val.val).address,false::(J.physical.record h.val.val).body⟩ : WireRequest port)=_
    exact congrArg (WireRequest.mk _) hE
  unfold retainedInput
  dsimp only
  rw [show before.result=_ from hBefore]
  exact ⟨congrArg some endShape,rfl⟩

#print axioms retained_output_port_is_same_half
#print axioms as_kept_port_inj
#print axioms as_kept_port_surj
#print axioms kept_ports_exact
#print axioms actual_retained_request_file
end J6R36ChildFramedRoute
