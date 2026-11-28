import J6R34ChildPathChart
import J6R33GeneratedChildSiteFrames

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 2400
set_option maxHeartbeats 13000000

/-! On the actual selected row, the inherited body is prefixed rather
than reseated from a new page. A fresh body uses the slot and side in
its actual parent chart. These finite operations do not identify a
logical source proof with a raw address lookup. -/
namespace J6R34ChildPath
open scoped Polynomial Classical
open AOracleMachineTime AOracleMachineTimeTape J6R21Ancestor J6R20Ancestor
open J6R15ModeCost J6R25PreparedSupply J6R27OriginalGate
open J6R10Repack J6R11Blueprint J6R12Blueprint P11FullPacking J6R9PacketScopes
open J6ActiveRun J6R26DescriptorTree J6R24MeteredRecursion J1PPrinted J6R16ModeCost
open J6R32ChildResidentTransfer

def retainHeader (parent : List Bool) : Meter (List Bool) :=
  let w := copyBytes parent
  ⟨false::w.result,w.steps+4⟩

def freshHeader {a : ℕ} (wasColumn : Bool) (slot : Word a) : Meter (List Bool) :=
  let s := copyFixed slot
  ⟨true::wasColumn::s.result.bits,s.steps+4⟩

theorem retain_header_exact (parent : List Bool) :
    retainHeader parent=⟨false::parent,3*parent.length+5⟩ := by
  simp only [retainHeader,copyBytes_exact]

theorem fresh_header_exact {a : ℕ} (side : Bool) (slot : Word a) :
    freshHeader side slot=⟨true::side::slot.bits,3*a+5⟩ := by
  simp only [freshHeader,copy_fixed_exact]

variable {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable (T : Prepared cfg sel r hf) (v : Ticket sel r)

theorem retained_uses_selected_parent_half {w : ℕ}
    (D : PhysicalPorts sel (ticketReady T v) v.centerAt w)
    (u : OldAt T v) (x : PortAt (retainedMove T v u).next) :
    let h := ((retainedMove T v u).back x).val
    h∈D.physicalSelected v.groupAt ∧
      D.record h∈(selectPorts (word v.groupAt.val) D.raw).result ∧
      h=(edge x.val).val := by
  let h := ((retainedMove T v u).back x).val
  have i : h=(edge x.val).val := (retainedMove T v u).back_val x
  have G : physicalGroup sel (ticketReady T v) v.centerAt h=v.groupAt := by
    rw [i]
    exact (edge x.val).property
  have mem : h∈D.physicalSelected v.groupAt := List.mem_filter.mpr
    ⟨D.complete h,decide_eq_true G⟩
  refine ⟨mem,?_,i⟩
  rw [D.physical_port_select v.groupAt]
  exact List.mem_map_of_mem mem

theorem fresh_uses_selected_parent_half {w : ℕ}
    (D : PhysicalPorts sel (ticketReady T v) v.centerAt w)
    (k : PageAt T v) (x : PortAt (bornPoint T v k)) :
    let h := (edge x.val).val
    h∈D.physicalSelected v.groupAt ∧
      D.record h∈(selectPorts (word v.groupAt.val) D.raw).result ∧
      atPacket (layout T v) (edge h)=k := by
  let h := (edge x.val).val
  have eq : physicalGroup sel (ticketReady T v) v.centerAt h=v.groupAt := (edge x.val).property
  have mem : h∈D.physicalSelected v.groupAt := List.mem_filter.mpr
    ⟨D.complete h,decide_eq_true eq⟩
  refine ⟨mem,?_,(actual_fresh_port T v k x).2.1⟩
  rw [D.physical_port_select v.groupAt]
  exact List.mem_map_of_mem mem

theorem native_retained_prefix
    {root : Point f ell} (u : OldAt T v) (previous : Trace root (point v.parent.host u.val))
    (seed : PortAt root→List Bool) (x : PortAt (retainedMove T v u).next)
    (parent : List Bool)
    (receipt : parent=previous.literal seed ((retainedMove T v u).back x)) :
    retainHeader parent=
      ⟨(previous.keep (retainedMove T v u)).literal seed x,3*parent.length+5⟩ := by
  rw [retain_header_exact,Trace.literal,(retainedMove T v u).side_left,receipt]

variable {rW kW eW w p : ℕ}

theorem new_body_from_true_slot (k : PageAt T v) (x : PortAt (bornPoint T v k))
    (oldKey : v.parent.host.Row⊕v.parent.host.Col→Word rW)
    (pageKey : PageAt T v→Word kW) (id : v.parent.host.Edge→Word eW)
    (stamp : v.parent.host.Row⊕v.parent.host.Col→Stamp w p) :
    let H := (edge x.val).val
    let row := installedLane (layout T v) oldKey pageKey id stamp H
    let seat := physicalSeatField (layout T v) (axis T v) pageKey (edge H)
    freshHeader row.oldSide seat.slot=
      ⟨originSeed (layout T v) (axis T v) v.groupAt k x,
        3*((printedParams (f:=f) (ell:=ell) s).levelBits v.parent.depth)+5⟩ := by
  obtain ⟨x,h⟩ := x
  cases x with
  | inl e => cases h
  | inr e =>
    dsimp only
    rw [fresh_header_exact]
    rfl

#print axioms retain_header_exact
#print axioms fresh_header_exact
#print axioms retained_uses_selected_parent_half
#print axioms fresh_uses_selected_parent_half
#print axioms native_retained_prefix
#print axioms new_body_from_true_slot
end J6R34ChildPath
