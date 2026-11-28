import J6R51PeakSidecar
import J6R51PeakNativeHeader
import J6R51OnlineCore
import J6R48GeneratedAddonsNative

/-! Actual first indexed installation and later emission-plus-install.
The parent tape has two rows per actual edge. Arbitrarily priced
queries remain exactly as an explicit sum, not hidden in a free read. -/
namespace J6R57ScopeFee
open scoped Polynomial BigOperators Classical
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R21Ancestor J6R25PreparedSupply J6R26DescriptorTree
open J6ActiveRun J6ActiveSchedule J6R12Blueprint J6R11Blueprint J1PPrinted J6R16ModeCost
open J6R10Repack J6R24MeteredRecursion J6R34ChildPath
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R48DFS J6R49DFS J6R50SourceProducer J6R51Peak J6R51Online
open J6R36ChildFramedRoute J6R41StructuredAllPaths J6R48GeneratedAddons J6R48RawRoute
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 24000000
set_option maxRecDepth 4800
set_option Elab.async false
noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "P" => (Plan sel)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)

def maxAddonFee (owner dim key prec page : ℕ) : ℕ :=
  3*owner+3*dim+3*key+3*prec+6*page+41

theorem addon_fee_from_actual_widths (owner a key prec page : ℕ) (hasPage : Bool) :
    addonFee owner a key prec page hasPage≤maxAddonFee owner a key prec page := by
  cases hasPage <;> simp only [addonFee,maxAddonFee,originFee,if_true,if_false,Bool.false_eq_true]
  all_goals omega

theorem sum_with_explicit_query_bill {X : Type*} (dirs : List X) (read acquire : X→ℕ) (extra : ℕ)
    (compare : ∀ h∈dirs,read h≤acquire h+extra) :
    (dirs.map read).sum≤(dirs.map acquire).sum+dirs.length*extra := by
  induction dirs with
  | nil => simp
  | cons a xs ih =>
    rw [List.map_cons,List.map_cons,List.sum_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    have h := compare a List.mem_cons_self
    have t := ih (fun p hp=>compare p (List.mem_cons_of_mem _ hp))
    omega

theorem actual_physical_index_install_ceiling {v : Ticket sel r} {B : Birth T v key prec tw bw page}
    {origins : v.parent.host.Row⊕v.parent.host.Col→Origin key prec page}
    (S : SiteInputs B origins) :
    S.install.steps≤4+(2*v.parent.edges)*(3*B.port+11+maxAddonFee S.ownerWidth (dim v) key prec page) := by
  rw [S.install_exact.2]
  apply Nat.add_le_add_left
  have cnt := (actual_addon_tapes_count_both_half_ports S).1
  rw [←cnt]
  exact uniform_sum_bound _ _ _ (fun x _=>Nat.add_le_add_left (addon_fee_from_actual_widths _ _ _ _ _ _) _)

def sidecarGeometry (parentEdges port owner d key prec page ownerKey seatKey ownerRows seatRows : ℕ) :=
  8+(2*parentEdges)*(locateFee ownerKey ownerRows+locateFee seatKey seatRows+
    3*port+25+2*maxAddonFee owner d key prec page)

variable {v : Ticket sel r} {X : StoredSite T v key prec tw bw page} {u : (Plan sel).Slot v.child}

def sidecarQueryBill (K : LocalLoad X u) : ℕ :=
  let D := K.directory
  List.sum (List.map (fun h : Port v.child.host.Edge=>(D.queries h).steps)
    K.advance.next.birth.native.physical.order)

theorem actual_demand_sidecar_ceiling (K : LocalLoad X u) :
    K.sidecarCharge≤sidecarQueryBill K+
      sidecarGeometry v.child.edges K.advance.next.birth.port K.directory.ow
        (dim (successorTicket v u)) key prec page K.directory.k1 K.directory.k2
        K.directory.owners.length K.directory.seats.length := by
  let D := K.directory
  let B := K.advance.next.birth
  let S := K.advance.next.site
  let order := B.native.physical.order
  let add := maxAddonFee D.ow (dim (successorTicket v u)) key prec page
  let look := locateFee D.k1 D.owners.length+locateFee D.k2 D.seats.length
  let rd := D.read X K.event
  let query := fun h=>(D.queries h).steps
  have orderLen : order.length=2*v.child.edges := by
    have h := (actual_addon_tapes_count_both_half_ports S).1
    rw [S.aligned,List.length_map] at h
    exact h
  have each (h : Port v.child.host.Edge) :
      (rd h).steps+addonFee D.ow (dim (successorTicket v u)) key prec page
        (rd h).result.oldOrigin.pageKey.isSome+4≤query h+(look+add+14) := by
    have qBound := resident_read_bound D.owners D.seats (D.queries h)
    have exactFee : (rd h).steps=(residentRead D.owners D.seats (D.queries h)).steps+2 := rfl
    have aBound := addon_fee_from_actual_widths D.ow (dim (successorTicket v u)) key prec page
      (rd h).result.oldOrigin.pageKey.isSome
    have rBound : (residentRead D.owners D.seats (D.queries h)).steps≤query h+look+8 := by
      dsimp only [query,look]
      omega
    change _≤add at aBound
    rw [exactFee]
    omega
  have total := sum_with_explicit_query_bill order
    (fun h=>(rd h).steps+addonFee D.ow (dim (successorTicket v u)) key prec page
       (rd h).result.oldOrigin.pageKey.isSome+4) query (look+add+14) (fun h _=>each h)
  rw [orderLen] at total
  have e : (emit rd order).steps≤4+((order.map query).sum+(2*v.child.edges)*(look+add+14)) := by
    rw [(emit_exact _ _).2]
    exact Nat.add_le_add_left total _
  have i : S.install.steps≤4+(2*v.child.edges)*(3*B.port+11+add) :=
    actual_physical_index_install_ceiling S
  have eq : sidecarQueryBill K=(order.map query).sum := rfl
  change (emit rd order).steps+S.install.steps≤_
  rw [eq]
  refine (Nat.add_le_add e i).trans_eq ?_
  change _= (order.map query).sum+(8+(2*v.child.edges)*(look+3*B.port+25+2*add))
  ring

end
#print axioms addon_fee_from_actual_widths
#print axioms sum_with_explicit_query_bill
#print axioms actual_physical_index_install_ceiling
#print axioms sidecarQueryBill
#print axioms actual_demand_sidecar_ceiling
end J6R57ScopeFee
