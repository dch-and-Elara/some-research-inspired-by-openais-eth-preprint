import J6R48GeneratedAddonsFused

/-! The fused installer for one actual source occurrence writes the same
bank as the old installer and accounts for the eliminated serialization. -/
namespace J6R48GeneratedAddons
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J6R26DescriptorTree J6R34ChildPath J6R33StatefulArithmeticPage J6R36ChildFramedRoute
open J6ActiveRun J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6R30ProducedGateRegistry J6R41StructuredAllPaths
set_option autoImplicit false
set_option linter.unusedSectionVars false

theorem sum_fee_fuse {X : Type*} (order : List X) (f g c : X → ℕ) :
    (order.map (fun x=>f x+c x+4)).sum+(order.map (fun x=>g x+c x)).sum =
      (order.map (fun x=>f x+g x+c x)).sum+(order.map (fun x=>c x+4)).sum := by
  induction order with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons]
    omega

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable (Q : Birth T v key prec tw bw page)
variable (previous : v.parent.host.Row⊕v.parent.host.Col→Origin key prec page)
variable {owner : ℕ}
variable (oldKey : v.parent.host.Row⊕v.parent.host.Col→Word owner)
variable (pageKey : PageAt T v→Word page)
variable (readRow : Port v.parent.host.Edge → Meter (Addon owner (dim v) key prec page))

theorem actual_site_fused_saves_copy
    (law : ∀ h, (readRow h).result=addonAt T v oldKey previous pageKey h) :
    let order := Q.native.physical.order
    let made := emit readRow order
    let S := SiteInputs.fromReader Q previous oldKey pageKey readRow law
    let fused := directInstall (fun h=>(Q.native.physical.record h).address) readRow order
    S.install.result=some fused.result ∧
    made.steps+S.install.steps=fused.steps+4+
      (order.map (fun h=>addonFee owner (dim v) key prec page
        (readRow h).result.oldOrigin.pageKey.isSome+4)).sum := by
  dsimp only
  have G := generated_install_exact Q previous oldKey pageKey readRow law
  have D := direct_install_exact (fun h=>(Q.native.physical.record h).address)
    readRow Q.native.physical.order
  dsimp only at G
  constructor
  · rw [G.1,D.1]
    congr 1
    exact List.map_congr_left (fun h _=>by rw [law])
  · rw [G.2,D.2,(emit_exact readRow _).1,List.map_map]
    have F := sum_fee_fuse Q.native.physical.order (fun h=>(readRow h).steps)
      (fun _=>3*Q.port+11)
      (fun h=>addonFee owner (dim v) key prec page (readRow h).result.oldOrigin.pageKey.isSome)
    simp only [Function.comp_def,Nat.add_assoc] at F ⊢
    omega

#print axioms actual_site_fused_saves_copy
end J6R48GeneratedAddons

