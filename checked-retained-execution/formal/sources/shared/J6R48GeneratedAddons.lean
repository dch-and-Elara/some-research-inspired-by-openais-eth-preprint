import J6R41StructuredAllPathsSite

/-! Produce the sidecar in the order of the physical parent file, paying
for each source row read and serialization. The per-row reader is a
separate boundary: this result does not treat lookups as free. -/
namespace J6R48GeneratedAddons
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J6R26DescriptorTree J6R34ChildPath J6R33StatefulArithmeticPage J6R36ChildFramedRoute
open J6ActiveRun J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6R30ProducedGateRegistry J6R41StructuredAllPaths
set_option autoImplicit false
set_option linter.unusedSectionVars false

def emit {X : Type*} {owner a key prec page : ℕ}
    (readRow : X → Meter (Addon owner a key prec page)) :
    List X → Meter (List (Addon owner a key prec page))
  | [] => ⟨[], 4⟩
  | p::ps =>
    let r := readRow p
    let b := copyAddon r.result
    let t := emit readRow ps
    ⟨b.result::t.result, r.steps+b.steps+t.steps+4⟩

theorem emit_exact {X : Type*} {owner a key prec page : ℕ}
    (readRow : X → Meter (Addon owner a key prec page)) (order : List X) :
    (emit readRow order).result=order.map (fun h=>(readRow h).result) ∧
    (emit readRow order).steps=4+(order.map (fun h=>(readRow h).steps+
      addonFee owner a key prec page (readRow h).result.oldOrigin.pageKey.isSome+4)).sum := by
  induction order with
  | nil => exact ⟨rfl,rfl⟩
  | cons p ps ih =>
    simp only [emit,copy_addon_exact,List.map_cons,List.sum_cons,ih.1,ih.2,true_and]
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

def SiteInputs.fromReader
    (law : ∀ h, (readRow h).result=addonAt T v oldKey previous pageKey h) :
    SiteInputs Q previous :=
  ⟨owner,oldKey,pageKey,(emit readRow Q.native.physical.order).result,by
    rw [(emit_exact readRow _).1]
    exact List.map_congr_left (fun h _=>law h)⟩

theorem generated_install_exact
    (law : ∀ h, (readRow h).result=addonAt T v oldKey previous pageKey h) :
    let made := emit readRow Q.native.physical.order
    let S := SiteInputs.fromReader Q previous oldKey pageKey readRow law
    S.install.result=some (Q.native.physical.order.map
      (fun h=>⟨(Q.native.physical.record h).address,addonAt T v oldKey previous pageKey h⟩)) ∧
    made.steps+S.install.steps=8+
      (Q.native.physical.order.map (fun h=>(readRow h).steps+
        addonFee owner (dim v) key prec page (readRow h).result.oldOrigin.pageKey.isSome+4)).sum+
      (made.result.map (fun x=>3*Q.port+11+
        addonFee owner (dim v) key prec page x.oldOrigin.pageKey.isSome)).sum := by
  dsimp only
  have E := emit_exact readRow Q.native.physical.order
  have I := (SiteInputs.fromReader Q previous oldKey pageKey readRow law).install_exact
  refine ⟨I.1,?_⟩
  rw [E.2,I.2]
  dsimp only [SiteInputs.fromReader]
  omega

#print axioms emit_exact
#print axioms SiteInputs.fromReader
#print axioms generated_install_exact
end J6R48GeneratedAddons

