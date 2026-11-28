import J6R48GeneratedAddonsNative

namespace J6R48GeneratedAddons
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J6R26DescriptorTree J6R34ChildPath J6R33StatefulArithmeticPage J6R36ChildFramedRoute
open J6ActiveRun J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6R30ProducedGateRegistry J6R41StructuredAllPaths J6R27OriginalGate
set_option autoImplicit false
set_option linter.unusedSectionVars false

private theorem list_sum_compare {α : Type*} (L : List α) {f g : α → ℕ}
    (h : ∀ x, f x ≤ g x) : (L.map f).sum ≤ (L.map g).sum := by
  induction L with
  | nil => exact Nat.le_refl 0
  | cons a l ih => exact Nat.add_le_add (h a) ih

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable (Q : Birth T v key prec tw bw page)
variable {k1 k2 ow : ℕ}
variable (owners : List (RefRow k1 (Word ow × Origin key prec page)))
variable (seats : List (RefRow k2 (SeatField (dim v) page)))
variable (queries : Port v.parent.host.Edge → Meter (Word k1 × Word k2 × Bool))
variable (fallback : Addon ow (dim v) key prec page)

theorem physical_fused_resident_bound :
    let rd := witnessedReader owners seats queries fallback
    let order := Q.native.physical.order
    let f := directInstall (fun h=>(Q.native.physical.record h).address) rd order
    f.steps ≤ 4+(order.map (fun h=>(queries h).steps+
      locateFee k1 owners.length+locateFee k2 seats.length+10+3*Q.port+11+
      addonFee ow (dim v) key prec page (rd h).result.oldOrigin.pageKey.isSome)).sum := by
  dsimp only
  rw [(direct_install_exact _ _ _).2]
  apply Nat.add_le_add_left
  apply list_sum_compare
  intro h
  have fee := resident_read_bound owners seats (queries h)
  have calcFee : (witnessedReader owners seats queries fallback h).steps=
      (residentRead owners seats (queries h)).steps+2 := rfl
  rw [calcFee]
  omega

#print axioms physical_fused_resident_bound
end J6R48GeneratedAddons

