import J6R48GeneratedAddonsReader

/-! Apply the two-list resident decoder to the exact source-side port.
This replaces the generic readRow contract by address membership and
matching fields in the two actual, already resident, source tables. -/
namespace J6R48GeneratedAddons
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J6R26DescriptorTree J6R34ChildPath J6R33StatefulArithmeticPage J6R36ChildFramedRoute
open J6ActiveRun J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6R30ProducedGateRegistry J6R41StructuredAllPaths J6R27OriginalGate J6R20Ancestor
set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable (Q : Birth T v key prec tw bw page)
variable (previous : v.parent.host.Row⊕v.parent.host.Col→Origin key prec page)
variable {k1 k2 ow : ℕ}
variable (oldKey : v.parent.host.Row⊕v.parent.host.Col→Word ow)
variable (pageKey : PageAt T v→Word page)
variable (owners : List (RefRow k1 (Word ow × Origin key prec page)))
variable (seats : List (RefRow k2 (SeatField (dim v) page)))
variable (queries : Port v.parent.host.Edge → Meter (Word k1 × Word k2 × Bool))

abbrev rawSeat (h : Port v.parent.host.Edge) :=
  physicalSeatField (layout T v) (axis T v) pageKey (edge h)

abbrev rawOwner (h : Port v.parent.host.Edge) :=
  let u := owner v.parent.host.network h
  (oldKey u,previous u)

structure NativeTables : Prop where
  side_matches : ∀ h, (queries h).result.2.2=side h
  owner_hit : ∀ h, (⟨(queries h).result.1,rawOwner previous oldKey h⟩ : RefRow k1 _) ∈ owners
  owner_unique : ∀ h x, x∈owners → x.address=(queries h).result.1 → x.payload=rawOwner previous oldKey h
  seat_hit : ∀ h, (⟨(queries h).result.2.1,rawSeat pageKey h⟩ : RefRow k2 _) ∈ seats
  seat_unique : ∀ h x, x∈seats → x.address=(queries h).result.2.1 → x.payload=rawSeat pageKey h

theorem no_raw_row_miss (valid : NativeTables previous oldKey pageKey owners seats queries)
    (h : Port v.parent.host.Edge) :
    (residentRead owners seats (queries h)).result=some (addonAt T v oldKey previous pageKey h) := by
  rw [resident_read_hit _ _ _ _ _ (valid.owner_hit h) (valid.owner_unique h)
    (valid.seat_hit h) (valid.seat_unique h),valid.side_matches h]
  rfl

def witnessedReader (fallback : Addon ow (dim v) key prec page)
    (h : Port v.parent.host.Edge) : Meter (Addon ow (dim v) key prec page) :=
  let M := residentRead owners seats (queries h)
  ⟨M.result.getD fallback,M.steps+2⟩

theorem selected_table_bank (valid : NativeTables previous oldKey pageKey owners seats queries)
    (fallback : Addon ow (dim v) key prec page) :
    let rd := witnessedReader owners seats queries fallback
    let f := directInstall (fun h=>(Q.native.physical.record h).address) rd Q.native.physical.order
    f.result=Q.native.physical.order.map
      (fun h=>⟨(Q.native.physical.record h).address,addonAt T v oldKey previous pageKey h⟩) := by
  dsimp only
  rw [(direct_install_exact _ _ _).1]
  apply List.map_congr_left
  intro h _
  simp only [witnessedReader,no_raw_row_miss _ _ _ _ _ _ valid h,Option.getD_some]

#print axioms no_raw_row_miss
#print axioms selected_table_bank
end J6R48GeneratedAddons

