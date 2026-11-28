import J6R48GeneratedAddonsPhysical

/-! Concrete charged row decoder: the owner/origin and seat fields are
located in two resident tables. A checked miss does not manufacture a
valid descriptor. Producing the certified table headers is separate. -/
namespace J6R48GeneratedAddons
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J6R26DescriptorTree J6R34ChildPath J6R33StatefulArithmeticPage J6R36ChildFramedRoute
open J6ActiveRun J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6R30ProducedGateRegistry J6R41StructuredAllPaths J6R27OriginalGate
set_option autoImplicit false

def residentRead {w u owner a key prec page : ℕ}
    (owners : List (RefRow w (Word owner × Origin key prec page)))
    (seats : List (RefRow u (SeatField a page)))
    (query : Meter (Word w × Word u × Bool)) :
    Meter (Option (Addon owner a key prec page)) :=
  let first := locate query.result.1 owners
  let second := locate query.result.2.1 seats
  let result := do
    let o ← first.result
    let s ← second.result
    pure ⟨o.1,o.2,query.result.2.2,s.slot,s.page⟩
  ⟨result,query.steps+first.steps+second.steps+8⟩

theorem resident_read_bound {w u owner a key prec page : ℕ}
    (owners : List (RefRow w (Word owner × Origin key prec page)))
    (seats : List (RefRow u (SeatField a page)))
    (query : Meter (Word w × Word u × Bool)) :
    (residentRead owners seats query).steps ≤
      query.steps+locateFee w owners.length+locateFee u seats.length+8 := by
  have a := locate_bound query.result.1 owners
  have b := locate_bound query.result.2.1 seats
  unfold residentRead
  dsimp only
  omega

theorem resident_read_hit {w u owner a key prec page : ℕ}
    (owners : List (RefRow w (Word owner × Origin key prec page)))
    (seats : List (RefRow u (SeatField a page)))
    (query : Meter (Word w × Word u × Bool)) (x : Word owner × Origin key prec page)
    (y : SeatField a page)
    (ho : (⟨query.result.1,x⟩ : RefRow w _) ∈ owners)
    (uo : ∀ r∈owners, r.address=query.result.1 → r.payload=x)
    (hs : (⟨query.result.2.1,y⟩ : RefRow u _) ∈ seats)
    (us : ∀ r∈seats, r.address=query.result.2.1 → r.payload=y) :
    (residentRead owners seats query).result=some ⟨x.1,x.2,query.result.2.2,y.slot,y.page⟩ := by
  unfold residentRead
  dsimp only
  rw [locate_hit _ _ _ ho uo,locate_hit _ _ _ hs us]
  rfl

#print axioms resident_read_bound
#print axioms resident_read_hit
end J6R48GeneratedAddons

