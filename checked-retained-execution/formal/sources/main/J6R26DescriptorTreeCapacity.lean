import J6R26DescriptorTreeWhole

/-! A sufficient fresh number width from the printed root schedule.
The executor does not count future actual tickets to choose its word
width. This is only address capacity, not a bound on the sizes of
supplied physical Gate payloads. -/
namespace J6R26DescriptorTree
open scoped Polynomial BigOperators
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R16ModeCost

def printedKeyWidth (s C : ℕ) : ℕ :=
  let H := pathLimit s C
  let lam := Nat.clog 2 s
  H+(branchBits lam*H+24*depthScale s C lam (siteConstant C))+1

variable {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable (T : Prepared cfg sel r hf)

set_option maxHeartbeats 2400000 in
theorem printed_capacity (d₀ : r.depth=0) (p₀ : r.prec≤C*s) :
    (allTickets T).length<(2:ℕ)^printedKeyWidth s C := by
  let H := pathLimit s C
  let lam := Nat.clog 2 s
  let E := branchBits lam*H+24*depthScale s C lam (siteConstant C)
  have n : (allTickets T).length+1≤(H+1)*2^E := by
    rw [all_tickets_count T]
    exact total_native_occurrences cfg sel T.rootStable d₀ p₀
  have hH := J9PrintedSchedule.next_le_two_power H
  have fit := n.trans (Nat.mul_le_mul_right (2^E) hH)
  change (allTickets T).length<(2:ℕ)^(H+E+1)
  rw [←pow_add] at fit
  exact (Nat.lt_succ_self _).trans_le
    (fit.trans (Nat.pow_le_pow_right (by decide) (Nat.le_succ _)))

#print axioms printed_capacity
end J6R26DescriptorTree
