import J6R48BitCostSite
import J6R24MeteredRecursionLedger

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 9000000

/-! Measure the real quotient-jet kernel with any metered sample
supplier, including the halt-driven sampler. The literal slot reading
is retained in the fee rather than modeled as a free ring oracle. -/
namespace J6R49Cost
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 A1R12
open J6R22Active J6ActiveSchedule J6R48BitCost J6R24MeteredRecursion

theorem full_center_kernel_actual_bill {p ell k n : ℕ} {fw : List (Word p)}
    (hp : 0<p) (he : 0<fw.length) (hv : 0<ell) (hk : 0<k)
    (node sample : Fin n→Meter (UVBlock fw ell)) (norm : Meter (JetTape fw ell k)) :
    (fullCenterM hp he hv hk node sample norm).steps ≤
      bill sample (probeOrder n)+(norm.steps+((probeOrder n).map (needsAt node)).sum+
        interpExtra fw.length ell p k n hp+quotientFee fw.length ell p k hp+4) := by
  let J := interpPrefix hp he hv hk node sample
  let Q := divideJet hp he hv hk norm.result J.result
  have hJ : J.steps ≤ interpBill node sample+interpExtra fw.length ell p k n hp :=
    interpPrefix_steps hp he hv hk node sample
  have hQ : Q.steps ≤ quotientFee fw.length ell p k hp :=
    quotient_loop_measured hp he hv hk norm.result J.result
  have split : interpBill node sample =
      ((probeOrder n).map (needsAt node)).sum+bill sample (probeOrder n) :=
    list_charge _ _ _ _ (fun _ _ => rfl)
  rw [split] at hJ
  change norm.steps+J.steps+Q.steps+4 ≤ _
  omega

theorem full_rostered_center_actual_bill {p ell k n : ℕ} {fw : List (Word p)}
    (hp : 0<p) (he : 0<fw.length) (hv : 0<ell) (hk : 0<k)
    (node sample : Fin n→Meter (UVBlock fw ell)) (a M u : ℕ) {t : ℤ}
    (ht : t∈active a M u) (rows : List (ℤ×ℕ))
    (nd : (rows.map Prod.fst).Nodup)
    (rowsExact : (rows.map Prod.fst).toFinset=(active a M u).erase t)
    (ord : ∀ q∈rows,q.2=order M u q.1) :
    (fullCenterM hp he hv hk node sample (normalizerM hp he hv hk a t rows)).steps ≤
      bill sample (probeOrder n)+(normalizerFee fw.length ell p a k hp rows+
        ((probeOrder n).map (needsAt node)).sum+
        interpExtra fw.length ell p k n hp+quotientFee fw.length ell p k hp+4) := by
  have Cost := full_center_kernel_actual_bill hp he hv hk node sample (normalizerM hp he hv hk a t rows)
  have Norm := (normalizerM_exact hp he hv hk a M u ht rows nd rowsExact ord).2
  exact Cost.trans (Nat.add_le_add_left (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_right (Nat.add_le_add_right Norm _) _) _) _) _)

#print axioms full_center_kernel_actual_bill
#print axioms full_rostered_center_actual_bill
end J6R49Cost

