import J6R48BitCostProbe

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

/-! Price the entire R22 arithmetic at a native centre. The actual
normalizer roster is still required, but no semantic child callback
or assumption that a centre's result has already been computed. -/
namespace J6R48BitCost
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 A1R12
open J6R22Active J6ActiveSchedule

theorem quotient_loop_measured {p ell k : ℕ} {fw : List (Word p)}
    (hp : 0<p) (he : 0<fw.length) (hv : 0<ell) (hk : 0<k)
    (normal values : JetTape fw ell k) :
    (divideJet hp he hv hk normal values).steps ≤ quotientFee fw.length ell p k hp := by
  obtain ⟨E,hE⟩ := AdjoinRoot.mk_surjective (jetRead hp he normal)
  obtain ⟨F,hF⟩ := AdjoinRoot.mk_surjective (jetRead hp he values)
  exact (divideJet_exact hp he hv hk normal values E F hE.symm hF.symm).2

theorem resident_centre_core_measured {p ell k n : ℕ} {Mode : Type*}
    (I : SiteTape p ell k n Mode) (a M u : ℕ) {t : ℤ} (ht : t∈active a M u)
    (nodup : (I.roster.map Prod.fst).Nodup)
    (listExact : (I.roster.map Prod.fst).toFinset=(active a M u).erase t)
    (orderExact : ∀ q∈I.roster,q.2=order M u q.1) :
    (I.run a t).steps ≤ I.nodeBill+I.childBill+I.localFee a := by
  let N := I.normM a t
  let J := interpPrefix I.hp I.nonempty I.he I.hk I.nodeM I.groupedM
  let Q := divideJet I.hp I.nonempty I.he I.hk N.result J.result
  have hn : N.steps≤normalizerFee I.fw.length ell p a k I.hp I.roster :=
    (normalizerM_exact I.hp I.nonempty I.he I.hk a M u ht I.roster nodup listExact orderExact).2
  have hj := (interpPrefix_steps I.hp I.nonempty I.he I.hk I.nodeM I.groupedM).trans
    (Nat.add_le_add_right I.interp_bill _)
  have hq : Q.steps≤quotientFee I.fw.length ell p k I.hp :=
    quotient_loop_measured I.hp I.nonempty I.he I.hk N.result J.result
  change N.steps+J.steps+Q.steps+4≤_
  unfold SiteTape.localFee
  exact (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hn hj) hq) 4).trans
    (le_of_eq (by ac_rfl))

theorem resident_centre_probe_schedule {p ell k n : ℕ} {Mode : Type*}
    (I : SiteTape p ell k n Mode) (a M u : ℕ) {t : ℤ} (ht : t∈active a M u)
    (nodup : (I.roster.map Prod.fst).Nodup)
    (listExact : (I.roster.map Prod.fst).toFinset=(active a M u).erase t)
    (orderExact : ∀ q∈I.roster,q.2=order M u q.1) :
    (I.run a t).steps ≤ n*bill I.nodeM (probeOrder n)+I.childBill+I.localFee a :=
  (resident_centre_core_measured I a M u ht nodup listExact orderExact).trans
    (le_of_eq (by rw [site_probe_reload_exact]))

#print axioms quotient_loop_measured
#print axioms resident_centre_core_measured
#print axioms resident_centre_probe_schedule
end J6R48BitCost

