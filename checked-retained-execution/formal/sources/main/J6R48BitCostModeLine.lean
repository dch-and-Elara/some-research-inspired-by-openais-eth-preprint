import J6R48BitCostSite

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4200000

/-! Separate the mode-independent site budget from the linear charge
for the actual probe × tuple roster. The empty-roster record appears
only in this arithmetic tariff, never in the evaluated program. -/
namespace J6R48BitCost
open A1R11 A1R12 J6R22Active J6ActiveSchedule

def ratePerTuple {p ell k n : ℕ} {Mode : Type*}
    (I : SiteTape p ell k n Mode) : ℕ :=
  tupleExtra I.fw.length ell p 64+addCap I.fw.length ell p I.hp+2

def fixedSiteFee {p ell k n : ℕ} {Mode : Type*}
    (I : SiteTape p ell k n Mode) (a : ℕ) : ℕ :=
  ({I with modes:=[]}).localFee a

theorem site_fee_exact_affine {p ell k n : ℕ} {Mode : Type*}
    (I : SiteTape p ell k n Mode) (a : ℕ) :
    I.localFee a = fixedSiteFee I a + (n * I.modes.length) * ratePerTuple I := by
  unfold fixedSiteFee SiteTape.localFee probeExtra ratePerTuple
  simp only [List.length_nil,zero_mul,Nat.add_zero,Nat.mul_add,Nat.mul_assoc]
  ac_rfl

theorem resident_centre_affine_schedule {p ell k n : ℕ} {Mode : Type*}
    (I : SiteTape p ell k n Mode) (a M u : ℕ) {t : ℤ} (ht : t∈active a M u)
    (nodup : (I.roster.map Prod.fst).Nodup)
    (listExact : (I.roster.map Prod.fst).toFinset=(active a M u).erase t)
    (orderExact : ∀ q∈I.roster,q.2=order M u q.1) :
    (I.run a t).steps ≤ n*bill I.nodeM (probeOrder n)+I.childBill+
       fixedSiteFee I a + (n*I.modes.length)*ratePerTuple I := by
  have h := resident_centre_probe_schedule I a M u ht nodup listExact orderExact
  rw [site_fee_exact_affine,←Nat.add_assoc] at h
  exact h

#print axioms site_fee_exact_affine
#print axioms resident_centre_affine_schedule
end J6R48BitCost

