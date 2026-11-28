
import J6R29BinaryFieldSearchRun

/-! A polynomial bit-work envelope for the original exhaustive search.
Here e = 4 ceil(log₂ s); no faster factoring method is substituted. -/
namespace J6R29BinaryFieldSearch
open J6R27PrescribedProbe
set_option maxHeartbeats 5200000
set_option maxRecDepth 1300

theorem trial_upper_quadratic (e : ℕ) : trialUpper e≤400*(e+1)^2 := by
  unfold trialUpper
  nlinarith [Nat.zero_le (e*e)]

theorem candidate_fee_bound (e : ℕ) : candidateFee e≤64*(e+1)*2^e := by
  let q : ℕ := 2^e
  have hq : 1≤q := Nat.one_le_iff_ne_zero.mpr (by dsimp [q]; positivity)
  have tape := Nat.mul_le_mul_right (20*e+6) (Nat.sub_le q 1)
  have init : 15+7*e≤q*(15+7*e) := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (15+7*e) hq
  change 4+(q-1)*(20*e+6)+3*e+6+4*e+5≤64*(e+1)*q
  calc
    _ ≤ q*(15+7*e)+q*(20*e+6) := by omega
    _ ≤ q*(64*(e+1)) := by rw [←Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega)
    _ = _ := Nat.mul_comm _ _

theorem divisor_fee_bound (d : ℕ) : divisorFee d≤128*(d+1)*2^(d+1) := by
  induction d with
  | zero => decide
  | succ d ih =>
    let q : ℕ := 2^(d+1)
    have hq : 1≤q := Nat.one_le_iff_ne_zero.mpr (by dsimp [q]; positivity)
    have prev : divisorFee d≤128*(d+1)*q := ih
    have row : candidateFee (d+1)≤64*(d+2)*q := candidate_fee_bound (d+1)
    have five : 5≤q*5 := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right 5 hq
    change candidateFee (d+1)+divisorFee d+q*(4*(d+1)+10)+5≤128*(d+2)*2^(d+1+1)
    rw [pow_succ 2 (d+1)]
    change _≤128*(d+2)*(q*2)
    calc
      _ ≤ 64*(d+2)*q+128*(d+1)*q+q*(4*(d+1)+10)+q*5 :=
        Nat.add_le_add (Nat.add_le_add (Nat.add_le_add row prev) (Nat.le_refl _)) five
      _ = q*(64*(d+2)+128*(d+1)+(4*(d+1)+10)+5) := by ring
      _ ≤ q*(256*(d+2)) := Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring

theorem field_search_fee_bound (e : ℕ) :
    fieldSearchFee e≤1024*(e+1)^2*2^e*2^(e/2+1) := by
  let Q : ℕ := 2^e
  let H : ℕ := 2^(e/2+1)
  let A : ℕ := (e+1)^2
  have q : 1≤Q := Nat.one_le_iff_ne_zero.mpr (by dsimp [Q]; positivity)
  have h : 1≤H := Nat.one_le_iff_ne_zero.mpr (by dsimp [H]; positivity)
  have a : 1≤A := Nat.one_le_iff_ne_zero.mpr (by dsimp [A]; positivity)
  have amp : e+1≤A := by
    dsimp only [A]
    rw [pow_two]
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (e+1) (show 1≤e+1 by omega)
  have du : e/2+1≤A := (Nat.add_le_add_right (Nat.div_le_self e 2) 1).trans amp
  have leCnt : divisorCount (e/2)≤H := Nat.sub_le _ _
  have mulTrial : divisorCount (e/2)*(trialUpper e+6)≤H*(406*A) :=
    Nat.mul_le_mul leCnt (by
      have z : trialUpper e≤400*A := trial_upper_quadratic e
      omega)
  have hLin : 4+e+6≤16*A := by omega
  have hScale : 16*A≤H*(16*A) := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right _ h
  have allTrial : 4+divisorCount (e/2)*(trialUpper e+6)+e+6≤512*A*H := by
    calc
      _ ≤ H*(406*A)+H*(16*A) := by omega
      _ ≤ H*(512*A) := by rw [←Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega)
      _ = _ := Nat.mul_comm _ _
  have first : candidateFee e≤64*A*Q*H :=
    (candidate_fee_bound e).trans ((Nat.mul_le_mul_right Q (Nat.mul_le_mul_left 64 amp)).trans (by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (64*A*Q) h))
  have second : divisorFee (e/2)≤128*A*Q*H := by
    calc
      _ ≤ 128*(e/2+1)*H := divisor_fee_bound (e/2)
      _ ≤ 128*A*H := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ du)
      _ ≤ 128*A*H*Q := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left _ q
      _ = _ := by ring
  have last : 10≤10*A*Q*H := by
    have P : 1≤A*Q*H := by exact Nat.one_le_iff_ne_zero.mpr (by positivity)
    simpa only [Nat.mul_one,Nat.mul_assoc] using Nat.mul_le_mul_left 10 P
  change candidateFee e+divisorFee (e/2)+4+
      Q*(4+divisorCount (e/2)*(trialUpper e+6)+e+6)+6≤1024*A*Q*H
  have mid := Nat.mul_le_mul_left Q allTrial
  calc
    _ ≤ 64*A*Q*H+128*A*Q*H+Q*(512*A*H)+10*A*Q*H := by omega
    _ = 714*A*Q*H := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide)))

theorem pow_clog_two_bound (s : ℕ) (hs : 1<s) :
    (2:ℕ)^Nat.clog 2 s≤2*s := by
  have H := Nat.le_pow_clog (b:=2) (by decide) s
  have pos : 0<Nat.clog 2 s := by
    by_contra np
    have z : Nat.clog 2 s=0 := by omega
    rw [z,pow_zero] at H
    omega
  have h := Nat.pow_pred_clog_lt_self (b:=2) (by decide) hs
  have a := Nat.mul_le_mul_right 2 (Nat.le_of_lt h)
  have b : (Nat.clog 2 s).pred+1=Nat.clog 2 s := Nat.succ_pred_eq_of_pos pos
  rw [←pow_succ,b] at a
  exact a.trans_eq (Nat.mul_comm _ _)

theorem printed_field_search_polynomial (s : ℕ) (hs : 1<s) :
    fieldSearchFee (4*Nat.clog 2 s)≤(1024*9^2*2*2^6)*s^8 := by
  let k := Nat.clog 2 s
  let e := 4*k
  have pk : (2:ℕ)^k≤2*s := pow_clog_two_bound s hs
  have kBound : k≤2*s := (Nat.le_of_lt (Nat.lt_pow_self (n:=k) (a:=2) (by decide))).trans pk
  have eBound : e+1≤9*s := by dsimp only [e]; omega
  have ex : e+(e/2+1)=k*6+1 := by dsimp only [e]; omega
  have powE : (2:ℕ)^e*2^(e/2+1)=2*((2^k)^6) := by
    rw [←pow_add,ex,pow_succ 2 (k*6),pow_mul]
    exact Nat.mul_comm _ _
  change fieldSearchFee e≤_
  calc
    _ ≤ 1024*(e+1)^2*2^e*2^(e/2+1) := field_search_fee_bound e
    _ = (1024*(e+1)^2)*(2^e*2^(e/2+1)) := Nat.mul_assoc _ _ _
    _ = 1024*(e+1)^2*(2*((2^k)^6)) := congrArg (fun t=>1024*(e+1)^2*t) powE
    _ ≤ 1024*(9*s)^2*(2*((2*s)^6)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left eBound _))
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left pk _))
    _ = _ := by ring

#print axioms trial_upper_quadratic
#print axioms candidate_fee_bound
#print axioms divisor_fee_bound
#print axioms field_search_fee_bound
#print axioms printed_field_search_polynomial
end J6R29BinaryFieldSearch
