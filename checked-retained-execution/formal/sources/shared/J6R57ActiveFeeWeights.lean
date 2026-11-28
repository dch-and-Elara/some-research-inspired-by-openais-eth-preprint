import J6R57ActiveFeeKernels
import J6R23ScheduleWeightTerm
import J6R23ScheduleWeightBounds

/-! Bound the actual retained Hermite coefficient weight computation.
All powers are scanned at their printed bounded exponents; the source
nonnegative dyadic counters are carried separately from the UV words. -/
namespace J6R57ActiveFee
open A1R10 A1R11 A1R12 J6R22Active J6R23ScheduleWeight J6R19Retained
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 12000000
set_option maxRecDepth 3200
set_option Elab.async false

def partPx (K : ℕ) :=
  (19*K+14+14*(K+2)^2)+2*uvPx K+
  K*(mulPx K+4)+8*(K+1+K+3)^2+8

def rowWeightPx (K : ℕ) :=
  partPx K+mulPx K+8*(K+K*(K*K)+3)^2+10

def weightsFoldPx (K : ℕ) := (uvPx K+4)+K*rowWeightPx K

def weightPx (K : ℕ) :=
  weightsFoldPx K+weightsFoldPx K+3*uvPx K+oddPx K+2*(mulPx K+2)+2+
    4*(K+K+K*(K*K)+1)+8*(K+K+K+K*(K*K)+K*(K*K)+6)^2+10

def coefficientPx (K : ℕ) := K*(uvPx K+2)+6*(K+1)+4

def boxPx (K : ℕ) := boxFee K K K K

def termPx (K : ℕ) := coefficientPx K+boxPx K+weightPx K+mulPx K+6

private theorem bounded_count {t : ℤ} (kind : Side) (xs : List (ℤ×ℕ)) (K : ℕ)
    (h : ∀ q∈xs,factorCount t kind q ≤ K) : countParts t kind xs ≤ xs.length*K := by
  induction xs with
  | nil => simp [countParts]
  | cons q xs ih =>
    have a := h q List.mem_cons_self
    have b := ih (fun p hp=>h p (List.mem_cons_of_mem _ hp))
    change factorCount t kind q+countParts t kind xs ≤ (xs.length+1)*K
    rw [Nat.succ_mul xs.length]
    omega

variable {e ell p K : ℕ} (cap : BitCaps e ell p K)

include cap in
theorem actual_power_part_cap {a n : ℕ} (ha : a ≤ K) (hn : n ≤ K) :
    partCap e ell p (a+1) n ≤ partPx K := by
  have u := uv_word_cap cap
  have m := multiplication_cap cap
  have pp := cap.precision
  unfold partCap partPx dyadicCap
  have eq : K+1+1=K+2 := by omega
  rw [←eq]
  gcongr

include cap in
theorem actual_weight_fold_arithmetic_cap {a : ℕ} (ha : a ≤ K) (t : ℤ) (side : Side)
    (xs : List (ℤ×ℕ)) (len : xs.length ≤ K)
    (pow : ∀ q∈xs,q.2 ≤ K) (counts : ∀ q∈xs,factorCount t side q ≤ K*K) :
    foldFee e ell p a t side xs ≤ (uvPx K+4)+xs.length*rowWeightPx K := by
  induction xs with
  | nil => simpa only [foldFee,List.length_nil,Nat.zero_mul,Nat.add_zero] using
      Nat.add_le_add_right (uv_word_cap cap) 4
  | cons q xs ih =>
    have nb : xs.length ≤ K := (Nat.le_succ _).trans len
    have bounds := ih nb
      (fun v hv=>pow v (List.mem_cons_of_mem _ hv))
      (fun v hv=>counts v (List.mem_cons_of_mem _ hv))
    have weight := actual_power_part_cap cap ha (pow q List.mem_cons_self)
    have totals := (bounded_count side (q::xs) _ counts).trans (Nat.mul_le_mul_right _ len)
    change factorCount t side q+countParts t side xs ≤ K*(K*K) at totals
    have plus : a+factorCount t side q+countParts t side xs+3 ≤ K+K*(K*K)+3 := by omega
    have m := multiplication_cap cap
    calc
      _ ≤ partPx K+((uvPx K+4)+xs.length*rowWeightPx K)+
          mulPx K+8*(K+K*(K*K)+3)^2+10 := by
        rw [foldFee]
        gcongr
      _=_ := by
        simp only [List.length_cons,Nat.succ_mul,rowWeightPx]
        ring

include cap in
theorem actual_weight_arithmetic_cap (hp : 0<p) {a B j : ℕ}
    (ha : a ≤ K) (hB : B ≤ K) (hj : j ≤ K) (t : ℤ)
    (xs : List (ℤ×ℕ)) (len : xs.length+1 ≤ K) (pow : ∀ q∈xs,q.2 ≤ K)
    (num : ∀ q∈xs++[(t,j)],factorCount t .num q ≤ K*K)
    (den : ∀ q∈xs,factorCount t .den q ≤ K*K) :
    rawWeightFee e ell p a B j hp t xs ≤ weightPx K := by
  let ys := xs++[(t,j)]
  have ln : ys.length ≤ K := by simpa only [ys,List.length_append,List.length_singleton] using len
  have ld : xs.length ≤ K := (Nat.le_succ _).trans len
  have qp (q : ℤ×ℕ) (hq : q∈ys) : q.2 ≤ K := by
    rcases List.mem_append.mp hq with h | h
    · exact pow q h
    · rw [List.mem_singleton] at h
      subst q
      exact hj
  have fn : foldFee e ell p a t .num ys ≤ weightsFoldPx K :=
    (actual_weight_fold_arithmetic_cap cap ha t .num ys ln qp num).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ ln) _)
  have fd : foldFee e ell p a t .den xs ≤ weightsFoldPx K :=
    (actual_weight_fold_arithmetic_cap cap ha t .den xs ld pow den).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ ld) _)
  have cn := (bounded_count .num ys _ num).trans (Nat.mul_le_mul_right _ ln)
  have cd := (bounded_count .den xs _ den).trans (Nat.mul_le_mul_right _ ld)
  have u := uv_word_cap cap
  have o := odd_arithmetic_cap cap hp
  have m := multiplication_cap cap
  have pp := cap.precision
  unfold rawWeightFee weightPx
  dsimp only
  change foldFee e ell p a t .num ys+foldFee e ell p a t .den xs+3*uvWidth e ell p+
      oddCap e ell p hp+2*(mulCap e ell p+2)+2+4*(p+B+countParts t .num ys+1)+
      8*(a+B+j+countParts t .num ys+countParts t .den xs+6)^2+10 ≤ _
  gcongr

include cap in
theorem actual_term_arithmetic_cap {q a B k j : ℕ} (new : BitCaps e ell q K)
    (hq : 0<q) (ha : a ≤ K) (hB : B ≤ K) (hk : k ≤ K) (hj : j ≤ K) (t : ℤ)
    (xs : List (ℤ×ℕ)) (len : xs.length+1 ≤ K) (pow : ∀ x∈xs,x.2 ≤ K)
    (num : ∀ x∈xs++[(t,j)],factorCount t .num x ≤ K*K)
    (den : ∀ x∈xs,factorCount t .den x ≤ K*K) :
    termFee e ell p q a B k j hq t xs ≤ termPx K := by
  have hw := actual_weight_arithmetic_cap new hq ha hB hj t xs len pow num den
  have hm := multiplication_cap new
  have cf : jetCoeffFee e ell p k ≤ coefficientPx K := by
    have u := uv_word_cap cap
    unfold jetCoeffFee coefficientPx jetEntryWidth
    gcongr
  have bk : boxFee e ell p q ≤ boxPx K := by
    have he := cap.degree
    have hn := cap.vLength
    have hp := cap.precision
    have qn := new.precision
    unfold boxPx boxFee scalarFee wordFee
    gcongr
  unfold termFee termPx
  gcongr

#print axioms actual_weight_fold_arithmetic_cap
#print axioms actual_weight_arithmetic_cap
#print axioms actual_term_arithmetic_cap
end J6R57ActiveFee
