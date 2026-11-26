import P5FrontendG1NormalizationPrinted

/-! Exact source hashing dimensions. This verifies the integer dimensions
determining the printed two-sided index set. It does not replace the
source's separate existence/search proofs for the shifts and local code. -/
namespace Paper5.FrontendG1.Tanner
open Paper5.NativeEntry

def sourceMu (m : ℕ) : ℕ := Nat.log 2 m+1
def sourceD (B m : ℕ) : ℕ := 320000*B^2*(sourceMu m)^3
def sourceDegree (B m : ℕ) : ℕ := min m (sourceD B m)
def ceilNat (n d : ℕ) : ℕ := (n+d-1)/d
def sourceEll (B m : ℕ) : ℕ := Nat.clog 2 (ceilNat m (sourceDegree B m))
def sourceQ (B m : ℕ) : ℕ := 2^(sourceEll B m)
def sourceLocalRows (B m : ℕ) : ℕ := ceilNat (sourceDegree B m) (8*B)
def sourceDelta (B m : ℕ) : ℚ := 1/(100*(B:ℚ)*(sourceMu m:ℚ))
def sourceMinDistance (B m : ℕ) : ℚ := sourceDelta B m*(sourceDegree B m:ℚ)

theorem source_d_pos {B m : ℕ} (hB : 0<B) (hm : 0<m) : 0<sourceDegree B m := by
  unfold sourceDegree
  apply lt_min hm
  unfold sourceD sourceMu
  positivity

theorem ceilNat_le_iff (n d k : ℕ) (hd : 0<d) :
    ceilNat n d≤k ↔ n≤k*d := by
  unfold ceilNat
  constructor
  · intro hh
    have h := (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_of_le hh)
    rw [Nat.succ_mul] at h
    omega
  · intro hh
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul hd).mpr
    rw [Nat.succ_mul]
    omega

theorem source_q_covers {B m : ℕ} (hB : 0<B) (hm : 0<m) :
    m≤sourceQ B m*sourceDegree B m := by
  apply (ceilNat_le_iff _ _ _ (source_d_pos hB hm)).mp
  exact Nat.le_pow_clog (by decide) _

theorem source_q_least {B m : ℕ} (hB : 0<B) (hm : 0<m) (a : ℕ) (ha : a<sourceEll B m) :
    (2:ℕ)^a*sourceDegree B m<m := by
  have hp : (2:ℕ)^a < ceilNat m (sourceDegree B m) := by
    exact (Nat.lt_clog_iff_pow_lt (by decide)).mp ha
  exact lt_of_not_ge fun h =>
    (not_le_of_gt hp) ((ceilNat_le_iff _ _ _ (source_d_pos hB hm)).mpr h)

theorem source_q_slots_lt_twice {B m : ℕ} (hB : 0<B) (hm : 0<m) :
    sourceQ B m*sourceDegree B m<2*m := by
  by_cases hZero : sourceEll B m=0
  · have hd : sourceDegree B m≤m := Nat.min_le_left _ _
    simp only [sourceQ,hZero,pow_zero,one_mul]
    omega
  · have hprev : sourceEll B m-1<sourceEll B m := by omega
    have hp := source_q_least hB hm _ hprev
    have hconst : (2:ℕ)^(sourceEll B m) =
        2*2^(sourceEll B m-1) := by
      conv_lhs => rw [show sourceEll B m=(sourceEll B m-1)+1 by omega,pow_succ']
    unfold sourceQ
    rw [hconst,mul_assoc]
    omega

theorem source_q_gt_one_of_D_lt {B m : ℕ} (hB : 0<B) (hm : 0<m)
    (hd : sourceD B m<m) : 1<sourceQ B m := by
  have hcover := source_q_covers hB hm
  rw [sourceDegree,min_eq_right (le_of_lt hd)] at hcover
  by_contra! h
  have hh := Nat.mul_le_mul_right (sourceD B m) h
  omega

theorem source_d_eq_D_of_q_gt_one {B m : ℕ} (hB : 0<B) (hm : 0<m)
    (hq : 1<sourceQ B m) : sourceDegree B m=sourceD B m := by
  have hL : 0<sourceEll B m := by
    by_contra! hn
    have h0 : sourceEll B m=0 := by omega
    simp [sourceQ,h0] at hq
  have hr := source_q_least hB hm 0 hL
  simp only [pow_zero,one_mul] at hr
  unfold sourceDegree at *
  omega

theorem source_D_ge_eight_B {B m : ℕ} (hB : 0<B) : 8*B≤sourceD B m := by
  have hi : 0<40000*B*(sourceMu m)^3 := by
    unfold sourceMu
    positivity
  calc
    _ = (8*B)*1 := by rw [mul_one]
    _ ≤ (8*B)*(40000*B*(sourceMu m)^3) :=
      Nat.mul_le_mul_left _ (Nat.one_le_of_lt hi)
    _ = sourceD B m := by unfold sourceD; ring

theorem source_distance_large_exact {B m : ℕ} (hB : 0<B)
    (hD : sourceDegree B m=sourceD B m) :
    sourceMinDistance B m = 3200*(B:ℚ)*(sourceMu m:ℚ)^2 := by
  have hBq : (B:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hB)
  have hMuq : (sourceMu m:ℚ)≠0 := by
    exact_mod_cast (show sourceMu m≠0 by unfold sourceMu; omega)
  rw [sourceMinDistance,sourceDelta,hD,sourceD]
  push_cast
  field_simp
  ring

theorem source_distance_gt_one {B m : ℕ} (hB : 0<B) (hm : 0<m)
    (hq : 1<sourceQ B m) : 1<sourceMinDistance B m := by
  rw [source_distance_large_exact hB (source_d_eq_D_of_q_gt_one hB hm hq)]
  have hBq : (1:ℚ)≤B := by exact_mod_cast (Nat.one_le_of_lt hB)
  have hMuq : (1:ℚ)≤sourceMu m := by
    exact_mod_cast (show 1≤sourceMu m by unfold sourceMu; omega)
  have hh : (1:ℚ)≤(B:ℚ)*(sourceMu m:ℚ)^2 :=
    one_le_mul_of_one_le_of_one_le hBq (one_le_pow₀ hMuq)
  calc
    _ < (3200:ℚ) := by norm_num
    _ ≤ _ := by simpa [mul_assoc] using mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℚ)≤3200)

theorem source_indexed_rows_strict {B m : ℕ} (hB : 0<B) (hm : 0<m)
    (hq : 1<sourceQ B m) :
    (2*sourceQ B m*sourceLocalRows B m)*B<m := by
  let d := sourceDegree B m
  let q := sourceQ B m
  let c := sourceLocalRows B m
  have h8d : 8*B≤d := by
    dsimp [d]
    rw [source_d_eq_D_of_q_gt_one hB hm hq]
    exact source_D_ge_eight_B hB
  have c_mul : c*(8*B)≤d+8*B-1 := Nat.div_mul_le_self _ _
  have hh : (8*B)*c≤d+d := by
    rw [mul_comm (8*B) c]
    omega
  have h4 : 4*B*c≤d := by
    have he : 8*B*c=2*(4*B*c) := by ring
    omega
  have hmain : 2*((2*q*c)*B)≤q*d := by
    calc
      _ = q*(4*B*c) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ h4
  have hq2 : q*d<2*m := source_q_slots_lt_twice hB hm
  change (2*q*c)*B<m
  omega

#print axioms source_d_pos
#print axioms ceilNat_le_iff
#print axioms source_q_covers
#print axioms source_q_least
#print axioms source_q_slots_lt_twice
#print axioms source_q_gt_one_of_D_lt
#print axioms source_d_eq_D_of_q_gt_one
#print axioms source_D_ge_eight_B
#print axioms source_distance_large_exact
#print axioms source_distance_gt_one
#print axioms source_indexed_rows_strict
end Paper5.FrontendG1.Tanner