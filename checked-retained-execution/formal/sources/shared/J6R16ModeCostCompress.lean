import J6R16ModeCostTotals

/-! The polynomial branching prefix contributes no extra asymptotic
exponent. An explicit integer constant times the actual printed leaf
threshold bounds the full depth exponent. -/
namespace J6R16ModeCost
open J1PPrinted
open scoped Polynomial BigOperators
open J6ActiveRun J6R10Reachable J6R12Blueprint J6R11Blueprint

theorem square_log_le_leaf (s : ℕ) (hl : 1024≤Nat.clog 2 s) :
    (Nat.clog 2 s+1)^2≤J9PrintedSchedule.leafThreshold s (Nat.clog 2 s) := by
  let lam := Nat.clog 2 s
  let n := lam-1
  let H := J9PrintedSchedule.leafThreshold s lam
  have hp : 0<lam.sqrt := Nat.sqrt_pos.mpr (by omega)
  have hN : 32≤n := by unfold n; omega
  have hCube : (lam+1)^3≤(2:ℕ)^n := by
    calc
      _≤(2*n)^3 := Nat.pow_le_pow_left (by unfold n; omega) _
      _=8*n^3 := by rw [mul_pow]; rfl
      _≤16*n^5 := Nat.mul_le_mul (by decide)
        (Nat.pow_le_pow_right (by omega) (by decide))
      _≤_ := sixteen_pow5_le n hN
  have hs : (2:ℕ)^n<s := (Nat.lt_clog_iff_pow_lt (by decide)).mp (by unfold n lam; omega)
  have hi : s≤H*lam.sqrt := J9PrintedSchedule.le_roundup_mul s lam.sqrt hp
  apply Nat.le_of_mul_le_mul_right _ hp
  calc
    (lam+1)^2*lam.sqrt≤(lam+1)^2*(lam+1) :=
      Nat.mul_le_mul_left _ ((Nat.sqrt_le_self _).trans (Nat.le_succ _))
    _=(lam+1)^3 := rfl
    _≤H*lam.sqrt := (hCube.trans hs.le).trans hi

theorem depth_scale_le_leaf (s C lam K : ℕ) (hl : 0<lam) :
    depthScale s C lam K≤(12*K*epsDen)*C*J9PrintedSchedule.leafThreshold s lam := by
  let A := 12*K*epsDen
  let H := J9PrintedSchedule.leafThreshold s lam
  let R := A*C*H
  by_cases ha : A=0
  · change Nat.sqrt ((A*(C*s)*(C*s))/lam)≤R
    simp [ha,R]
  · have hA : 0<A := Nat.pos_of_ne_zero ha
    have hd : s≤H*lam.sqrt := J9PrintedSchedule.le_roundup_mul s lam.sqrt (Nat.sqrt_pos.mpr hl)
    have hq : A*(C*s)*(C*s)≤(R*R)*lam := by
      calc
        _=(A*C*C)*(s*s) := by ring
        _≤(A*C*C)*((H*lam.sqrt)*(H*lam.sqrt)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hd hd)
        _=(A*(C*H)*(C*H))*(lam.sqrt*lam.sqrt) := by ring
        _≤(A*(C*H)*(C*H))*lam := Nat.mul_le_mul_left _ (Nat.sqrt_le lam)
        _=((C*H)*(C*H)*lam)*A := by ring
        _≤((C*H)*(C*H)*lam)*(A*A) :=
          Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hA)
        _=(R*R)*lam := by unfold R; ring
    have hDiv : (A*(C*s)*(C*s))/lam≤R*R := by
      apply Nat.le_of_lt_succ
      apply (Nat.div_lt_iff_lt_mul hl).mpr
      exact hq.trans_lt (Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) hl)
    change Nat.sqrt ((A*(C*s)*(C*s))/lam)≤R
    exact (Nat.sqrt_le_sqrt hDiv).trans_eq (Nat.sqrt_eq R)

def prefixConstant (C : ℕ) : ℕ := 12+24*(12*(siteConstant C)*epsDen)*C

theorem compress_exponent (s C : ℕ) (hC : 0<C)
    (hsize : (2*epsDen)^30*C^10≤Nat.clog 2 s) (hLam : 1024≤Nat.clog 2 s) :
    let lam := Nat.clog 2 s
    branchBits lam*pathLimit s C+24*depthScale s C lam (siteConstant C)≤
      prefixConstant C*J9PrintedSchedule.leafThreshold s lam := by
  let lam := Nat.clog 2 s
  let H := J9PrintedSchedule.leafThreshold s lam
  let A := 12*(siteConstant C)*epsDen
  have hp : 0<lam := by omega
  have he : pathLimit s C≤lam+1 := path_limit_le s C hC hp hsize
  have hF : branchBits lam≤12*(lam+1) := by unfold branchBits; omega
  have hP : branchBits lam*pathLimit s C≤12*H := by
    calc
      _≤(12*(lam+1))*(lam+1) := Nat.mul_le_mul hF he
      _=12*(lam+1)^2 := by ring
      _≤_ := Nat.mul_le_mul_left _ (square_log_le_leaf s hLam)
  have hX := depth_scale_le_leaf s C lam (siteConstant C) hp
  change depthScale s C lam (siteConstant C)≤A*C*H at hX
  change branchBits lam*pathLimit s C+24*depthScale s C lam (siteConstant C)≤prefixConstant C*H
  calc
    _≤12*H+24*(A*C*H) := Nat.add_le_add hP (Nat.mul_le_mul_left 24 hX)
    _=_ := by unfold prefixConstant A; ring

variable {f : ℤ[X]} {ell s C : ℕ}
variable (cfg : RootBounds s C f)
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
variable {r : Call (PhysicalHost f ell)}

theorem total_metered_printed_rate (hr : Stable s C r) (hzero : r.depth=0) (hroot : r.prec≤C*s)
    (T : TapeSupply sel r (uniformWidth s C)) :
    let lam := Nat.clog 2 s
    let H := pathLimit s C
    (∑ j∈Finset.range H,((occurrences (Plan sel) r j).map (measuredCall cfg sel hr T)).sum)≤
      H*uniformFee s C*2^(prefixConstant C * J9PrintedSchedule.leafThreshold s lam) := by
  apply (total_measured_mode_cost cfg sel hr hzero hroot T).trans
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_right (by decide)
  exact compress_exponent s C cfg.constPos cfg.size (root_lambda_large cfg)

#print axioms square_log_le_leaf
#print axioms depth_scale_le_leaf
#print axioms compress_exponent
#print axioms total_metered_printed_rate
end J6R16ModeCost


