import J6R16ModeCostCompress

/-! The printed Appendix-D branching exponent for the entire finite
occurrence ledger, including the last level.  This is only a numerical
compression; it places no bound on a caller-supplied Meter. -/
namespace J6R56PrintedExponent
open J1PPrinted J6R16ModeCost
set_option autoImplicit false
set_option warningAsError true

def fullPrefixConstant (C : ℕ) : ℕ := prefixConstant C+12

theorem last_branch_le_leaf (s : ℕ) (large : 1024≤Nat.clog 2 s) :
    branchBits (Nat.clog 2 s)≤12*J9PrintedSchedule.leafThreshold s (Nat.clog 2 s) := by
  let lam := Nat.clog 2 s
  have hstep : lam+1≤(lam+1)^2 := by
    rw [pow_two]
    exact Nat.le_mul_of_pos_right _ (Nat.succ_pos lam)
  calc
    _≤12*(lam+1) := by unfold branchBits; omega
    _≤12*((lam+1)^2) := Nat.mul_le_mul_left _ hstep
    _≤_ := Nat.mul_le_mul_left _ (square_log_le_leaf s large)

theorem compress_including_last_level (s C : ℕ) (hC : 0<C)
    (size : (2*epsDen)^30*C^10≤Nat.clog 2 s) (large : 1024≤Nat.clog 2 s) :
    let lam := Nat.clog 2 s
    branchBits lam*(pathLimit s C+1)+24*depthScale s C lam (siteConstant C)
      ≤fullPrefixConstant C*J9PrintedSchedule.leafThreshold s lam := by
  let lam := Nat.clog 2 s
  let H := J9PrintedSchedule.leafThreshold s lam
  change branchBits lam*(pathLimit s C+1)+24*depthScale s C lam (siteConstant C)
    ≤fullPrefixConstant C*H
  calc
    _=(branchBits lam*pathLimit s C+24*depthScale s C lam (siteConstant C))+branchBits lam := by ring
    _≤prefixConstant C*H+12*H :=
      Nat.add_le_add (compress_exponent s C hC size large) (last_branch_le_leaf s large)
    _=_ := by unfold fullPrefixConstant; ring

theorem compress_from_absolute_start (s C absoluteDepth : ℕ) (hC : 0<C)
    (size : (2*epsDen)^30*C^10≤Nat.clog 2 s) (large : 1024≤Nat.clog 2 s) :
    let lam := Nat.clog 2 s
    branchBits lam*(pathLimit s C-absoluteDepth+1)+24*depthScale s C lam (siteConstant C)
      ≤fullPrefixConstant C*J9PrintedSchedule.leafThreshold s lam := by
  have n : pathLimit s C-absoluteDepth+1≤pathLimit s C+1 :=
    Nat.succ_le_succ (Nat.sub_le _ _)
  exact (Nat.add_le_add_right (Nat.mul_le_mul_left _ n) _).trans
    (compress_including_last_level s C hC size large)

theorem compress_absolute_meter_bound (s C absoluteDepth factor steps : ℕ) (hC : 0<C)
    (size : (2*epsDen)^30*C^10≤Nat.clog 2 s) (large : 1024≤Nat.clog 2 s)
    (h : steps≤factor*2^(branchBits (Nat.clog 2 s)*(pathLimit s C-absoluteDepth+1)+
      24*depthScale s C (Nat.clog 2 s) (siteConstant C))) :
    steps≤factor*2^(fullPrefixConstant C*J9PrintedSchedule.leafThreshold s (Nat.clog 2 s)) := by
  apply h.trans
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_right (by decide)
  exact compress_from_absolute_start s C absoluteDepth hC size large

#print axioms fullPrefixConstant
#print axioms last_branch_le_leaf
#print axioms compress_including_last_level
#print axioms compress_from_absolute_start
#print axioms compress_absolute_meter_bound
end J6R56PrintedExponent
