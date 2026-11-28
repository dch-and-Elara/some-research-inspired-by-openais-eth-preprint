import J6R21AncestorRun

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6400000
set_option maxRecDepth 2300

/-! Separate the actual packet choice tree from its fixed-width native
arithmetic. The expansion is exponential in the number of real row
factors, not in the current leaf's total edge count or source exponent
word's *value*. No supplied arithmetic oracle is involved in this fee. -/
namespace J6R48Leaf
open A1R11 A1R12 J6R18ChildWrite J6R19Retained J6R21Ancestor

def packetStraightFee (a e ell p i w b r c m : ℕ) (hp : 0<p) : ℕ :=
  let W := uvWidth e ell p
  rowWriteCap a e ell p i w b c m r hp+
    m*((2*b+4*w+8)+(b+w)+4)+W+
    W+m*(sourcePowerFee a e ell p w c hp+mulCap e ell p+2)+mulCap e ell p+12

def packetBranchFee (e ell p m r b w : ℕ) (hp : 0<p) : ℕ :=
  leafFee e ell p m r b w+uvWidth e ell p+(m+1)*choiceFee e ell p b hp

theorem packet_fee_one_dfs_exponent (a e ell p i w b r c m : ℕ) (hp : 0<p) :
    packetFee a e ell p i w b r c m hp≤packetStraightFee a e ell p i w b r c m hp+
      (m+2)^r*packetBranchFee e ell p m r b w hp := by
  have h := treeFee_pow (uvWidth e ell p) (m+1) (leafFee e ell p m r b w)
    (choiceFee e ell p b hp) r
  rw [show m+1+1=m+2 by omega] at h
  unfold packetFee packetStraightFee packetBranchFee
  dsimp only
  omega

theorem invoke_fee_one_dfs_exponent (a e ell p q i w b dep n r c m : ℕ) (hp : 0<p) :
    invokeFee a e ell p q i w b dep n r c m hp≤
      traceRouteFee a dep n r c+packetStraightFee a e ell p i w b r c m hp+
      boxFee e ell p q+4+(m+2)^r*packetBranchFee e ell p m r b w hp := by
  have h := packet_fee_one_dfs_exponent a e ell p i w b r c m hp
  unfold invokeFee
  omega

theorem packet_fee_given_packet_rows
    (a e ell p i w b r c m R B : ℕ) (hp : 0<p) (rows : r≤R) (choices : m≤B) :
    packetFee a e ell p i w b r c m hp≤packetStraightFee a e ell p i w b r c m hp+
      (B+2)^R*packetBranchFee e ell p m r b w hp := by
  apply (packet_fee_one_dfs_exponent a e ell p i w b r c m hp).trans
  have h : (m+2)^r≤(B+2)^R :=
    (Nat.pow_le_pow_left (Nat.add_le_add_right choices _) _).trans
      (Nat.pow_le_pow_right (by positivity) rows)
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

#print axioms packet_fee_one_dfs_exponent
#print axioms invoke_fee_one_dfs_exponent
#print axioms packet_fee_given_packet_rows
end J6R48Leaf
