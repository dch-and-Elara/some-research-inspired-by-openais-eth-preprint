import J6R58LeafScaleArithmetic
import J6R57LeafCapStored

/-! Convert the actual assignment-loop cap to the printed leaf-cutoff
factor. Address bills and the measured provider are deliberately not
hidden inside the ring-arithmetic envelope. -/
namespace J6R65LeafRate
open scoped Polynomial
open AOracleMachineTime A1R11 A1R12 J6R21Leaf J6R48Leaf
open J6R57LeafCap J6R58LeafScale

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 16000000

theorem raw_leaf_fee_from_dimensions
    {e ell p n v E L P H V bill : ℕ} (hp : 0<p)
    (field : e≤E) (truncation : ell≤L) (precision : p≤P) (stopped : n≤H) (vertices : v≤V) :
    rawLeafCap e ell p n v bill hp≤
      2^H*(bill+leafArithmeticScale E L P H V 0) :=
  (raw_leaf_cap_has_printed_factor e ell p n v bill H hp stopped).trans
    (Nat.mul_le_mul_left _ (actual_raw_leaf_scale_arithmetic_separate
      hp field truncation precision stopped vertices))

theorem zero_edges_have_one_assignment_fee (e ell p v bill : ℕ) (hp : 0<p) :
    rawLeafCap e ell p 0 v bill hp=bill+uvWidth e ell p+v*(mulCap e ell p+2)+reverseFee 0 := by
  simp [rawLeafCap]

theorem zero_edge_fee_from_dimensions
    {e ell p v E L P H V bill : ℕ} (hp : 0<p)
    (field : e≤E) (truncation : ell≤L) (precision : p≤P) (vertices : v≤V) :
    rawLeafCap e ell p 0 v bill hp≤bill+leafArithmeticScale E L P H V 0 := by
  have h : rawLeafCap e ell p 0 v bill hp≤rawLeafScale e ell p 0 v bill hp := by
    simpa only [pow_zero,one_mul] using raw_leaf_cap_has_printed_factor e ell p 0 v bill 0 hp le_rfl
  exact h.trans (actual_raw_leaf_scale_arithmetic_separate hp field truncation precision
    (Nat.zero_le H) vertices)

def finiteStopFee (provider setup bill arithmetic H : ℕ) : ℕ :=
  provider+setup+2^H*(bill+arithmetic)

theorem structural_leaf_fee_into_printed_rate
    {provider setup bill arithmetic H Bprep Bread K : ℕ}
    (s : setup≤Bprep) (b : bill≤Bread*2^(K*H)) :
    finiteStopFee provider setup bill arithmetic H≤
      provider+(Bprep+Bread+arithmetic)*2^((K+1)*H) := by
  let R := (2:ℕ)^(K*H)
  let N := (2:ℕ)^H
  have hR : 0<R := by positivity
  have hN : 0<N := by positivity
  have bn : Bprep≤Bprep*(R*N) := Nat.le_mul_of_pos_right _ (Nat.mul_pos hR hN)
  have ha : arithmetic≤arithmetic*R := Nat.le_mul_of_pos_right _ hR
  change provider+setup+N*(bill+arithmetic)≤_
  calc
    _≤provider+Bprep*(R*N)+N*(Bread*R+arithmetic*R) :=
      Nat.add_le_add (Nat.add_le_add_left (s.trans bn) _) (Nat.mul_le_mul_left _ (Nat.add_le_add b ha))
    _=provider+(Bprep+Bread+arithmetic)*(R*N) := by ring
    _=_ := by simp only [R,N,Nat.add_mul K 1 H,one_mul,pow_add]

theorem provider_budget_can_be_added_once
    {provider base bound K H : ℕ} (h : provider≤bound*2^(K*H)) :
    provider+base*2^((K+1)*H)≤(bound+base)*2^((K+1)*H) := by
  rw [Nat.add_mul bound base]
  apply Nat.add_le_add_right
  exact h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide)
    (Nat.mul_le_mul_right _ (Nat.le_succ _))))

#print axioms raw_leaf_fee_from_dimensions
#print axioms zero_edges_have_one_assignment_fee
#print axioms zero_edge_fee_from_dimensions
#print axioms structural_leaf_fee_into_printed_rate
#print axioms provider_budget_can_be_added_once
end J6R65LeafRate
