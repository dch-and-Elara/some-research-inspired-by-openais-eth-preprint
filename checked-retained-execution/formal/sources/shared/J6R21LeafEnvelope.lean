
import J6R21LeafPrintedStop

/-! A uniform monotone envelope for leaf arithmetic at possibly
different native precisions. The caller supplies actual maxima for
coefficient-field degree, side degree, precision, and each input read. -/
namespace J6R21Leaf
open A1R10 A1R11 A1R12 AOracleMachineTime
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4500000

def dimEnvelope (e ell p : ℕ) := (ell+1)^2*(e+1)^2*(p+1)^2

def polynomialLeafFee (e ell p m v U : ℕ) : ℕ :=
  let W := dimEnvelope e ell p
  2^m*(v*(U+3432*W+2)+429*W+3*m+12)

theorem call_leaf_fee_polynomial (e ell p m v U : ℕ) (hp : 0<p) :
    callLeafFee e ell p m v U hp ≤ polynomialLeafFee e ell p m v U := by
  let X := (e+1)^2*(p+1)^2
  let W := dimEnvelope e ell p
  have E : e+1≤(e+1)^2 := by nlinarith
  have P : p+1≤(p+1)^2 := by nlinarith
  have L : ell≤(ell+1)^2 := by nlinarith
  have ep : e*p+1≤X := (show e*p+1≤(e+1)*(p+1) by nlinarith).trans (Nat.mul_le_mul E P)
  have scale : (ell+1)^2*X=W := by unfold W X dimEnvelope; ring
  have width : uvWidth e ell p≤W+4 := by
    unfold uvWidth
    exact Nat.add_le_add_right ((Nat.mul_le_mul L ep).trans_eq scale) 4
  have u := uBudgetGates_poly e p hp
  change uBudgetGates e p hp≤424*X at u
  have ah : uBudgetGates e p hp+4*(e*p+1)≤428*X := by omega
  have add : addCap e ell p hp≤428*W := by
    unfold addCap
    calc
      _ ≤(ell+1)^2*(428*X) := Nat.mul_le_mul L ah
      _ =_ := by rw [← scale]; ring
  have mul : mulCap e ell p=3432*W := rfl
  unfold polynomialLeafFee
  change callLeafFee e ell p m v U hp ≤
    2^m*(v*(U+3432*W+2)+429*W+3*m+12)
  unfold callLeafFee reverseFee innerFee
  apply Nat.mul_le_mul_left
  rw [mul]
  omega

theorem polynomial_leaf_fee_mono {e E ell L p P m M v V U Q : ℕ}
    (he : e≤E) (hl : ell≤L) (hp : p≤P) (hm : m≤M) (hv : v≤V) (hU : U≤Q) :
    polynomialLeafFee e ell p m v U≤polynomialLeafFee E L P M V Q := by
  have hh : (2:ℕ)^m≤2^M := Nat.pow_le_pow_right (by decide) hm
  have d : dimEnvelope e ell p≤dimEnvelope E L P := by
    unfold dimEnvelope
    exact Nat.mul_le_mul (Nat.mul_le_mul
      (Nat.pow_le_pow_left (Nat.succ_le_succ hl) 2)
      (Nat.pow_le_pow_left (Nat.succ_le_succ he) 2))
      (Nat.pow_le_pow_left (Nat.succ_le_succ hp) 2)
  unfold polynomialLeafFee
  dsimp only
  exact Nat.mul_le_mul hh
    (Nat.add_le_add_right (Nat.add_le_add
      (Nat.add_le_add (Nat.mul_le_mul hv
        (Nat.add_le_add_right (Nat.add_le_add hU (Nat.mul_le_mul_left 3432 d)) 2))
        (Nat.mul_le_mul_left 429 d)) (Nat.mul_le_mul_left 3 hm)) 12)

theorem call_leaf_fee_uniform_dims {e E ell L p P m M v V U Q : ℕ} (hp0 : 0<p)
    (he : e≤E) (hl : ell≤L) (hp : p≤P) (hm : m≤M) (hv : v≤V) (hU : U≤Q) :
    callLeafFee e ell p m v U hp0≤polynomialLeafFee E L P M V Q :=
  (call_leaf_fee_polynomial e ell p m v U hp0).trans (polynomial_leaf_fee_mono he hl hp hm hv hU)


theorem leaf_compute_arithmetic_only {p ell : ℕ} (hp : 0<p)
    {fw : List (A1R10.Word p)} (he : 0<fw.length) (hℓ : 0<ell)
    (m : ℕ) {D : Type} (nodes : List D)
    (query : D→List Bool→Meter (UVBlock fw ell)) :
    (leafCompute hp he hℓ m nodes query).steps≤
      leafEntryBill m nodes query+callLeafFee fw.length ell p m nodes.length 0 hp := by
  have H := (leafCompute_bills_every_entry hp he hℓ m nodes query).2
  have a := Nat.mul_le_mul_right (innerFee fw.length ell p hp) (Nat.sub_le (2^m) 1)
  unfold callLeafFee
  simp only [zero_add,Nat.mul_add] at H ⊢
  omega

/-- Supply only maxima for physical dimensions, not a hypothetical bound
on any original callback. Its exact cost remains summanded separately. -/
theorem concrete_leaf_arithmetic_envelope {p ell : ℕ} (hp : 0<p)
    {fw : List (A1R10.Word p)} (he : 0<fw.length) (hℓ : 0<ell)
    {m : ℕ} {D : Type} (nodes : List D)
    (query : D→List Bool→Meter (UVBlock fw ell))
    {E L P M V : ℕ}
    (heMax : fw.length≤E) (hellMax : ell≤L) (hpMax : p≤P)
    (hmMax : m≤M) (hvMax : nodes.length≤V) :
    (leafCompute hp he hℓ m nodes query).steps≤
      leafEntryBill m nodes query+polynomialLeafFee E L P M V 0 :=
  (leaf_compute_arithmetic_only hp he hℓ m nodes query).trans
    (Nat.add_le_add_left (call_leaf_fee_uniform_dims hp heMax hellMax hpMax hmMax hvMax (le_refl 0)) _)

#print axioms leaf_compute_arithmetic_only
#print axioms concrete_leaf_arithmetic_envelope
#print axioms call_leaf_fee_polynomial
#print axioms polynomial_leaf_fee_mono
#print axioms call_leaf_fee_uniform_dims
end J6R21Leaf
