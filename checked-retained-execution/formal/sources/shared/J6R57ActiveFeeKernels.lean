import J6R57ActiveFeeArithmetic
import J6R22ActiveGrid
import J6R22ActiveInterpolate
import J6R22ActiveQuotient
import J6R48BitCostKernels

/-! A polynomial in real word dimensions (not the size of a typed
mode catalogue) for all jet interpolation/normalization primitives
used in the fixed active charge. -/
namespace J6R57ActiveFee
open A1R10 A1R11 A1R12 J6R22Active J6R48BitCost J6R19Retained
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 12000000
set_option maxRecDepth 3000
set_option Elab.async false

structure BitCaps (e ell p K : ℕ) : Prop where
  degree : e ≤ K
  vLength : ell ≤ K
  precision : p ≤ K

def uvPx (K : ℕ) := 5*(K+1)^3
def addPx (K : ℕ) := 428*(K+1)^5
def mulPx (K : ℕ) := 3432*(K+1)^6
def subPx (K : ℕ) := 2*addPx K
def oddPx (K : ℕ) :=
  subPx K+(uvPx K+K*(mulPx K+addPx K+uvPx K+4))+uvPx K+4
def gatePx (K : ℕ) := addPx K+subPx K+mulPx K
def tapePx (K : ℕ) := K*(uvPx K+1)+2
def jetMulPx (K : ℕ) :=
  (K+1)*(K+K+1)*(4*(gatePx K+4*(uvPx K+1)))+(6*K+2)*(uvPx K+1)
def jetAddPx (K : ℕ) := K*(gatePx K+4*(uvPx K+1))
def jetSubPx (K : ℕ) := K*(2*gatePx K+4*(uvPx K+1))+uvPx K
def inversePx (K : ℕ) :=
  uvPx K+K*(4*uvPx K+3*(mulPx K+2)+4)+
  3*uvPx K+2*(mulPx K+2)+oddPx K+6
def slopePx (K : ℕ) :=
  2*uvPx K+oddPx K+mulPx K+4*(K+K+2)+
  (19*K+14+14*(K+2)^2)+8*(K+3)^2+8
def normalPartPx (K : ℕ) :=
  slopePx K+jetMulPx K+jetAddPx K+
  (tapePx K+K*(jetMulPx K+tapePx K+2))+3*tapePx K+6
def normalizerPx (K : ℕ) :=
  K*normalPartPx K+tapePx K+K*(jetMulPx K+2)+K*(8*(K+3)^2+4)+6
def factorPx (K : ℕ) :=
  2*uvPx K+subPx K+2+inversePx K+jetSubPx K+jetMulPx K+3*tapePx K+4
def interpolationPx (K : ℕ) :=
  K*((tapePx K+K*(factorPx K+jetMulPx K+2)+4*(K+1)^2+6)+
    jetMulPx K+tapePx K+4+(jetAddPx K+2))+tapePx K+4*(K+1)^2+4
def quotientPx (K : ℕ) :=
  jetSubPx K+(tapePx K+K*(jetMulPx K+jetAddPx K+3*K*(uvPx K+1)+4))+
    jetMulPx K+3*K*(uvPx K+1)+4

variable {e ell p K : ℕ} (h : BitCaps e ell p K) (hp : 0<p)

include h in
theorem uv_word_cap : uvWidth e ell p ≤ uvPx K :=
  uvWidth_physical_poly h.degree h.vLength h.precision

include h in
theorem addition_cap : addCap e ell p hp ≤ addPx K :=
  addCap_physical_poly hp h.degree h.vLength h.precision

include h in
theorem multiplication_cap : mulCap e ell p ≤ mulPx K :=
  mulCap_physical_poly h.degree h.vLength h.precision

include h in
theorem subtraction_cap : subCap e ell p hp ≤ subPx K := by
  refine (show subCap e ell p hp ≤ 2*addCap e ell p hp from ?_).trans
    (Nat.mul_le_mul_left _ (addition_cap h hp))
  unfold subCap addCap
  calc
    _ ≤ ell*(2*(uBudgetGates e p hp+4*(e*p+1))) :=
      Nat.mul_le_mul_left ell (by omega)
    _=_ := by ring

include h in
theorem odd_arithmetic_cap : oddCap e ell p hp ≤ oddPx K := by
  have a := addition_cap h hp
  have m := multiplication_cap h
  have u := uv_word_cap h
  have s := subtraction_cap h hp
  have hh := h.precision
  unfold oddCap correctionCap oddPx
  gcongr

include h in
theorem jet_gate_cap : jetGateFee e ell p hp ≤ gatePx K := by
  have a := addition_cap h hp
  have m := multiplication_cap h
  have s := subtraction_cap h hp
  unfold jetGateFee gatePx
  gcongr

include h in
theorem jet_tape_cap {k : ℕ} (hk : k ≤ K) : tapeFee e ell p k ≤ tapePx K := by
  have u := uv_word_cap h
  unfold tapeFee tapePx jetEntryWidth
  gcongr

include h in
theorem jet_multiply_cap {k : ℕ} (hk : k ≤ K) : jetMulFee e ell p k hp ≤ jetMulPx K := by
  have u := uv_word_cap h
  have g := jet_gate_cap h hp
  unfold jetMulFee jetMulPx jetEntryWidth
  gcongr

include h in
theorem jet_addition_cap {k : ℕ} (hk : k ≤ K) : jetAddFee e ell p k hp ≤ jetAddPx K := by
  have u := uv_word_cap h
  have g := jet_gate_cap h hp
  unfold jetAddFee jetAddPx jetEntryWidth
  gcongr

include h in
theorem jet_subtraction_cap {k : ℕ} (hk : k ≤ K) : jetSubFee e ell p k hp ≤ jetSubPx K := by
  have u := uv_word_cap h
  have g := jet_gate_cap h hp
  unfold jetSubFee jetSubPx jetEntryWidth
  gcongr

include h in
theorem inverse_arithmetic_cap : inverseFee e ell p hp ≤ inversePx K := by
  have u := uv_word_cap h
  have m := multiplication_cap h
  have o := odd_arithmetic_cap h hp
  have b : e-1 ≤ K := (Nat.sub_le _ _).trans h.degree
  unfold inverseFee inversePx seedStride
  gcongr

include h in
theorem slope_arithmetic_cap {a : ℕ} (ha : a ≤ K) : slopeFee e ell p a hp ≤ slopePx K := by
  have u := uv_word_cap h
  have o := odd_arithmetic_cap h hp
  have m := multiplication_cap h
  have pp := h.precision
  unfold slopeFee slopePx dyadicCap
  have eq : K+1+1=K+2 := by omega
  rw [←eq]
  gcongr

include h in
theorem normal_part_cap {a k n : ℕ} (ha : a ≤ K) (hk : k ≤ K) (hn : n ≤ K) :
    normalFactorFee e ell p a k n hp ≤ normalPartPx K := by
  have s := slope_arithmetic_cap h hp ha
  have m := jet_multiply_cap h hp hk
  have t := jet_tape_cap h hk
  have add := jet_addition_cap h hp hk
  unfold normalFactorFee normalPartPx powerTapeFee
  gcongr

private theorem sum_of_units {A : Type*} (xs : List A) (f : A→ℕ) (K0 : ℕ)
    (cap : ∀ x∈xs,f x ≤ K0) : (xs.map f).sum ≤ xs.length*K0 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simpa only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul,Nat.add_comm] using
      Nat.add_le_add (cap x List.mem_cons_self) (ih (fun x hx=>cap x (List.mem_cons_of_mem _ hx)))

include h in
theorem normalizer_arithmetic_cap {a k : ℕ} (ha : a ≤ K) (hk : k ≤ K) (xs : List (ℤ×ℕ))
    (lengthFits : xs.length ≤ K) (powers : ∀ q∈xs,q.2 ≤ K) :
    normalizerFee e ell p a k hp xs ≤ normalizerPx K := by
  have s := (sum_of_units xs (fun q=>normalFactorFee e ell p a k q.2 hp) (normalPartPx K)
    (fun q hq=>normal_part_cap h hp ha hk (powers q hq))).trans
      (Nat.mul_le_mul_right _ lengthFits)
  have t := jet_tape_cap h hk
  have m := jet_multiply_cap h hp hk
  unfold normalizerFee normalizerPx
  gcongr

include h in
theorem interpolation_arithmetic_cap {k n : ℕ} (hk : k ≤ K) (hn : n ≤ K) :
    interpExtra e ell p k n hp ≤ interpolationPx K := by
  have u := uv_word_cap h
  have s := subtraction_cap h hp
  have i := inverse_arithmetic_cap h hp
  have m := jet_multiply_cap h hp hk
  have a := jet_addition_cap h hp hk
  have ss := jet_subtraction_cap h hp hk
  have t := jet_tape_cap h hk
  have b : n-1 ≤ K := (Nat.sub_le _ _).trans hn
  unfold interpExtra interpolationPx basisExtra factorExtra factorPx
  gcongr

include h in
theorem quotient_arithmetic_cap {k : ℕ} (hk : k ≤ K) :
    quotientFee e ell p k hp ≤ quotientPx K := by
  have u := uv_word_cap h
  have m := jet_multiply_cap h hp hk
  have a := jet_addition_cap h hp hk
  have s := jet_subtraction_cap h hp hk
  have t := jet_tape_cap h hk
  unfold quotientFee quotientPx jetGeomFee jetGeomStride
  change _+((tapeFee e ell p k)+_)+_+_+_ ≤ _
  unfold jetEntryWidth
  gcongr

#print axioms odd_arithmetic_cap
#print axioms inverse_arithmetic_cap
#print axioms normalizer_arithmetic_cap
#print axioms interpolation_arithmetic_cap
#print axioms quotient_arithmetic_cap
end J6R57ActiveFee
