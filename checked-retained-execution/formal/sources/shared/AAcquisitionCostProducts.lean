import AAcquisitionCostNormalizer

/-! Exact accumulation of A4's 2/3/5 factors by a little-endian
bit stream. The local multiplier/carry is bounded by 5, so each
transition is a fixed-size Boolean table, not arbitrary-precision
multiplication. The final exact integer division is not charged here. -/

namespace AAcquisitionCost

def bitNat (b : Bool) : ℕ := if b then 1 else 0

def wordNat : List Bool → ℕ
  | [] => 0
  | b::bs => bitNat b+2*wordNat bs

theorem wordNat_append (xs ys : List Bool) :
    wordNat (xs++ys) = wordNat xs+2^xs.length*wordNat ys := by
  induction xs with
  | nil => simp [wordNat]
  | cons x xs ih =>
    simp only [List.cons_append,wordNat,List.length_cons,ih,pow_succ]
    ring

def oddBit (n : ℕ) : Bool := decide (n%2=1)

theorem bitNat_low (n : ℕ) : bitNat (oddBit n) = n%2 := by
  have hr := Nat.mod_lt n (by decide : 0 < 2)
  have hc : n%2 = 0 ∨ n%2 = 1 := by omega
  rcases hc with h | h <;> simp [oddBit,bitNat,h]

def multiplySmall (factor : ℕ) (carry : ℕ) : List Bool → List Bool × ℕ
  | [] => ([],carry)
  | x::xs =>
    let term := bitNat x*factor+carry
    let r := multiplySmall factor (term/2) xs
    (oddBit term :: r.1,r.2)

theorem multiplySmall_length (factor carry : ℕ) (w : List Bool) :
    (multiplySmall factor carry w).1.length = w.length := by
  induction w generalizing carry with
  | nil => rfl
  | cons b bs ih => simp [multiplySmall,ih]

theorem multiplySmall_carry (factor carry : ℕ) (w : List Bool)
    (hf : factor ≤ 5) (hc : carry ≤ 5) : (multiplySmall factor carry w).2 ≤ 5 := by
  induction w generalizing carry with
  | nil => exact hc
  | cons b bs ih =>
    let term := bitNat b*factor+carry
    have hterm : term ≤ 10 := by cases b <;> simp [term,bitNat] <;> omega
    exact ih (term/2) (by omega)

theorem multiplySmall_value (factor carry : ℕ) (w : List Bool) :
    let r := multiplySmall factor carry w
    wordNat r.1 + 2^w.length*r.2 = factor*wordNat w+carry := by
  induction w generalizing carry with
  | nil => simp [wordNat,multiplySmall]
  | cons b bs ih =>
    let term := bitNat b*factor+carry
    let r := multiplySmall factor (term/2) bs
    change bitNat (oddBit term) + 2*wordNat r.1 + 2^(bs.length+1)*r.2 =
      factor*(bitNat b+2*wordNat bs)+carry
    calc
      _ = bitNat (oddBit term) + 2*(wordNat r.1 + 2^bs.length*r.2) := by rw [pow_succ]; ring
      _ = bitNat (oddBit term) + 2*(factor*wordNat bs+term/2) := by rw [ih (term/2)]
      _ = (term%2+2*(term/2)) + 2*(factor*wordNat bs) := by rw [bitNat_low]; ring
      _ = _ := by rw [Nat.mod_add_div]; dsimp [term]; ring

def threeBits (x : ℕ) : List Bool := [oddBit x,oddBit (x/2),oddBit (x/4)]

theorem threeBits_value (x : ℕ) (hx : x ≤ 5) : wordNat (threeBits x) = x := by
  interval_cases x <;> decide

def extendMul (factor : ℕ) (w : List Bool) : List Bool :=
  let r := multiplySmall factor 0 w
  r.1 ++ threeBits r.2

theorem extendMul_length (factor : ℕ) (w : List Bool) :
    (extendMul factor w).length = w.length+3 := by
  simp [extendMul,threeBits,multiplySmall_length]

theorem extendMul_value (factor : ℕ) (w : List Bool) (hf : factor ≤ 5) :
    wordNat (extendMul factor w) = factor*wordNat w := by
  rw [extendMul,wordNat_append,threeBits_value _ (multiplySmall_carry _ _ _ hf (by decide)),
    multiplySmall_length]
  simpa using multiplySmall_value factor 0 w

def multiplyFactors : List ℕ → List Bool → List Bool
  | [], w => w
  | f::fs, w => multiplyFactors fs (extendMul f w)

theorem multiplyFactors_length (factors : List ℕ) (w : List Bool) :
    (multiplyFactors factors w).length = w.length+3*factors.length := by
  induction factors generalizing w with
  | nil => simp [multiplyFactors]
  | cons f fs ih =>
    simp only [multiplyFactors,ih,extendMul_length,List.length_cons]
    omega

theorem multiplyFactors_value (factors : List ℕ) (w : List Bool)
    (valid : ∀ f ∈ factors, f ≤ 5) :
    wordNat (multiplyFactors factors w) = factors.prod*wordNat w := by
  induction factors generalizing w with
  | nil => simp [multiplyFactors]
  | cons f fs ih =>
    rw [multiplyFactors,ih (extendMul f w) (fun g hg => valid g (List.mem_cons_of_mem _ hg)),
      extendMul_value _ _ (valid f (by simp)),List.prod_cons]
    ring

/-- Number of finite-state digit steps and carry-output writes.
Each digit step reads/writes the digit and uses the (fixed-width)
factor and carry registers; their full-range sizes never depend on input. -/
def productSchedule : List ℕ → ℕ → ℕ
  | [], _ => 0
  | _::fs, w => w+3+productSchedule fs (w+3)

theorem productSchedule_budget (factors : List ℕ) (width : ℕ) :
    productSchedule factors width ≤ factors.length*(width+3*factors.length) := by
  induction factors generalizing width with
  | nil => simp [productSchedule]
  | cons f fs ih =>
    have h := ih (width+3)
    simp only [productSchedule,List.length_cons,Nat.succ_mul]
    nlinarith

def binaryNormalizer {u c : ℕ} (tap : Fin u → Option (Fin c)) : List Bool :=
  multiplyFactors (factorTape tap) [true]

theorem binaryNormalizer_exact {u c : ℕ} (tap : Fin u → Option (Fin c))
    (cap : ∀ a, Acquisition.unaryLoad tap a ≤ 2) :
    wordNat (binaryNormalizer tap) = Acquisition.publicFactor tap := by
  have valid : ∀ f ∈ factorTape tap, f ≤ 5 := by
    intro f hf
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hf
    rw [tapTape_hits,min_eq_right (cap a)]
    exact Nat.add_le_add_left (Nat.pow_le_pow_right (by decide) (cap a)) 1
  rw [binaryNormalizer,multiplyFactors_value _ _ valid,factorTape_exact tap cap]
  simp [wordNat,bitNat]

def explicitNormalizerSize (u c p : ℕ) : ℕ := u+c+p+1

theorem normalizer_schedule_poly {u c : ℕ} (tap : Fin u → Option (Fin c)) (p : ℕ) :
    factorScanCost tap + productSchedule (factorTape tap) 1 ≤ 18*(explicitNormalizerSize u c p)^3 := by
  let S := explicitNormalizerSize u c p
  have hc : c ≤ S := by dsimp [S,explicitNormalizerSize]; omega
  have hu : u ≤ S := by dsimp [S,explicitNormalizerSize]; omega
  have hs : 1 ≤ S := by dsimp [S,explicitNormalizerSize]; omega
  have hscan := factorScanCost_budget tap
  have hprod := productSchedule_budget (factorTape tap) 1
  have hlen : (factorTape tap).length = c := by simp [factorTape]
  rw [hlen] at hprod
  have hsc : c*((4*c+9)*u) ≤ S*((13*S)*S) :=
    Nat.mul_le_mul hc (Nat.mul_le_mul (by omega) hu)
  have hpr : c*(1+3*c) ≤ S*(4*S) :=
    Nat.mul_le_mul hc (by omega)
  have hpow : S^2 ≤ S^3 := Nat.pow_le_pow_right hs (by decide)
  change _ ≤ 18*S^3
  nlinarith

#print axioms multiplySmall_carry
#print axioms multiplySmall_value
#print axioms multiplyFactors_value
#print axioms productSchedule_budget
#print axioms binaryNormalizer_exact
#print axioms normalizer_schedule_poly

end AAcquisitionCost
