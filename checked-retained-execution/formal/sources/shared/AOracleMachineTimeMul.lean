import AOracleMachineTime

/-!
# Bit-serial multiplication of finite residue words

Shift and conditional ripple addition run on literal bit lists.
Their result in Z/(2^p) is the arithmetic product. This bit primitive
can replace the word-cost hypothesis in a dense coefficient schedule.
-/

namespace AOracleMachineTimeMul
open AOracleMachineTime

theorem value_split (a : List Bool) (k : ℕ) (hk : k≤a.length) :
    bitsValue a = bitsValue (a.take k)+2^k*bitsValue (a.drop k) := by
  induction k generalizing a with
  | zero => simp [bitsValue]
  | succ k ih =>
    cases a with
    | nil => simp at hk
    | cons b a =>
      have he := ih a (by simpa using hk)
      simp only [List.take_succ_cons, List.drop_succ_cons, bitsValue, pow_succ]
      nlinarith

theorem value_zero (p : ℕ) : bitsValue (List.replicate p false)=0 := by
  induction p with
  | zero => rfl
  | succ p ih => simp [List.replicate_succ, bitsValue, ih]

def shift (a : List Bool) : List Bool := (false::a).take a.length

theorem shift_length (a : List Bool) : (shift a).length=a.length := by
  simp [shift]

/-- The reduction of a binary list in the actual residue ring. -/
def asResidue (p : ℕ) (a : List Bool) : ZMod (2^p) := bitsValue a

theorem ring_nilpotent (p : ℕ) : (2:ZMod (2^p))^p=0 := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using ZMod.natCast_self (2^p)

theorem shift_residue (p : ℕ) (a : List Bool) (ha : a.length=p) :
    asResidue p (shift a)=2*asResidue p a := by
  have h : a.length ≤ (false::a).length := by simp
  have hc := congrArg (fun n : ℕ => (n:ZMod (2^p))) (value_split (false::a) a.length h)
  simpa [shift, asResidue, bitsValue, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, ha, ring_nilpotent] using hc.symm

theorem add_residue (p : ℕ) (a b : List Bool) (ha : a.length=p) (hb : b.length=p) :
    asResidue p (addBits a b).result=asResidue p a+asResidue p b := by
  have vv := (addBits_exact a b (ha.trans hb.symm)).2.1
  unfold asResidue
  rw [vv, ha, ZMod.natCast_mod, Nat.cast_add]

/-- Horner's bit loop (higher suffix first). One shift per multiplier
bit and at most one full-width addition; no Nat multiplication is
performed in the loop. -/
def multiply (a : List Bool) : List Bool → Meter (List Bool)
  | [] => ⟨List.replicate a.length false,a.length⟩
  | b::bs =>
    let hi := multiply a bs
    let shifted := shift hi.result
    let lo := if b then addBits shifted a else Meter.pure shifted
    ⟨lo.result,hi.steps+lo.steps+4*a.length+8⟩

theorem multiply_result (p : ℕ) (a b : List Bool) (ha : a.length=p) :
    (multiply a b).result.length=p ∧
      asResidue p (multiply a b).result=asResidue p a*asResidue p b ∧
      (multiply a b).steps≤p+(16*p+8)*b.length := by
  induction b with
  | nil => simp [multiply, ha, asResidue, value_zero, bitsValue]
  | cons b bs ih =>
    obtain ⟨hl,hv,hc⟩ := ih
    have hshift : (shift (multiply a bs).result).length=p := by rw [shift_length,hl]
    have hvs := shift_residue p (multiply a bs).result hl
    cases b
    · change (shift (multiply a bs).result).length=p ∧
          asResidue p (shift (multiply a bs).result) = asResidue p a*asResidue p (false::bs) ∧
          (multiply a bs).steps+0+4*a.length+8 ≤ p+(16*p+8)*(bs.length+1)
      refine ⟨hshift,?_,?_⟩
      · rw [hvs, hv]
        simp [asResidue, bitsValue, mul_left_comm]
      · rw [ha, Nat.mul_succ]
        omega
    · have hadd := addBits_exact (shift (multiply a bs).result) a (hshift.trans ha.symm)
      change (addBits (shift (multiply a bs).result) a).result.length=p ∧
        asResidue p (addBits (shift (multiply a bs).result) a).result =
          asResidue p a*asResidue p (true::bs) ∧
        (multiply a bs).steps+(addBits (shift (multiply a bs).result) a).steps+4*a.length+8
          ≤ p+(16*p+8)*(bs.length+1)
      refine ⟨hadd.1.trans hshift, ?_, ?_⟩
      · rw [add_residue p _ _ hshift ha, hvs, hv]
        simp only [asResidue, bitsValue, Bool.toNat_true, Nat.cast_add, Nat.cast_one,
          Nat.cast_mul, Nat.cast_ofNat]
        ring
      · rw [hadd.2.2, hshift,ha,Nat.mul_succ]
        omega

/-- The actual truncating schoolbook primitive consumes at most a
quadratic number of counted Boolean/tape operations. -/
theorem square_word_cost (p : ℕ) (a b : List Bool) (ha : a.length=p) (hb : b.length=p) :
    (multiply a b).steps≤16*(p+1)^2 := by
  have h := (multiply_result p a b ha).2.2
  rw [hb] at h
  nlinarith

#print axioms value_split
#print axioms shift_residue
#print axioms add_residue
#print axioms multiply_result
#print axioms square_word_cost

end AOracleMachineTimeMul

