import A1R12UV

/-! Fixed-width truncating encoders for signed dyadic parts. A raw
magnitude enters in little-endian bits; its sign is implemented by
metered two's complement, never by a ring oracle. -/

namespace A1R12
open A1R10 A1R11 AOracleMachineTime AOracleMachineTimeTape AOracleMachineTimeMul

def lowBits : ℕ → List Bool → List Bool
  | 0,_ => []
  | p+1,[] => false::lowBits p []
  | p+1,b::bs => b::lowBits p bs

theorem lowBits_len (p : ℕ) (l : List Bool) : (lowBits p l).length=p := by
  induction p generalizing l with
  | zero => rfl
  | succ p ih => cases l <;> simp [lowBits,ih]

theorem lowBits_value (p : ℕ) (l : List Bool) : bitsValue (lowBits p l)=bitsValue l%2^p := by
  induction p generalizing l with
  | zero => simp [lowBits,bitsValue,Nat.mod_one]
  | succ p ih =>
    cases l with
    | nil => simp [lowBits,bitsValue,ih]
    | cons b bs =>
      rw [pow_succ, Nat.mul_comm _ 2,Nat.mod_mul]
      simp only [lowBits,bitsValue,ih]
      have hb : b.toNat≤1 := by cases b <;> decide
      rw [show (b.toNat+2*bitsValue bs)%2=b.toNat by omega,
        show (b.toNat+2*bitsValue bs)/2=bitsValue bs by omega]

def asLowWord (p : ℕ) (l : List Bool) : A1R10.Word p :=
  ⟨lowBits p l,lowBits_len p l⟩

theorem asLowWord_read (p : ℕ) (l : List Bool) :
    wordRead (asLowWord p l)=(bitsValue l:ZMod (2^p)) := by
  change (bitsValue (lowBits p l):ZMod (2^p))=_
  rw [lowBits_value,ZMod.natCast_mod]

theorem encodeBits_mod (p n : ℕ) : bitsValue (encodeBits p n)=n%2^p := by
  induction p generalizing n with
  | zero => simp [encodeBits,bitsValue,Nat.mod_one]
  | succ p ih =>
    rw [pow_succ,Nat.mul_comm _ 2,Nat.mod_mul]
    simp only [encodeBits,bitsValue,ih]
    by_cases h : n%2=1
    · simp [h]
    · have h0 : n%2=0 := by omega
      simp [h0]

def natWord (p n : ℕ) : A1R10.Word p := ⟨encodeBits p n,encodeBits_length _ _⟩

theorem natWord_read (p n : ℕ) : wordRead (natWord p n)=(n:ZMod (2^p)) := by
  change (bitsValue (encodeBits p n):ZMod (2^p))=_
  rw [encodeBits_mod,ZMod.natCast_mod]

def signedDenote (neg : Bool) (l : List Bool) : ℤ :=
  if neg then -(bitsValue l:ℤ) else bitsValue l

def wordSign {p : ℕ} (hp : 0<p) (neg : Bool) (u : A1R10.Word p) : Meter (A1R10.Word p) :=
  if neg then
    let r := A1R9.negWord p u.val
    ⟨⟨r.result,(A1R9.negWord_exact p hp u.val u.property).1⟩,r.steps+2⟩
  else ⟨u,2⟩

theorem wordSign_exact {p : ℕ} (hp : 0<p) (neg : Bool) (u : A1R10.Word p) :
    wordRead (wordSign hp neg u).result=(if neg then -wordRead u else wordRead u) ∧
      (wordSign hp neg u).steps≤15*p+2 := by
  cases neg
  · simp [wordSign]
  · obtain ⟨_,h,mc⟩ := A1R9.negWord_exact p hp u.val u.property
    refine ⟨h,?_⟩
    change (A1R9.negWord p u.val).steps+2≤_
    rw [mc]

def signedWord {p : ℕ} (hp : 0<p) (neg : Bool) (l : List Bool) : Meter (A1R10.Word p) :=
  let r := wordSign hp neg (asLowWord p l)
  ⟨r.result,r.steps+4*p+4⟩

theorem signedWord_exact {p : ℕ} (hp : 0<p) (neg : Bool) (l : List Bool) :
    wordRead (signedWord hp neg l).result=(signedDenote neg l:ZMod (2^p)) ∧
      (signedWord hp neg l).steps≤19*p+6 := by
  obtain ⟨hv,hc⟩ := wordSign_exact hp neg (asLowWord p l)
  refine ⟨?_,?_⟩
  · change wordRead (wordSign hp neg (asLowWord p l)).result=_
    rw [hv,asLowWord_read]
    cases neg <;> simp [signedDenote]
  · change (wordSign hp neg (asLowWord p l)).steps+4*p+4≤_
    omega

/-- One hot bit, clipped at p. No large power of two is constructed. -/
def dyadicBits : ℕ → ℕ → List Bool
  | 0,_ => []
  | p+1,0 => true::List.replicate p false
  | p+1,j+1 => false::dyadicBits p j

theorem dyadicBits_len (p j : ℕ) : (dyadicBits p j).length=p := by
  induction p generalizing j with
  | zero => rfl
  | succ p ih => cases j <;> simp [dyadicBits,ih]

theorem dyadicBits_value (p j : ℕ) :
    bitsValue (dyadicBits p j)=(if j<p then 2^j else 0) := by
  induction p generalizing j with
  | zero => simp [dyadicBits,bitsValue]
  | succ p ih =>
    cases j with
    | zero => simp [dyadicBits,bitsValue,value_zero]
    | succ j => simp [dyadicBits,bitsValue,ih,pow_succ,mul_comm]

def dyadicWord (p j : ℕ) : A1R10.Word p :=
  ⟨dyadicBits p j,dyadicBits_len p j⟩

theorem dyadicWord_read (p j : ℕ) : wordRead (dyadicWord p j)=(2:ZMod (2^p))^j := by
  change (bitsValue (dyadicBits p j):ZMod (2^p))=_
  rw [dyadicBits_value]
  by_cases h : j<p
  · simp [h,Nat.cast_pow]
  · rw [if_neg h,Nat.cast_zero]
    obtain ⟨r,hr⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt h)
    rw [hr,pow_add,ring_nilpotent,zero_mul]

#print axioms lowBits_value
#print axioms natWord_read
#print axioms signedWord_exact
#print axioms dyadicWord_read
end A1R12

