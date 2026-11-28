import J4R43LiteralOutsideUnitWord

/-! Read the true common trailing-even factors and drop the same
binary positions from both magnitudes, without a valuation oracle
or arbitrary integer division. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators
open A1R10 A1R12 AOracleMachineTime AOracleMachineTimeTape AOracleCoordinates
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5700000

structure BitStripRun where
  numerator : List Bool
  denominator : List Bool
  steps : ℕ

def stripMagnitudeBits (a b : List Bool) : ℕ→BitStripRun
  | 0 => ⟨a,b,1⟩
  | n+1 =>
    match b with
    | false::t =>
      let r := stripMagnitudeBits a.tail t n
      ⟨r.numerator,r.denominator,r.steps+4⟩
    | _ => ⟨a,b,2⟩

theorem strip_bits_fee (a b : List Bool) (n : ℕ) :
    (stripMagnitudeBits a b n).steps≤4*n+2 := by
  induction n generalizing a b with
  | zero => simp [stripMagnitudeBits]
  | succ n ih =>
    cases b with
    | nil => simp [stripMagnitudeBits]
    | cons x b =>
      cases x
      · have h := ih a.tail b
        simp only [stripMagnitudeBits]
        omega
      · simp [stripMagnitudeBits]

@[simp] theorem false_low_value (bs : List Bool) :
    bitsValue (false::bs)=2*bitsValue bs := by
  change 0+2*bitsValue bs=2*bitsValue bs
  omega

@[simp] theorem true_low_value (bs : List Bool) :
    bitsValue (true::bs)=1+2*bitsValue bs := rfl

theorem tail_halves_abs_word (a : List Bool) : bitsValue a.tail=bitsValue a/2 := by
  cases a with
  | nil => simp [bitsValue]
  | cons b bs =>
    cases b <;> simp only [List.tail_cons,false_low_value,true_low_value] <;> omega

theorem common_binary_stripping_exact (a b : List Bool) (n d : ℕ)
    (odd : d%2=1) (k fuel : ℕ) (en : bitsValue a=2^k*n)
    (ed : bitsValue b=2^k*d) (h : k≤fuel) :
    let out := stripMagnitudeBits a b fuel
    bitsValue out.numerator=n ∧ bitsValue out.denominator=d := by
  induction fuel generalizing k a b with
  | zero =>
    have z : k=0 := by omega
    subst k
    simpa [stripMagnitudeBits] using And.intro en ed
  | succ fuel ih =>
    cases k with
    | zero =>
      cases b with
      | nil => simp [bitsValue] at ed; omega
      | cons B b =>
        cases B with
        | false =>
          simp only [false_low_value,pow_zero,one_mul] at ed
          omega
        | true =>
          simpa [stripMagnitudeBits] using And.intro en ed
    | succ k =>
      have pr : 2^(k+1)*n=2*(2^k*n) := by rw [pow_succ]; ring
      have dr : 2^(k+1)*d=2*(2^k*d) := by rw [pow_succ]; ring
      cases b with
      | nil =>
        simp only [bitsValue] at ed
        have pos : 0<d := by omega
        have R : 0<(2:ℕ)^(k+1)*d := by positivity
        omega
      | cons B b =>
        cases B with
        | true =>
          rw [dr] at ed
          simp only [true_low_value] at ed
          omega
        | false =>
          have zz : bitsValue a.tail=2^k*n := by
            rw [tail_halves_abs_word,en,pr]
            omega
          have bb : bitsValue b=2^k*d := by
            rw [dr] at ed
            simp only [false_low_value] at ed
            omega
          exact ih a.tail b k zz bb (by omega)

#print axioms strip_bits_fee
#print axioms tail_halves_abs_word
#print axioms common_binary_stripping_exact
end
end J4R43LiteralOutside

