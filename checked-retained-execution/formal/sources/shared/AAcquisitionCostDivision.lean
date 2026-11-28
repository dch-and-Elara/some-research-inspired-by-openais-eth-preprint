import AAcquisitionCostProducts

/-! Fixed-width Boolean subtraction and restoring binary division for
the public A4 integer postprocessing. The proof uses division only in
the final specification, not in the executable digit program. -/

namespace AAcquisitionCost

theorem wordNat_lt_width (w : List Bool) : wordNat w < 2^w.length := by
  induction w with
  | nil => decide
  | cons b bs ih =>
    cases b <;> simp only [wordNat,bitNat,Bool.false_eq_true,if_false,if_true,List.length_cons,pow_succ] <;> omega

theorem wordNat_take_width (w : List Bool) (n : ℕ) (h : wordNat w < 2^n) :
    wordNat (w.take n) = wordNat w := by
  by_cases hn : w.length ≤ n
  · simp [List.take_of_length_le hn]
  · have hl : (w.take n).length = n := by simp [Nat.min_eq_left (by omega : n ≤ w.length)]
    have eq : wordNat w = wordNat (w.take n)+2^n*wordNat (w.drop n) := by
      nth_rw 1 [← List.take_append_drop n w]
      rw [wordNat_append,hl]
    have z : wordNat (w.drop n)=0 := by
      by_contra ht
      have hp : 2^n ≤ 2^n * wordNat (w.drop n) := by
        simpa using Nat.mul_le_mul_left (2^n) (show 1 ≤ wordNat (w.drop n) by omega)
      omega
    rw [eq,z,mul_zero,add_zero]

def borrowDigit (a b c : Bool) : Bool × Bool :=
  (xor (xor a b) c, (!a && (b || c)) || (b && c))

theorem borrowDigit_eq (a b c : Bool) :
    bitNat a+2*bitNat (borrowDigit a b c).2 = bitNat b+bitNat c+bitNat (borrowDigit a b c).1 := by
  cases a <;> cases b <;> cases c <;> decide

def rippleBorrow : List Bool → List Bool → Bool → List Bool × Bool
  | a::as,b::bs,c =>
    let s := borrowDigit a b c
    let r := rippleBorrow as bs s.2
    (s.1::r.1,r.2)
  | _,_,c => ([],c)

theorem rippleBorrow_length (a b : List Bool) (c : Bool) (h : a.length=b.length) :
    (rippleBorrow a b c).1.length = a.length := by
  induction a generalizing b c with
  | nil => cases b <;> simp [rippleBorrow]
  | cons x xs ih =>
    cases b with
    | nil => simp at h
    | cons y ys =>
      have h' : xs.length=ys.length := by simpa using h
      simp [rippleBorrow,ih _ _ h']

theorem rippleBorrow_value (a b : List Bool) (c : Bool) (h : a.length=b.length) :
    let r := rippleBorrow a b c
    wordNat a+2^a.length*bitNat r.2 = wordNat b+bitNat c+wordNat r.1 := by
  induction a generalizing b c with
  | nil => cases b <;> simp_all [rippleBorrow,wordNat]
  | cons x xs ih =>
    cases b with
    | nil => simp at h
    | cons y ys =>
      have h' : xs.length=ys.length := by simpa using h
      let s := borrowDigit x y c
      let r := rippleBorrow xs ys s.2
      have hs := borrowDigit_eq x y c
      have ht := ih ys s.2 h'
      dsimp only at ht
      change wordNat xs+2^xs.length*bitNat r.2 =
        wordNat ys+bitNat s.2+wordNat r.1 at ht
      change bitNat x+2*wordNat xs+2^(xs.length+1)*bitNat r.2 =
        bitNat y+2*wordNat ys+bitNat c+(bitNat s.1+2*wordNat r.1)
      rw [pow_succ,mul_comm (2^xs.length) 2,Nat.mul_assoc]
      change bitNat x+2*bitNat s.2 = bitNat y+bitNat c+bitNat s.1 at hs
      omega

def divideDigit (divisor remainder : List Bool) (b : Bool) : Bool × List Bool :=
  let z := b::remainder
  let sub := rippleBorrow z (divisor++[false]) false
  (!sub.2,(if sub.2 then z else sub.1).take divisor.length)

theorem divideDigit_exact (divisor remainder : List Bool) (b : Bool)
    (hlen : remainder.length=divisor.length) (hr : wordNat remainder < wordNat divisor) :
    let p := divideDigit divisor remainder b
    p.2.length=divisor.length ∧ wordNat p.2 < wordNat divisor ∧
    wordNat divisor*bitNat p.1 + wordNat p.2 = 2*wordNat remainder + bitNat b := by
  let z := b::remainder
  let dv := divisor++[false]
  let sub := rippleBorrow z dv false
  have hlen' : z.length=dv.length := by simp [z,dv,hlen]
  have hd : wordNat dv=wordNat divisor := by simp [dv,wordNat_append,wordNat,bitNat]
  have hspec := rippleBorrow_value z dv false hlen'
  change wordNat z+2^z.length*bitNat sub.2 =
    wordNat dv+bitNat false+wordNat sub.1 at hspec
  have hout : sub.1.length=z.length := rippleBorrow_length z dv false hlen'
  have lt := wordNat_lt_width sub.1
  rw [hout] at lt
  have hz : wordNat z < 2*wordNat divisor := by cases b <;> simp [z,wordNat,bitNat] <;> omega
  have hconst : wordNat divisor < 2^divisor.length := wordNat_lt_width _
  have zrep : wordNat z = 2*wordNat remainder + bitNat b := by simp [z,wordNat,Nat.add_comm]
  change ((if sub.2 then z else sub.1).take divisor.length).length = divisor.length ∧
    wordNat ((if sub.2 then z else sub.1).take divisor.length) < wordNat divisor ∧
    wordNat divisor * bitNat (!sub.2) +
    wordNat ((if sub.2 then z else sub.1).take divisor.length) = 2*wordNat remainder+bitNat b
  rw [← zrep]
  cases he : sub.2 with
  | false =>
    have hs : wordNat z=wordNat divisor+wordNat sub.1 := by simpa [he,hd,bitNat] using hspec
    have hsmall : wordNat sub.1 < wordNat divisor := by omega
    have hlt : divisor.length ≤ sub.1.length := by rw [hout]; simp [z,hlen]
    simp [bitNat,List.length_take,Nat.min_eq_left hlt,
      wordNat_take_width _ _ (hsmall.trans hconst),hsmall,hs]
  | true =>
    have hs : wordNat z+2^z.length=wordNat divisor+wordNat sub.1 := by
      simpa [he,hd,bitNat] using hspec
    have hsmall : wordNat z < wordNat divisor := by omega
    have hlt : divisor.length ≤ z.length := by simp [z,hlen]
    simp [bitNat,List.length_take,Nat.min_eq_left hlt,
      wordNat_take_width _ _ (hsmall.trans hconst),hsmall]

def feedValue : List Bool → ℕ → ℕ
  | [], t => t
  | b::bs,t => feedValue bs (2*t+bitNat b)

def divisionDigits (divisor : List Bool) : List Bool → List Bool × List Bool → List Bool × List Bool
  | [],s => s
  | b::bs,s =>
    let t := divideDigit divisor s.2 b
    divisionDigits divisor bs (t.1::s.1,t.2)

theorem divisionDigits_exact (divisor digits : List Bool) (s : List Bool × List Bool)
    (hlen : s.2.length=divisor.length) (hr : wordNat s.2 < wordNat divisor) :
    let out := divisionDigits divisor digits s
    out.2.length=divisor.length ∧ wordNat out.2 < wordNat divisor ∧
    wordNat divisor*wordNat out.1+wordNat out.2 =
      feedValue digits (wordNat divisor*wordNat s.1+wordNat s.2) := by
  induction digits generalizing s with
  | nil => exact ⟨hlen,hr,rfl⟩
  | cons b bs ih =>
    let u := divideDigit divisor s.2 b
    obtain ⟨hl,hs,he⟩ := divideDigit_exact divisor s.2 b hlen hr
    change wordNat divisor * bitNat u.1 + wordNat u.2 = _ at he
    have hb : wordNat divisor * wordNat (u.1::s.1)+wordNat u.2 =
        2*(wordNat divisor * wordNat s.1+wordNat s.2)+bitNat b := by
      rw [wordNat]
      calc
       _ = 2*(wordNat divisor * wordNat s.1) + (wordNat divisor*bitNat u.1+wordNat u.2) := by ring
       _ = _ := by rw [he]; ring
    obtain ⟨l,r,h⟩ := ih (u.1::s.1,u.2) hl hs
    change _ = feedValue bs (wordNat divisor * wordNat (u.1::s.1)+wordNat u.2) at h
    rw [hb] at h
    exact ⟨l,r,h⟩

theorem zeroWordNat (n : ℕ) : wordNat (List.replicate n false)=0 := by
  induction n with
  | zero => decide
  | succ n ih => simp [List.replicate_succ,wordNat,bitNat,ih]

def binaryDivide (divisor msbInput : List Bool) : List Bool :=
  (divisionDigits divisor msbInput ([],List.replicate divisor.length false)).1

theorem binaryDivide_exact (divisor msbInput : List Bool) (hd : 0 < wordNat divisor) :
    wordNat (binaryDivide divisor msbInput) = feedValue msbInput 0 / wordNat divisor := by
  have hr : wordNat (List.replicate divisor.length false) < wordNat divisor := by
    rw [zeroWordNat]
    exact hd
  obtain ⟨_,hr',he⟩ := divisionDigits_exact divisor msbInput
    ([],List.replicate divisor.length false) (by simp) hr
  have he' : wordNat divisor*wordNat (binaryDivide divisor msbInput) +
        wordNat (divisionDigits divisor msbInput ([],List.replicate divisor.length false)).2 =
        feedValue msbInput 0 := by
    simpa only [wordNat,zeroWordNat,mul_zero,add_zero] using he
  rw [← he',Nat.mul_add_div hd,Nat.div_eq_of_lt hr',Nat.add_zero]

/-- Per numerator bit: one scan of the padded divisor for the borrow,
one bounded copy/take of the chosen result and constant digit writes.
Each borrow step is a constant-size Boolean transition. -/
def divisionSchedule (msbInput divisor : List Bool) : ℕ :=
  msbInput.length*(2*divisor.length+5)

theorem normalizer_divide_exact {u c : ℕ} (tap : Fin u → Option (Fin c))
    (cap : ∀ a, Acquisition.unaryLoad tap a ≤ 2) (bits : List Bool) :
    wordNat (binaryDivide (binaryNormalizer tap) bits) =
      feedValue bits 0 / Acquisition.publicFactor tap := by
  have he := binaryNormalizer_exact tap cap
  rw [binaryDivide_exact _ _ (by rw [he]; exact Acquisition.publicFactor_pos tap),he]

theorem divisionSchedule_quadratic {u c : ℕ} (tap : Fin u → Option (Fin c)) (word : List Bool) :
    divisionSchedule word (binaryNormalizer tap) ≤ 13*(word.length+c+1)^2 := by
  have hlen : (binaryNormalizer tap).length = 1+3*c := by
    simp [binaryNormalizer,multiplyFactors_length,factorTape]
  unfold divisionSchedule
  rw [hlen]
  nlinarith

#print axioms wordNat_take_width
#print axioms rippleBorrow_value
#print axioms divideDigit_exact
#print axioms divisionDigits_exact
#print axioms binaryDivide_exact
#print axioms normalizer_divide_exact
#print axioms divisionSchedule_quadratic

end AAcquisitionCost
