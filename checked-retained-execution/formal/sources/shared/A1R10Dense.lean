import A1R10Word

/-! Descending coefficient tapes. The loops below use only sequential row
walks, literal zero padding and verified coefficient operations. Length and
copy traffic are charged with per-coefficient width, not free indexed access. -/

open scoped Polynomial
namespace A1R10
open AOracleMachineTime Polynomial

variable {A R : Type*} [CommRing R] (o : Ops A R)

noncomputable def decode : List A → R[X]
  | [] => 0
  | a::as => monomial as.length (o.read a) + decode as

def zeros (o : Gates A) (n : ℕ) : List A := List.replicate n o.zero

@[simp] theorem zeros_len (o : Gates A) (n : ℕ) : (zeros o n).length=n := by simp [zeros]

@[simp] theorem decode_zeros (n : ℕ) : decode o (zeros o n)=0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change decode o (o.zero :: zeros o n)=0
    simpa [decode,o.zero_read] using ih

@[simp] theorem decode_zero_cons (a : List A) : decode o (o.zero::a)=decode o a := by
  simp [decode,o.zero_read]

theorem decode_append (a b : List A) :
    decode o (a++b)=X^b.length*decode o a+decode o b := by
  induction a with
  | nil => simp [decode]
  | cons x a ih =>
    simp only [List.cons_append,decode,List.length_append,ih,mul_add,X_pow_mul_monomial]
    abel

theorem decode_coeff_zero (a : List A) (k : ℕ) (h : a.length≤k) :
    (decode o a).coeff k=0 := by
  induction a with
  | nil => simp [decode]
  | cons x a ih =>
    simp only [List.length_cons] at h
    rw [decode,coeff_add,coeff_monomial_of_ne _ (by omega),ih (by omega),add_zero]

/-- One complete linear tape walk. -/
def timesRow (o : Gates A) (a : A) : List A → Meter (List A)
  | [] => ⟨[],0⟩
  | x::xs =>
    let m := o.mul a x
    let tail := timesRow o a xs
    ⟨m.result::tail.result,m.steps+tail.steps+4*(o.move+1)⟩

theorem timesRow_exact (a : A) (xs : List A) :
    (timesRow o a xs).result.length=xs.length ∧
    decode o (timesRow o a xs).result=C (o.read a)*decode o xs ∧
    (timesRow o a xs).steps≤xs.length*(o.budget+4*(o.move+1)) := by
  induction xs with
  | nil => simp [timesRow,decode]
  | cons x xs ih =>
    obtain ⟨hl,hr,hc⟩ := ih
    refine ⟨by simp only [timesRow,List.length_cons,hl], ?_, ?_⟩
    · simp only [timesRow,hl,decode,hr,o.mul_read,mul_add,C_mul_monomial]
    · change (o.mul a x).steps+(timesRow o a xs).steps+4*(o.move+1)
        ≤ (xs.length+1)*(o.budget+4*(o.move+1))
      rw [Nat.succ_mul xs.length]
      have h := o.mul_cost a x
      omega

/-- Equal-length rows are zip-added; the total function also supports an
empty tape and exposes the surviving suffix without copying it. -/
def addRows (o : Gates A) : List A → List A → Meter (List A)
  | [],ys => ⟨ys,0⟩
  | x::xs,[] => ⟨x::xs,0⟩
  | x::xs,y::ys =>
    let m := o.add x y
    let tail := addRows o xs ys
    ⟨m.result::tail.result,m.steps+tail.steps+4*(o.move+1)⟩

theorem addRows_exact (xs ys : List A) (h : xs.length=ys.length) :
    (addRows o xs ys).result.length=xs.length ∧
    decode o (addRows o xs ys).result=decode o xs+decode o ys ∧
    (addRows o xs ys).steps≤xs.length*(o.budget+4*(o.move+1)) := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => simp [addRows,decode]
    | cons y ys => simp at h
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp only [List.length_cons,Nat.add_right_cancel_iff] at h
      obtain ⟨hl,hr,hc⟩ := ih ys h
      refine ⟨by simp only [addRows,List.length_cons,hl], ?_, ?_⟩
      · simp only [addRows,hl,decode,hr,o.add_read,monomial_add,← h]
        abel
      · change (o.add x y).steps+(addRows o xs ys).steps+4*(o.move+1)
          ≤ (xs.length+1)*(o.budget+4*(o.move+1))
        rw [Nat.succ_mul xs.length]
        have hh := o.add_cost x y
        omega

/-- A schoolbook multiplication, by one shifted row and one addition per
first input coefficient. The redundant high zero is kept in the tape:
output length is exactly |a|+|b|, also when a or b is empty. -/
def convolve (o : Gates A) : List A → List A → Meter (List A)
  | [],ys => ⟨zeros o ys.length,(2*ys.length+1)*(o.move+1)⟩
  | x::xs,ys =>
    let lo := convolve o xs ys
    let hi := timesRow o x ys
    let row := o.zero::(hi.result ++ zeros o xs.length)
    let m := addRows o row (o.zero::lo.result)
    ⟨m.result,lo.steps+hi.steps+m.steps+4*(xs.length+ys.length+2)*(o.move+1)⟩

def lane (o : Gates A) : ℕ := 4*(o.budget+4*(o.move+1))

theorem convolve_exact (xs ys : List A) :
    (convolve o xs ys).result.length=xs.length+ys.length ∧
    decode o (convolve o xs ys).result=decode o xs*decode o ys ∧
    (convolve o xs ys).steps≤(xs.length+1)*(xs.length+ys.length+1)*lane o.toGates := by
  induction xs with
  | nil =>
    simp only [convolve,zeros_len,decode_zeros,decode,zero_mul,List.length_nil,zero_add,one_mul,
      true_and]
    unfold lane
    nlinarith [Nat.zero_le (ys.length*(o.move+1)),Nat.zero_le ((ys.length+1)*o.budget)]
  | cons x xs ih =>
    obtain ⟨hl,hr,hc⟩ := ih
    obtain ⟨hl',hr',hc'⟩ := timesRow_exact o x ys
    let row := o.zero::((timesRow o x ys).result ++ zeros o xs.length)
    let lo := o.zero::(convolve o xs ys).result
    have he : row.length=lo.length := by
      simp [row,lo,hl,hl',Nat.add_comm]
    obtain ⟨hm,hs,ht⟩ := addRows_exact o row lo he
    have hlen : row.length=xs.length+ys.length+1 := by
      simp [row,hl',Nat.add_comm]
    change (addRows o row lo).result.length=(x::xs).length+ys.length ∧ _ ∧ _
    refine ⟨by rw [hm,hlen,List.length_cons]; omega,?_,?_⟩
    · change decode o (addRows o row lo).result = decode o (x::xs)*decode o ys
      rw [hs]
      rw [show decode o row=X^xs.length*(C (o.read x)*decode o ys) by
        simp only [row,decode_zero_cons,decode_append,zeros_len,decode_zeros,add_zero,hr']]
      rw [show decode o lo=decode o xs*decode o ys by simp only [lo,decode_zero_cons,hr]]
      simp only [decode]
      rw [add_mul,← mul_assoc,mul_comm _ (C (o.read x))]
      simp [C_mul_monomial,← monomial_one_right_eq_X_pow]
    · change (convolve o xs ys).steps+(timesRow o x ys).steps+(addRows o row lo).steps+
        4*(xs.length+ys.length+2)*(o.move+1) ≤ _ 
      rw [hlen] at ht
      let k := xs.length+ys.length+2
      let w := o.budget+4*(o.move+1)
      have hby : ys.length≤k := by dsimp [k]; omega
      have hrow : xs.length+ys.length+1≤k := by dsimp [k]; omega
      have hmove : 4*(o.move+1)≤w := by dsimp [w]; omega
      have hcopy : 4*k*(o.move+1)≤k*w := by
        rw [show 4*k*(o.move+1)=k*(4*(o.move+1)) by ring]
        exact Nat.mul_le_mul_left k hmove
      have ha := hc'.trans (Nat.mul_le_mul_right w hby)
      have hb := ht.trans (Nat.mul_le_mul_right w hrow)
      have hrest : (timesRow o x ys).steps+(addRows o row lo).steps+4*k*(o.move+1)
          ≤ k*lane o.toGates := by
        change _≤k*(4*w)
        nlinarith [Nat.zero_le (k*w)]
      simp only [List.length_cons]
      calc
        _ ≤ (xs.length+1)*(xs.length+ys.length+1)*lane o.toGates+k*lane o.toGates := by
          change _ + _ + _ + 4*k*(o.move+1) ≤ _
          omega
        _ = ((xs.length+1)*(xs.length+ys.length+1)+k)*lane o.toGates := by ring
        _ ≤ (xs.length+1+1)*(xs.length+1+ys.length+1)*lane o.toGates := by
          apply Nat.mul_le_mul_right
          dsimp [k]
          nlinarith

#print axioms decode_append
#print axioms decode_coeff_zero
#print axioms timesRow_exact
#print axioms addRows_exact
#print axioms convolve_exact
end A1R10



