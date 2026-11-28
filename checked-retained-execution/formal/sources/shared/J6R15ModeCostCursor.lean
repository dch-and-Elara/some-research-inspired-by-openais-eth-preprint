import AOracleMachineTimeTape
import J6R12CollisionMenu

/-! An unsigned fixed-width subtraction supplies both the actual
budget result and its underflow bit. Each sibling is reached by one
subtraction and one ripple increment, not uncharged Nat division. -/
namespace J6R15ModeCost
open AOracleMachineTime AOracleMachineTimeTape J6R12CollisionMenu

structure Word (q : ℕ) where
  bits : List Bool
  size : bits.length=q

def word {q : ℕ} (n : ℕ) : Word q := ⟨encodeBits q n,encodeBits_length q n⟩

def Word.val {q : ℕ} (w : Word q) : ℕ := bitsValue w.bits

theorem word_val {q n : ℕ} (hn : n<2^q) :
    (word (q:=q) n).val=n := encodeBits_exact _ _ hn

theorem val_lt {q : ℕ} (x : Word q) : x.val<2^q :=
  by simpa only [Word.val,x.size] using bitsValue_lt x.bits

theorem valued_word {q : ℕ} (x : Word q) : word x.val=x := by
  cases x with
  | mk xs hs =>
    have H : (encodeBits q (bitsValue xs)).length=xs.length := by rw [encodeBits_length,hs]
    have h := equal_width_inj H (encodeBits_exact _ _ (val_lt (Word.mk xs hs)))
    unfold word Word.val
    simp only [h]

def diffDigit (x y b : Bool) : Bool × Bool :=
  ((x != y) != b,(!x && (y || b)) || (y && b))

theorem diffDigit_exact (x y b : Bool) :
    x.toNat+2*(diffDigit x y b).2.toNat =
      y.toNat+b.toNat+(diffDigit x y b).1.toNat := by
  cases x <;> cases y <;> cases b <;> decide

def diffCore (b : Bool) : List (Bool × Bool) → Meter (List Bool × Bool)
  | [] => ⟨([],b),0⟩
  | (u,v)::xs =>
    let s := diffDigit u v b
    let r := diffCore s.2 xs
    ⟨(s.1::r.result.1,r.result.2),r.steps+12⟩

theorem diffCore_exact (b : Bool) (xs : List (Bool×Bool)) :
    let d := diffCore b xs
    d.result.1.length=xs.length ∧
    bitsValue (xs.map Prod.fst)+2^xs.length*d.result.2.toNat =
      bitsValue (xs.map Prod.snd)+b.toNat+bitsValue d.result.1 ∧
    d.steps=12*xs.length := by
  induction xs generalizing b with
  | nil => simp [diffCore,bitsValue]
  | cons a xs ih =>
    rcases a with ⟨u,v⟩
    let s := diffDigit u v b
    let r := diffCore s.2 xs
    obtain ⟨hl,hv,ht⟩ := ih s.2
    have hs := diffDigit_exact u v b
    change u.toNat+2*s.2.toNat=v.toNat+b.toNat+s.1.toNat at hs
    change ((s.1::r.result.1).length=_) ∧
      (bitsValue (u::xs.map Prod.fst)+2^(xs.length+1)*r.result.2.toNat=
        bitsValue (v::xs.map Prod.snd)+b.toNat+bitsValue (s.1::r.result.1)) ∧
      (r.steps+12=12*(xs.length+1))
    change r.result.1.length=_ at hl
    change bitsValue (xs.map Prod.fst)+2^xs.length*r.result.2.toNat=
      bitsValue (xs.map Prod.snd)+s.2.toNat+bitsValue r.result.1 at hv
    change r.steps=_ at ht
    rw [List.length_cons,hl,List.length_cons,ht,Nat.mul_succ]
    simp only [true_and,and_true,bitsValue,pow_succ,Nat.mul_assoc]
    nlinarith

def subtract {q : ℕ} (x y : Word q) : Meter (Word q × Bool) :=
  let z := diffCore false (x.bits.zip y.bits)
  ⟨(⟨z.result.1,by rw [(diffCore_exact _ _).1,List.length_zip,x.size,y.size,min_self]⟩,
    z.result.2),z.steps+4*q+6⟩

theorem subtract_exact {q : ℕ} (x y : Word q) :
    let z := subtract x y
    (z.result.2=false ↔ y.val≤x.val) ∧
    (z.result.2=false → z.result.1.val=x.val-y.val) ∧
    z.steps=16*q+6 := by
  let d := diffCore false (x.bits.zip y.bits)
  have hW : x.bits.length=y.bits.length := by rw [x.size,y.size]
  obtain ⟨hl,hv,ht⟩ := diffCore_exact false (x.bits.zip y.bits)
  change d.result.1.length=_ at hl
  change d.steps=_ at ht
  change bitsValue ((x.bits.zip y.bits).map Prod.fst)+2^(x.bits.zip y.bits).length*d.result.2.toNat =
    bitsValue ((x.bits.zip y.bits).map Prod.snd)+Bool.false.toNat+bitsValue d.result.1 at hv
  rw [zip_map_fst _ _ hW,zip_map_snd _ _ hW,List.length_zip,x.size,y.size,min_self] at hv
  rw [List.length_zip,x.size,y.size,min_self] at hl ht
  have hz := bitsValue_lt d.result.1
  rw [hl] at hz
  have hx := val_lt x
  have hy := val_lt y
  change x.val+2^q*d.result.2.toNat=y.val+Bool.false.toNat+bitsValue d.result.1 at hv
  change (d.result.2=false ↔ y.val≤x.val) ∧
    (d.result.2=false → bitsValue d.result.1=x.val-y.val) ∧
    d.steps+4*q+6=16*q+6
  cases he : d.result.2 <;> simp [he] at hv ⊢ <;> omega

def increment {q : ℕ} (w : Word q) : Meter (Word q) :=
  let r := addBits w.bits (encodeBits q 1)
  ⟨⟨r.result,by
      rw [(addBits_exact w.bits (encodeBits q 1) (by rw [w.size,encodeBits_length])).1,w.size]⟩,
    r.steps+q+4⟩

theorem increment_exact {q : ℕ} (hq : 0<q) (w : Word q) (h : w.val+1<2^q) :
    (increment w).result.val=w.val+1 ∧ (increment w).steps=13*q+4 := by
  have h1 : 1<(2:ℕ)^q := one_lt_pow₀ (by decide) hq.ne'
  obtain ⟨_,hv,hs⟩ := addBits_exact w.bits (encodeBits q 1) (by rw [w.size,encodeBits_length])
  constructor
  · change bitsValue (addBits w.bits (encodeBits q 1)).result=_
    rw [hv,encodeBits_exact _ _ h1,w.size]
    exact Nat.mod_eq_of_lt h
  · change (addBits w.bits (encodeBits q 1)).steps+q+4=_
    rw [hs,w.size]
    omega

structure Cursor (q : ℕ) where
  rem : Word q
  counter : Word q

def advance {q : ℕ} (w : Word q) (c : Cursor q) : Meter (Option (Cursor q)) :=
  let s := subtract c.rem w
  if s.result.2 then ⟨none,s.steps+6⟩
  else
    let a := increment c.counter
    ⟨some ⟨s.result.1,a.result⟩,s.steps+a.steps+6*q+12⟩

def Cursor.need {q : ℕ} (w : Word q) (c : Cursor q) : ℕ :=
  w.val*c.counter.val+c.rem.val

theorem advance_bound {q : ℕ} (w : Word q) (c : Cursor q) :
    (advance w c).steps≤35*q+22 := by
  let s := subtract c.rem w
  have hS : s.steps=16*q+6 := (subtract_exact c.rem w).2.2
  let a := increment c.counter
  have ha : a.steps=13*q+4 := by
    change (addBits c.counter.bits (encodeBits q 1)).steps+q+4=_
    rw [(addBits_exact c.counter.bits (encodeBits q 1)
        (by rw [c.counter.size,encodeBits_length])).2.2,c.counter.size]
    omega
  change (if s.result.2 then (⟨none,s.steps+6⟩ : Meter (Option (Cursor q))) else
    ⟨some ⟨s.result.1,a.result⟩,s.steps+a.steps+6*q+12⟩).steps≤_
  cases s.result.2 <;> simp [hS,ha] <;> omega

theorem advance_exact {q : ℕ} (hq : 0<q) (w : Word q) (c : Cursor q)
    (hw : 0<w.val) (hB : c.need w<2^q) :
    let z := advance w c
    (z.result=none ↔ c.rem.val<w.val) ∧
    ∀ u, z.result=some u →
      u.counter.val=c.counter.val+1 ∧ u.rem.val=c.rem.val-w.val ∧
      u.need w=c.need w ∧ u.rem.val<c.rem.val := by
  let s := subtract c.rem w
  obtain ⟨hV,hD,_⟩ := subtract_exact c.rem w
  change (s.result.2=false ↔ w.val≤c.rem.val) at hV
  change (s.result.2=false → s.result.1.val=c.rem.val-w.val) at hD
  change w.val*c.counter.val+c.rem.val<2^q at hB
  let a := increment c.counter
  change ((if s.result.2 then (⟨none,s.steps+6⟩ : Meter (Option (Cursor q))) else
    ⟨some ⟨s.result.1,a.result⟩,s.steps+a.steps+6*q+12⟩).result=none ↔ _) ∧ _
  cases he : s.result.2 with
  | true =>
    have hLT : c.rem.val<w.val := by
      apply Nat.lt_of_not_ge
      intro h
      have := hV.mpr h
      simp [he] at this
    simp [advance,show (subtract c.rem w).result.2=true from he,hLT]
  | false =>
    have ho := hV.mp he
    have hcount : c.counter.val+1<2^q := by
      have hM := Nat.le_mul_of_pos_left c.counter.val hw
      omega
    have hv := (increment_exact hq c.counter hcount).1
    have hs := hD he
    have hh : ¬ c.rem.val<w.val := Nat.not_lt.mpr ho
    refine ⟨by simp [hh],?_⟩
    intro u hu
    have hu' : u=⟨s.result.1,(increment c.counter).result⟩ := by
      simpa only [advance,show (subtract c.rem w).result.2=false from he,Bool.false_eq_true,
        if_false,Option.some.injEq] using hu.symm
    rcases hu' with rfl
    refine ⟨hv,hs,?_,?_⟩
    · unfold Cursor.need
      dsimp only
      rw [hv,hs,Nat.mul_succ]
      omega
    · change s.result.1.val<c.rem.val
      omega

#print axioms diffCore_exact
#print axioms subtract_exact
#print axioms increment_exact
#print axioms advance_exact
#print axioms advance_bound
end J6R15ModeCost




