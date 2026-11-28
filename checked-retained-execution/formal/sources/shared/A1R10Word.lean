import A1R9Blocks

/-! Exact fixed-width scalar gates used by the double-quotient verifier.
`Meter` tracks Boolean tape operations; residues are only denotations. -/

namespace A1R10
open AOracleMachineTime AOracleMachineTimeMul AOracleMachineTimeTape

structure Gates (A : Type*) where
  zero : A
  add : A → A → Meter A
  mul : A → A → Meter A
  sub : A → A → Meter A
  move : ℕ
  budget : ℕ

structure Ops (A R : Type*) [Ring R] extends Gates A where
  read : A → R
  zero_read : read zero = 0
  add_read : ∀ a b, read (add a b).result = read a+read b
  mul_read : ∀ a b, read (mul a b).result = read a*read b
  sub_read : ∀ a b, read (sub a b).result = read a-read b
  add_cost : ∀ a b, (add a b).steps ≤ budget
  mul_cost : ∀ a b, (mul a b).steps ≤ budget
  sub_cost : ∀ a b, (sub a b).steps ≤ budget

instance {A R : Type*} [Ring R] : CoeOut (Ops A R) (Gates A) := ⟨Ops.toGates⟩

abbrev Word (p : ℕ) := {x : List Bool // x.length=p}

def wordZero (p : ℕ) : Word p := ⟨List.replicate p false, by simp⟩

def wordOne (p : ℕ) : Word p := ⟨encodeBits p 1, encodeBits_length p 1⟩

def wordRead {p : ℕ} (a : Word p) : ZMod (2^p) := asResidue p a.val

theorem wordOne_read (p : ℕ) (hp : 0<p) : wordRead (wordOne p)=1 :=
  A1R9.value_encode_one p hp

def addWord {p : ℕ} (a b : Word p) : Meter (Word p) :=
  let t := addBits a.val b.val
  ⟨⟨t.result, (addBits_exact a.val b.val (a.property.trans b.property.symm)).1.trans a.property⟩, t.steps⟩

def mulWord {p : ℕ} (a b : Word p) : Meter (Word p) :=
  let t := multiply a.val b.val
  ⟨⟨t.result, (multiply_result p a.val b.val a.property).1⟩, t.steps⟩

def subWord {p : ℕ} (hp : 0<p) (a b : Word p) : Meter (Word p) :=
  let t := A1R9.negWord p b.val
  let u := addWord a ⟨t.result,(A1R9.negWord_exact p hp b.val b.property).1⟩
  ⟨u.result, t.steps+u.steps⟩

theorem addWord_read {p : ℕ} (a b : Word p) :
    wordRead (addWord a b).result=wordRead a+wordRead b :=
  add_residue p a.val b.val a.property b.property

theorem mulWord_read {p : ℕ} (a b : Word p) :
    wordRead (mulWord a b).result=wordRead a*wordRead b :=
  (multiply_result p a.val b.val a.property).2.1

theorem subWord_read {p : ℕ} (hp : 0<p) (a b : Word p) :
    wordRead (subWord hp a b).result=wordRead a-wordRead b := by
  rw [subWord, addWord_read]
  change wordRead a + asResidue p (A1R9.negWord p b.val).result=_
  rw [(A1R9.negWord_exact p hp b.val b.property).2.1,sub_eq_add_neg]
  rfl

def wordOps (p : ℕ) (hp : 0<p) : Ops (Word p) (ZMod (2^p)) where
  read := wordRead
  zero := wordZero p
  zero_read := by simp [wordZero,wordRead,asResidue,value_zero]
  add := addWord
  mul := mulWord
  sub := subWord hp
  add_read := addWord_read
  mul_read := mulWord_read
  sub_read := subWord_read hp
  move := p
  budget := 32*(p+1)^2
  add_cost a b := by
    change (addBits a.val b.val).steps ≤ _
    rw [(addBits_exact a.val b.val (a.property.trans b.property.symm)).2.2,a.property]
    nlinarith
  mul_cost a b := (square_word_cost p a.val b.val a.property b.property).trans (by omega)
  sub_cost a b := by
    let t := A1R9.negWord p b.val
    obtain ⟨hl,_,hc⟩ := A1R9.negWord_exact p hp b.val b.property
    change (A1R9.negWord p b.val).steps + (addBits a.val t.result).steps ≤ _
    rw [hc,(addBits_exact a.val t.result (a.property.trans hl.symm)).2.2,a.property]
    nlinarith

#print axioms wordOne_read
#print axioms addWord_read
#print axioms mulWord_read
#print axioms subWord_read
#print axioms wordOps
end A1R10



