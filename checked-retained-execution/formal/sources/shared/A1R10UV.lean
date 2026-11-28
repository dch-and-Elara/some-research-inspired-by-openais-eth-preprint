import A1R10Monic
import AOracleCoordinates

/-! Genuine packed left-to-right scans for the native double quotient
(ℤ/2^p)[U,V]/(f(U),V^ell), with f given by its lower coefficients.
The runtime definitions use Gates (not the noncomputable denotation Ops). -/

open scoped Polynomial
namespace A1R10
open AOracleMachineTime Polynomial AOracleCoordinates

noncomputable abbrev Modulus (p : ℕ) (hp : 0<p) (f : List (Word p)) :=
  modulus (wordOps p hp) f

abbrev UBlock {p : ℕ} (f : List (Word p)) := {v : List (Word p) // v.length=f.length}

noncomputable def uRead {p : ℕ} (hp : 0<p) (f : List (Word p)) (a : UBlock f) :
    AdjoinRoot (Modulus p hp f) :=
  AdjoinRoot.mk (Modulus p hp f) (decode (wordOps p hp) a.val)

def uAdd {p : ℕ} (hp : 0<p) {f : List (Word p)} (a b : UBlock f) : Meter (UBlock f) :=
  let q := addRows (wordOps p hp) a.val b.val
  ⟨⟨q.result,(addRows_exact (wordOps p hp) a.val b.val (a.property.trans b.property.symm)).1.trans
    a.property⟩,q.steps⟩

def uMul {p : ℕ} (hp : 0<p) {f : List (Word p)} (a b : UBlock f) : Meter (UBlock f) :=
  let q := uProduct (wordOps p hp) f a.val b.val
  ⟨⟨q.result,(uProduct_exact (wordOps p hp) f a.val b.val a.property b.property).1⟩,q.steps⟩

def uSub {p : ℕ} (hp : 0<p) {f : List (Word p)} (a b : UBlock f) : Meter (UBlock f) :=
  let q := subtractScaled (wordOps p hp) (wordOne p) b.val a.val
  ⟨⟨q.result,(subtractScaled_exact (wordOps p hp) (wordOne p) b.val a.val
    (by rw [a.property,b.property])).1.trans a.property⟩,q.steps⟩

def uBudgetGates (e p : ℕ) (hp : 0<p) : ℕ :=
  uBudget (wordOps p hp).toGates e+e*(2*(wordOps p hp).budget+4*((wordOps p hp).move+1))

def uGates {p : ℕ} (hp : 0<p) (f : List (Word p)) : Gates (UBlock f) where
  zero := ⟨zeros (wordOps p hp) f.length,zeros_len ..⟩
  add := uAdd hp
  mul := uMul hp
  sub := uSub hp
  move := f.length*p
  budget := uBudgetGates f.length p hp

noncomputable def uOps {p : ℕ} (hp : 0<p) (f : List (Word p)) :
    Ops (UBlock f) (AdjoinRoot (Modulus p hp f)) where
  toGates := uGates hp f
  read := uRead hp f
  zero_read := by
    change AdjoinRoot.mk _ (decode (wordOps p hp) (zeros (wordOps p hp) f.length))=0
    simp
  add_read a b := by
    change AdjoinRoot.mk _ (decode (wordOps p hp) (addRows (wordOps p hp) a.val b.val).result)=_
    rw [(addRows_exact (wordOps p hp) _ _ (a.property.trans b.property.symm)).2.1,map_add]
    rfl
  mul_read a b := (uProduct_exact (wordOps p hp) f a.val b.val a.property b.property).2.1
  sub_read a b := by
    change AdjoinRoot.mk _ (decode (wordOps p hp)
      (subtractScaled (wordOps p hp) (wordOne p) b.val a.val).result)=_
    have h : b.val.length≤a.val.length := by rw [b.property,a.property]
    rw [(subtractScaled_exact (wordOps p hp) _ _ _ h).2.1,a.property,b.property,Nat.sub_self]
    change AdjoinRoot.mk _ (decode (wordOps p hp) a.val -
      C (wordRead (wordOne p)) * (X^0*decode (wordOps p hp) b.val))=_
    rw [wordOne_read p hp,pow_zero,C_1,one_mul,one_mul,map_sub]
    rfl
  add_cost a b := by
    have h := (addRows_exact (wordOps p hp) _ _ (a.property.trans b.property.symm)).2.2
    rw [a.property] at h
    change (addRows (wordOps p hp) a.val b.val).steps≤uBudgetGates f.length p hp
    apply h.trans
    unfold uBudgetGates
    have hh : (wordOps p hp).budget+4*((wordOps p hp).move+1)
        ≤ 2*(wordOps p hp).budget+4*((wordOps p hp).move+1) := by omega
    have hhh := Nat.mul_le_mul_left f.length hh
    omega
  mul_cost a b := by
    have h := (uProduct_exact (wordOps p hp) f a.val b.val a.property b.property).2.2
    change (uProduct (wordOps p hp) f a.val b.val).steps≤uBudgetGates f.length p hp
    exact h.trans (Nat.le_add_right _ _)
  sub_cost a b := by
    have h : b.val.length≤a.val.length := by rw [b.property,a.property]
    have hc := (subtractScaled_exact (wordOps p hp) (wordOne p) _ _ h).2.2
    rw [b.property] at hc
    change (subtractScaled (wordOps p hp) (wordOne p) b.val a.val).steps≤uBudgetGates f.length p hp
    exact hc.trans (Nat.le_add_left _ _)

variable {A R : Type*} [CommRing R]

theorem decode_drop_quotient (o : Ops A R) (a : List A) (n ell : ℕ)
    (h : a.length=n+ell) :
    AdjoinRoot.mk (X^ell : R[X]) (decode o (a.drop n)) =
      AdjoinRoot.mk (X^ell : R[X]) (decode o a) := by
  have hl : (a.drop n).length=ell := by simp [h]
  have ha := decode_append o (a.take n) (a.drop n)
  rw [List.take_append_drop,hl] at ha
  rw [ha,map_add,map_mul,AdjoinRoot.mk_self,zero_mul,zero_add]

abbrev UVBlock {p : ℕ} (f : List (Word p)) (ell : ℕ) :=
  {v : List (UBlock f) // v.length=ell}

noncomputable def uvRead {p : ℕ} (hp : 0<p) (f : List (Word p)) (ell : ℕ)
    (a : UVBlock f ell) : Truncated (Modulus p hp f) ell :=
  AdjoinRoot.mk (Polynomial.X^ell) (decode (uOps hp f) a.val)

/-- Multiply with monic elimination in every inner product; afterwards
drop the high V half. Scan/copy overhead is charged explicitly. -/
def uvMul {p : ℕ} (hp : 0<p) {f : List (Word p)} {ell : ℕ}
    (a b : UVBlock f ell) : Meter (UVBlock f ell) :=
  let c := convolve (uGates hp f) a.val b.val
  let len := (convolve_exact (uOps hp f) a.val b.val).1
  have hd : (c.result.drop ell).length=ell := by
    change ((convolve (uOps hp f) a.val b.val).result.drop ell).length=ell
    simp [len,a.property,b.property]
  ⟨⟨c.result.drop ell,hd⟩,c.steps+(6*ell+2)*((uGates hp f).move+1)⟩

def uvBudget (e ell p : ℕ) (hp : 0<p) : ℕ :=
  (ell+1)*(2*ell+1)*(4*(uBudgetGates e p hp+4*(e*p+1)))+(6*ell+2)*(e*p+1)

theorem uvMul_exact {p : ℕ} (hp : 0<p) {f : List (Word p)} {ell : ℕ}
    (a b : UVBlock f ell) :
    uvRead hp f ell (uvMul hp a b).result=uvRead hp f ell a*uvRead hp f ell b ∧
    (uvMul hp a b).steps≤uvBudget f.length ell p hp := by
  let g := uOps hp f
  let c := convolve g a.val b.val
  obtain ⟨hshape,hden,hcost⟩ := convolve_exact g a.val b.val
  rw [a.property,b.property] at hshape hcost
  constructor
  · change AdjoinRoot.mk (X^ell) (decode g (c.result.drop ell)) = _
    rw [decode_drop_quotient g c.result ell ell hshape]
    change AdjoinRoot.mk (X^ell) (decode g (convolve g a.val b.val).result)=_
    rw [hden,map_mul]
    rfl
  · change c.steps+(6*ell+2)*(f.length*p+1)≤uvBudget f.length ell p hp
    rw [← two_mul] at hcost
    exact Nat.add_le_add_right hcost _

#print axioms uOps
#print axioms decode_drop_quotient
#print axioms uvMul_exact
end A1R10


