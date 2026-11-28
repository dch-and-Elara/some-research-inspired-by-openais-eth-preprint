import A1R10Budget

/-! Zero, one, signed arithmetic, and sequential products in the same
native register. Positive physical dimensions suffice for the one tape. -/

open scoped Polynomial
namespace A1R10
open AOracleMachineTime Polynomial AOracleCoordinates

def constantTape {A : Type*} (g : Gates A) (n : ℕ) (a : A) : List A :=
  zeros g (n-1)++[a]

theorem constantTape_len {A : Type*} (g : Gates A) (n : ℕ) (hn : 0<n) (a : A) :
    (constantTape g n a).length=n := by
  simp only [constantTape,List.length_append,zeros_len,List.length_singleton]
  omega

theorem constantTape_read {A R : Type*} [CommRing R] (o : Ops A R) (n : ℕ) (a : A) :
    decode o (constantTape o.toGates n a)=C (o.read a) := by
  rw [constantTape,decode_append,decode_zeros,mul_zero,zero_add]
  simp [decode]

def uOne {p : ℕ} (hp : 0<p) {f : List (Word p)} (he : 0<f.length) : UBlock f :=
  ⟨constantTape (wordOps p hp).toGates f.length (wordOne p),constantTape_len _ _ he _⟩

theorem uOne_read {p : ℕ} (hp : 0<p) {f : List (Word p)} (he : 0<f.length) :
    uRead hp f (uOne hp he)=1 := by
  unfold uRead uOne
  dsimp only
  rw [constantTape_read]
  change AdjoinRoot.mk _ (C (wordRead (wordOne p)))=_
  rw [wordOne_read p hp,C_1,map_one]

def uvZero {p : ℕ} (hp : 0<p) (f : List (Word p)) (ell : ℕ) : UVBlock f ell :=
  ⟨zeros (uGates hp f) ell,zeros_len _ _⟩

def uvOne {p : ℕ} (hp : 0<p) {f : List (Word p)} {ell : ℕ}
    (he : 0<f.length) (hv : 0<ell) : UVBlock f ell :=
  ⟨constantTape (uGates hp f) ell (uOne hp he),constantTape_len _ _ hv _⟩

@[simp] theorem uvZero_read {p : ℕ} (hp : 0<p) (f : List (Word p)) (ell : ℕ) :
    uvRead hp f ell (uvZero hp f ell)=0 := by
  change AdjoinRoot.mk _ (decode (uOps hp f) (zeros (uOps hp f).toGates ell))=_
  rw [decode_zeros,map_zero]

@[simp] theorem uvOne_read {p : ℕ} (hp : 0<p) {f : List (Word p)} {ell : ℕ}
    (he : 0<f.length) (hv : 0<ell) : uvRead hp f ell (uvOne hp he hv)=1 := by
  change AdjoinRoot.mk _ (decode (uOps hp f) (constantTape (uOps hp f).toGates ell
      (uOne hp he)))=_
  rw [constantTape_read]
  change AdjoinRoot.mk _ (C (uRead hp f (uOne hp he)))=_
  rw [uOne_read hp he,C_1,map_one]

def uvAdd {p : ℕ} (hp : 0<p) {f : List (Word p)} {ell : ℕ}
    (a b : UVBlock f ell) : Meter (UVBlock f ell) :=
  let s := addRows (uGates hp f) a.val b.val
  ⟨⟨s.result,(addRows_exact (uOps hp f) _ _ (a.property.trans b.property.symm)).1.trans
      a.property⟩,s.steps⟩

def uvSub {p : ℕ} (hp : 0<p) {f : List (Word p)} {ell : ℕ} (he : 0<f.length)
    (a b : UVBlock f ell) : Meter (UVBlock f ell) :=
  let s := subtractScaled (uGates hp f) (uOne hp he) b.val a.val
  ⟨⟨s.result,(subtractScaled_exact (uOps hp f) _ _ _ (by rw [b.property,a.property])).1.trans
      a.property⟩,s.steps⟩

theorem uvAdd_exact {p : ℕ} (hp : 0<p) {f : List (Word p)} {ell : ℕ}
    (a b : UVBlock f ell) :
    uvRead hp f ell (uvAdd hp a b).result=uvRead hp f ell a+uvRead hp f ell b ∧
    (uvAdd hp a b).steps≤ell*(uBudgetGates f.length p hp+4*(f.length*p+1)) := by
  obtain ⟨_,hr,hc⟩ := addRows_exact (uOps hp f) a.val b.val (a.property.trans b.property.symm)
  refine ⟨?_,?_⟩
  · change AdjoinRoot.mk _ (decode (uOps hp f) (addRows (uOps hp f).toGates a.val b.val).result)=_
    rw [hr,map_add]
    rfl
  · rwa [a.property] at hc

theorem uvSub_exact {p : ℕ} (hp : 0<p) {f : List (Word p)} {ell : ℕ}
    (he : 0<f.length) (a b : UVBlock f ell) :
    uvRead hp f ell (uvSub hp he a b).result=uvRead hp f ell a-uvRead hp f ell b ∧
    (uvSub hp he a b).steps≤ell*(2*uBudgetGates f.length p hp+4*(f.length*p+1)) := by
  have hh : b.val.length≤a.val.length := by rw [b.property,a.property]
  obtain ⟨_,hr,hc⟩ := subtractScaled_exact (uOps hp f) (uOne hp he) b.val a.val hh
  refine ⟨?_,?_⟩
  · change AdjoinRoot.mk _
      (decode (uOps hp f) (subtractScaled (uOps hp f).toGates (uOne hp he) b.val a.val).result)=_
    rw [hr,a.property,b.property,Nat.sub_self]
    change AdjoinRoot.mk _ (decode (uOps hp f) a.val-
      C (uRead hp f (uOne hp he))*(X^0*decode (uOps hp f) b.val))=_
    rw [uOne_read hp he,C_1,pow_zero,one_mul,one_mul,map_sub]
    rfl
  · rwa [b.property] at hc

def uvProduct {p : ℕ} (hp : 0<p) {f : List (Word p)} {ell : ℕ}
    (he : 0<f.length) (hv : 0<ell) : List (UVBlock f ell) → Meter (UVBlock f ell)
  | [] => ⟨uvOne hp he hv,ell*(f.length*p+1)+4⟩
  | a::as =>
    let t := uvProduct hp he hv as
    let m := uvMul hp a t.result
    ⟨m.result,t.steps+m.steps+4⟩

theorem uvProduct_exact {p : ℕ} (hp : 0<p) {f : List (Word p)} {ell : ℕ}
    (he : 0<f.length) (hv : 0<ell) (as : List (UVBlock f ell)) :
    uvRead hp f ell (uvProduct hp he hv as).result=(as.map (uvRead hp f ell)).prod ∧
    (uvProduct hp he hv as).steps ≤ ell*(f.length*p+1)+4+
       as.length*(3432*((ell+1)^2*(f.length+1)^2*(p+1)^2)+4) := by
  induction as with
  | nil => simp [uvProduct]
  | cons a as ih =>
    let t := uvProduct hp he hv as
    obtain ⟨hm,hc⟩ := uvMul_native_bit_cost hp a t.result
    refine ⟨?_,?_⟩
    · change uvRead hp f ell (uvMul hp a t.result).result = _
      rw [hm]
      exact congrArg (uvRead hp f ell a * ·) ih.1
    · change t.steps+(uvMul hp a t.result).steps+4≤_
      rw [List.length_cons,Nat.succ_mul as.length]
      have ht := ih.2
      change t.steps≤_ at ht
      omega

#print axioms constantTape_read
#print axioms uvZero_read
#print axioms uvOne_read
#print axioms uvAdd_exact
#print axioms uvSub_exact
#print axioms uvProduct_exact
end A1R10

