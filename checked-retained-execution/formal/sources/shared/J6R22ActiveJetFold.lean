import J6R22ActiveJet
import J6R22ActiveGroups

/-! Paid sequential construction/composition of dense Taylor tapes.
Each list pass charges its actual coefficient word callbacks plus an
explicit polynomial copy/arithmetic overhead. No high-degree polynomial
or pointer-indexed table is read for free. -/
namespace J6R22Active
open scoped Polynomial
open Polynomial A1R10 A1R11 A1R12 AOracleMachineTime

variable {p ell : ℕ} {fw : List (Word p)}

def jetConst (hp : 0<p) (he : 0<fw.length) {k : ℕ} (hk : 0<k) (x : UVBlock fw ell) :
    JetTape fw ell k :=
  ⟨constantTape (jetGates hp he ell) k x,constantTape_len _ _ hk _⟩

theorem jetConst_exact (hp : 0<p) (he : 0<fw.length) {k : ℕ} (hk : 0<k)
    (x : UVBlock fw ell) :
    jetRead hp he (jetConst hp he hk x)=AdjoinRoot.mk (X^k) (C (uvRead hp fw ell x)) := by
  let o := jetOps hp he ell
  change AdjoinRoot.mk (X^k) (decode o (constantTape o.toGates k x))=_
  rw [constantTape_read]
  rfl

def jetX (hp : 0<p) (he : 0<fw.length) (hv : 0<ell) (k : ℕ) : JetTape fw ell k :=
  if h : 2≤k then
    ⟨zeros (jetGates hp he ell) (k-2)++[uvOne hp he hv,uvZero hp fw ell],by simp; omega⟩
  else jetZero hp he k

theorem jetX_exact (hp : 0<p) (he : 0<fw.length) (hv : 0<ell) (k : ℕ) (hk : 0<k) :
    jetRead hp he (jetX hp he hv k)=AdjoinRoot.mk (X^k) X := by
  unfold jetX
  split
  · let o := jetOps hp he ell
    change AdjoinRoot.mk _ (decode o (zeros o.toGates (k-2)++
      [uvOne hp he hv,uvZero hp fw ell]))=_
    rw [decode_append,decode_zeros,mul_zero,zero_add]
    change AdjoinRoot.mk (X^k) (monomial 1 (uvRead hp fw ell (uvOne hp he hv))+
      (monomial 0 (uvRead hp fw ell (uvZero hp fw ell))+0))=_
    simp [uvOne_read hp he hv,monomial_one_right_eq_X_pow]
  · rename_i h
    have h1 : k=1 := by omega
    subst k
    rw [jetZero_exact,pow_one,AdjoinRoot.mk_self]

def tapeFee (e ell p k : ℕ) : ℕ := k*(jetEntryWidth e ell p+1)+2

def paidJetProd {A : Type*} (hp : 0<p) (he : 0<fw.length)
    (hv : 0<ell) {k : ℕ} (hk : 0<k) (f : A→Meter (JetTape fw ell k)) :
    List A → Meter (JetTape fw ell k)
  | [] => ⟨jetOne hp he hv k hk,tapeFee fw.length ell p k⟩
  | a::as =>
    let w := f a
    let q := paidJetProd hp he hv hk f as
    let z := jetMult hp he w.result q.result
    ⟨z.result,w.steps+q.steps+z.steps+2⟩

theorem paidJetProd_exact {A : Type*} (hp : 0<p) (he : 0<fw.length) (hv : 0<ell)
    {k : ℕ} (hk : 0<k) (f : A→Meter (JetTape fw ell k)) (as : List A) :
    let q := paidJetProd hp he hv hk f as
    jetRead hp he q.result=(as.map (fun a=>jetRead hp he (f a).result)).prod ∧
    q.steps≤bill f as+tapeFee fw.length ell p k+as.length*(jetMulFee fw.length ell p k hp+2) := by
  dsimp only
  induction as with
  | nil => simp [paidJetProd,jetOne_exact,bill]
  | cons a as ih =>
    let w := f a
    let q := paidJetProd hp he hv hk f as
    let z := jetMult hp he w.result q.result
    have h1 : jetRead hp he q.result=(as.map (fun a=>jetRead hp he (f a).result)).prod := ih.1
    have h2 : q.steps≤_ := ih.2
    have hz := jetMult_exact hp he w.result q.result
    have h3 : z.steps≤_ := hz.2
    change jetRead hp he z.result=_ ∧ w.steps+q.steps+z.steps+2≤_
    constructor
    · rw [hz.1,h1]
      rfl
    · rw [List.length_cons,Nat.succ_mul as.length]
      change w.steps+q.steps+z.steps+2≤w.steps+bill f as+tapeFee fw.length ell p k+_
      omega

def paidJetSum {A : Type*} (hp : 0<p) (he : 0<fw.length)
    {k : ℕ} (f : A→Meter (JetTape fw ell k)) : List A→Meter (JetTape fw ell k)
  | [] => ⟨jetZero hp he k,tapeFee fw.length ell p k⟩
  | a::as =>
    let w := f a
    let q := paidJetSum hp he f as
    let z := jetAdd hp he w.result q.result
    ⟨z.result,w.steps+q.steps+z.steps+2⟩

theorem paidJetSum_exact {A : Type*} (hp : 0<p) (he : 0<fw.length)
    {k : ℕ} (f : A→Meter (JetTape fw ell k)) (as : List A) :
    let q := paidJetSum hp he f as
    jetRead hp he q.result=(as.map (fun a=>jetRead hp he (f a).result)).sum ∧
    q.steps≤bill f as+tapeFee fw.length ell p k+as.length*(jetAddFee fw.length ell p k hp+2) := by
  dsimp only
  induction as with
  | nil => simp [paidJetSum,jetZero_exact,bill]
  | cons a as ih =>
    let w := f a
    let q := paidJetSum hp he f as
    let z := jetAdd hp he w.result q.result
    have h1 : jetRead hp he q.result=(as.map (fun a=>jetRead hp he (f a).result)).sum := ih.1
    have h2 : q.steps≤_ := ih.2
    have hz := jetAdd_exact hp he w.result q.result
    have h3 : z.steps≤_ := hz.2
    change jetRead hp he z.result=_ ∧ w.steps+q.steps+z.steps+2≤_
    constructor
    · rw [hz.1,h1]
      rfl
    · rw [List.length_cons,Nat.succ_mul as.length]
      change w.steps+q.steps+z.steps+2≤w.steps+bill f as+tapeFee fw.length ell p k+_
      omega

#print axioms jetConst_exact
#print axioms jetX_exact
#print axioms paidJetProd_exact
#print axioms paidJetSum_exact
end J6R22Active

