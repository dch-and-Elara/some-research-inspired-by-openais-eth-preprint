import A1R11Moment

/-! Executable powers and shifted-odd inverses in the same native
double quotient as A1. The inverse is the finite Horner recurrence,
not a field inversion or an oracle. -/

namespace A1R12
open A1R10 A1R11 AOracleMachineTime AOracleCoordinates
open AOracleSuccinctNative AOracleSuccinctPhysical V9BitCostInterpolation

def mulCap (e ell p : ℕ) : ℕ := 3432*((ell+1)^2*(e+1)^2*(p+1)^2)

def addCap (e ell p : ℕ) (hp : 0<p) : ℕ :=
  ell*(uBudgetGates e p hp+4*(e*p+1))

def subCap (e ell p : ℕ) (hp : 0<p) : ℕ :=
  ell*(2*uBudgetGates e p hp+4*(e*p+1))

def uvPow {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (x : UVBlock f ell) : ℕ → Meter (UVBlock f ell)
  | 0 => ⟨uvOne hp he hv,uvWidth f.length ell p⟩
  | n+1 =>
    let t := uvPow hp he hv x n
    let q := uvMul hp t.result x
    ⟨q.result,t.steps+q.steps+4⟩

theorem uvPow_exact {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (x : UVBlock f ell) (n : ℕ) :
    uvRead hp f ell (uvPow hp he hv x n).result = uvRead hp f ell x^n ∧
      (uvPow hp he hv x n).steps≤uvWidth f.length ell p+n*(mulCap f.length ell p+4) := by
  induction n with
  | zero => simp [uvPow]
  | succ n ih =>
    let t := uvPow hp he hv x n
    let q := uvMul hp t.result x
    obtain ⟨hr,hc⟩ := uvMul_native_bit_cost hp t.result x
    refine ⟨?_,?_⟩
    · change uvRead hp f ell q.result=_
      rw [show uvRead hp f ell q.result=_ from hr,ih.1,pow_succ]
    · change t.steps+q.steps+4≤uvWidth f.length ell p+(n+1)*(mulCap f.length ell p+4)
      change q.steps≤mulCap f.length ell p at hc
      have ht := ih.2
      change t.steps≤_ at ht
      rw [Nat.succ_mul n]
      omega

/-- The recurrence computes 1+x+...+x^(n-1). Both products and additions
invoke the explicit R10 bit-level machine. -/
def uvCorrection {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (x : UVBlock f ell) : ℕ → Meter (UVBlock f ell)
  | 0 => ⟨uvZero hp f ell,uvWidth f.length ell p⟩
  | n+1 =>
    let t := uvCorrection hp he hv x n
    let q := uvMul hp x t.result
    let v := uvAdd hp (uvOne hp he hv) q.result
    ⟨v.result,t.steps+q.steps+v.steps+uvWidth f.length ell p+4⟩

def correctionCap (e ell p n : ℕ) (hp : 0<p) : ℕ :=
  uvWidth e ell p+n*(mulCap e ell p+addCap e ell p hp+uvWidth e ell p+4)

theorem uvCorrection_exact {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (x : UVBlock f ell) (n : ℕ) :
    uvRead hp f ell (uvCorrection hp he hv x n).result = correction (uvRead hp f ell x) n ∧
      (uvCorrection hp he hv x n).steps≤correctionCap f.length ell p n hp := by
  induction n with
  | zero => simp [uvCorrection,correction,correctionCap]
  | succ n ih =>
    let t := uvCorrection hp he hv x n
    let q := uvMul hp x t.result
    let v := uvAdd hp (uvOne hp he hv) q.result
    obtain ⟨hq,hqc⟩ := uvMul_native_bit_cost hp x t.result
    obtain ⟨hv',hvc⟩ := uvAdd_exact hp (uvOne hp he hv) q.result
    refine ⟨?_,?_⟩
    · change uvRead hp f ell v.result=_
      rw [show uvRead hp f ell v.result=_ from hv',uvOne_read,hq,ih.1,correction]
    · change t.steps+q.steps+v.steps+uvWidth f.length ell p+4≤_
      change q.steps≤mulCap f.length ell p at hqc
      change v.steps≤addCap f.length ell p hp at hvc
      have ht := ih.2
      change t.steps≤_ at ht
      unfold correctionCap at ht ⊢
      rw [Nat.succ_mul n]
      omega

def uvOddInverse {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (x : UVBlock f ell) : Meter (UVBlock f ell) :=
  let y := uvSub hp he (uvOne hp he hv) x
  let k := uvCorrection hp he hv y.result p
  ⟨k.result,y.steps+k.steps+uvWidth f.length ell p+4⟩

def oddCap (e ell p : ℕ) (hp : 0<p) : ℕ :=
  subCap e ell p hp+correctionCap e ell p p hp+uvWidth e ell p+4

theorem uvOddInverse_exact {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (x : UVBlock f ell) :
    uvRead hp f ell (uvOddInverse hp he hv x).result = oddInverse p (uvRead hp f ell x) ∧
      (uvOddInverse hp he hv x).steps≤oddCap f.length ell p hp := by
  let y := uvSub hp he (uvOne hp he hv) x
  obtain ⟨hy,hyc⟩ := uvSub_exact hp he (uvOne hp he hv) x
  obtain ⟨hr,hc⟩ := uvCorrection_exact hp he hv y.result p
  refine ⟨?_,?_⟩
  · change uvRead hp f ell (uvCorrection hp he hv y.result p).result=_
    rw [hr,show uvRead hp f ell y.result=_ from hy,uvOne_read]
    rfl
  · exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add hyc hc) _) _

theorem uvOddInverse_is_inverse {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (x : UVBlock f ell)
    (hx : ∃ a : Truncated (Modulus p hp f) ell, uvRead hp f ell x=1+2*a) :
    uvRead hp f ell x * uvRead hp f ell (uvOddInverse hp he hv x).result=1 := by
  rw [(uvOddInverse_exact hp he hv x).1]
  exact oddInverse_correct p (double_quotient_two_nilpotent (Modulus p hp f) ell) _ hx

#print axioms uvPow_exact
#print axioms uvCorrection_exact
#print axioms uvOddInverse_exact
#print axioms uvOddInverse_is_inverse
end A1R12
