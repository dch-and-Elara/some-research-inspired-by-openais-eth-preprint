import A1R12GridProduct

/-! Full local Cauchy cell from source coordinates, including the
diagonal and off-diagonal branches and the odd derivative denominator. -/

open scoped BigOperators
namespace A1R12
open A1R10 A1R11 AOracleCoordinates AOracleMachineTime
open P1DyadicGrid AOracleSuccinctNative AOracleSuccinctKernel

def derivativeInverseM {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (a : ℕ) : Meter (UVBlock f ell) :=
  invM hp he hv (oddProdM hp he hv a 0)

def derivativeInverseCap (e ell p a : ℕ) (hp : 0<p) : ℕ :=
  oddProdCap e ell p a+oddCap e ell p hp+2

theorem derivativeInverseM_exact {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (a : ℕ) :
    uvRead hp f ell (derivativeInverseM hp he hv a).result=
       oddInverse p (oddDerivative a:Truncated (Modulus p hp f) ell) ∧
    (derivativeInverseM hp he hv a).steps≤derivativeInverseCap f.length ell p a hp := by
  obtain ⟨hr,hc⟩ := oddProdM_exact hp he hv a 0 (zero_mem_grid a)
  refine ⟨?_,?_⟩
  · rw [derivativeInverseM,invM_read,hr,oddDerivative_eq_parts]
  · have h := invM_cost hp he hv (oddProdM hp he hv a 0)
    exact h.trans (Nat.add_le_add_right (Nat.add_le_add_right hc _) _)

def localHeadM {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (z : UVBlock f ell) (a : ℕ) (t k : ℤ) : Meter (UVBlock f ell) :=
  let y := normProdM hp he hv z a t k
  let h := if k=t then y else
    let u := dyadicInt hp (a+1) (t-k)
    padCost (mulM hp (scaleM hp he hv z (a+1-u.result.1)) y) u.steps
  padCost h (8*(a+3)^2+4)

def localHeadCap (e ell p a : ℕ) (hp : 0<p) : ℕ :=
  normProdCap e ell p a hp+scaleCap e ell p (a+1)+mulCap e ell p+2+
    dyadicCap p (a+1)+8*(a+3)^2+4

theorem localHeadM_exact {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (z : UVBlock f ell) (a : ℕ) (t k : ℤ)
    (ht : t∈grid a) (hk : k∈grid a) :
    uvRead hp f ell (localHeadM hp he hv z a t k).result=
      (if k=t then (∏ q∈(grid a).erase t,normFactor a t q (uvRead hp f ell z))
       else (2:Truncated (Modulus p hp f) ell)^(a+1-padicValInt 2 (t-k))*uvRead hp f ell z*
        (∏ q∈((grid a).erase t).erase k,normFactor a t q (uvRead hp f ell z))) ∧
    (localHeadM hp he hv z a t k).steps≤localHeadCap f.length ell p a hp := by
  let g := normProdM hp he hv z a t k
  obtain ⟨hr,hc⟩ := normProdM_exact hp he hv z a t k ht
  change uvRead hp f ell g.result=_ at hr
  change g.steps≤_ at hc
  by_cases h : k=t
  · subst k
    rw [erase_twice] at hr
    constructor
    · simpa only [localHeadM,if_true,padCost] using hr
    · unfold localHeadM
      dsimp only
      rw [if_pos rfl]
      change g.steps+_≤_
      unfold localHeadCap
      omega
  · let u := dyadicInt hp (a+1) (t-k)
    let s := scaleM hp he hv z (a+1-u.result.1)
    obtain ⟨hu,_,huc⟩ := dyadicInt_exact hp (a+1) (t-k) (diff_width ht hk)
    have hs := scaleM_cost hp he hv z (Nat.sub_le (a+1) u.result.1)
    have hm := mulM_cost hp s g
    change s.steps≤_ at hs
    change u.steps≤_ at huc
    unfold localHeadM
    dsimp only
    simp only [h,if_false]
    constructor
    · change uvRead hp f ell (mulM hp s g).result=_
      rw [mulM_read,hr,show uvRead hp f ell s.result=_ from scaleM_read hp he hv z _,hu]
    · change (mulM hp s g).steps+u.steps+(8*(a+3)^2+4)≤_
      unfold localHeadCap
      omega

def modularGen {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (z : UVBlock f ell) (a : ℕ) (t k : ℤ) :
    Meter (UVBlock f ell) :=
  mulM hp (localHeadM hp he hv z a t k) (derivativeInverseM hp he hv a)

def modularGenCap (e ell p a : ℕ) (hp : 0<p) : ℕ :=
  localHeadCap e ell p a hp+derivativeInverseCap e ell p a hp+mulCap e ell p+2

theorem modularGen_exact {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (z : UVBlock f ell) (a : ℕ) (t k : ℤ)
    (ht : t∈grid a) (hk : k∈grid a) :
    uvRead hp f ell (modularGen hp he hv z a t k).result=modular p a t k (uvRead hp f ell z) ∧
    (modularGen hp he hv z a t k).steps≤modularGenCap f.length ell p a hp := by
  obtain ⟨hu,huc⟩ := localHeadM_exact hp he hv z a t k ht hk
  obtain ⟨hd,hdc⟩ := derivativeInverseM_exact hp he hv a
  refine ⟨?_,?_⟩
  · rw [modularGen,mulM_read,hu,hd,modular]
    split <;> simp [*]
  · exact (mulM_cost hp _ _).trans
      (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add huc hdc) _) _)

#print axioms derivativeInverseM_exact
#print axioms localHeadM_exact
#print axioms modularGen_exact
end A1R12

