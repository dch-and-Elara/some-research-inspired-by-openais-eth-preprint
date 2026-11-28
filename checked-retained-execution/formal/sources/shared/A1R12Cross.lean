import A1R12Local

/-! Literal native crossing coefficient generation, including the
signed distance, its valuation, the two grid products, the shifted-odd
inverse and exponent b+1. Equality also holds for off-target cells
where the formula is still defined but its p-step recurrence need not
be used as a unit inverse. -/

namespace A1R12
open A1R10 A1R11 AOracleMachineTime AOracleCoordinates
open P1DyadicGrid P1DyadicGridBridge AOracleSuccinctNative AOracleSuccinctPhysical

def crossScaleM {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (z : UVBlock f ell) (a i b : ℕ) (d : ℤ) : Meter (UVBlock f ell) :=
  let q := dyadicInt hp (a+i+2) d
  padCost (scaleM hp he hv z (crossingExponent a i b q.result.1))
    (q.steps+16*(a+i+b+4)^3)

def crossScaleCap (e ell p a i b : ℕ) : ℕ :=
  scaleCap e ell p (a+1+b+(b+1)*i)+dyadicCap p (a+i+2)+16*(a+i+b+4)^3

theorem crossScaleM_exact {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (z : UVBlock f ell) (a i b : ℕ) (d : ℤ)
    (hd : d.natAbs<2^(a+i+2)) :
    uvRead hp f ell (crossScaleM hp he hv z a i b d).result=
      (2:Truncated (Modulus p hp f) ell)^(crossingExponent a i b (padicValInt 2 d))*uvRead hp f ell z ∧
    (crossScaleM hp he hv z a i b d).steps≤crossScaleCap f.length ell p a i b := by
  let q := dyadicInt hp (a+i+2) d
  obtain ⟨h1,_,h2⟩ := dyadicInt_exact hp (a+i+2) d hd
  have h : crossingExponent a i b q.result.1≤a+1+b+(b+1)*i := by
    unfold crossingExponent
    have hsub := Nat.mul_le_mul_left (b+1) (Nat.sub_le i q.result.1)
    omega
  refine ⟨?_,?_⟩
  · change uvRead hp f ell (scaleM hp he hv z (crossingExponent a i b q.result.1)).result=_
    change q.result.1=_ at h1
    rw [scaleM_read,h1]
  · change (scaleM hp he hv z (crossingExponent a i b q.result.1)).steps+
      (q.steps+16*(a+i+b+4)^3)≤_
    have h3 := scaleM_cost hp he hv z h
    change q.steps≤_ at h2
    unfold crossScaleCap
    omega

def crossPowerM {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (z : UVBlock f ell) (a i b : ℕ) (d : ℤ) : Meter (UVBlock f ell) :=
  powM hp he hv (invM hp he hv (shiftM hp he hv z a (a+i+2) d)) (b+1)

def crossPowerCap (e ell p a i b : ℕ) (hp : 0<p) : ℕ :=
  shiftCap e ell p a (a+i+2) hp+oddCap e ell p hp+2+
    (uvWidth e ell p+(b+1)*(mulCap e ell p+4))+2

theorem crossPowerM_exact {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (z : UVBlock f ell) (a i b : ℕ) (d : ℤ)
    (hd : d.natAbs<2^(a+i+2)) :
    uvRead hp f ell (crossPowerM hp he hv z a i b d).result=
      (oddInverse p (shiftWord (oddWord d) (a+1-padicValInt 2 d) (uvRead hp f ell z)))^(b+1) ∧
    (crossPowerM hp he hv z a i b d).steps≤crossPowerCap f.length ell p a i b hp := by
  obtain ⟨hs,hsc⟩ := shiftM_exact hp he hv z a (a+i+2) d hd
  refine ⟨?_,?_⟩
  · rw [crossPowerM,powM_read,invM_read,hs]
  · have hi := invM_cost hp he hv (shiftM hp he hv z a (a+i+2) d)
    have h := powM_cost hp he hv (invM hp he hv (shiftM hp he hv z a (a+i+2) d)) (b+1)
    exact h.trans (by unfold crossPowerCap; omega)

def crossingGen {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (z : UVBlock f ell) (a i b : ℕ)
    (t : ℤ) (x u : ℕ) : Meter (UVBlock f ell) :=
  let d := crossingInt t x u
  let D := mulM hp (oddProdM hp he hv a t) (derivativeInverseM hp he hv a)
  let s := crossScaleM hp he hv z a i b d
  let P := ratioProdM hp he hv z a t
  let J := crossPowerM hp he hv z a i b d
  padCost (mulM hp (mulM hp (mulM hp D s) P) J) (8*(a+i+4)^2+4)

def crossingGenCap (e ell p a i b : ℕ) (hp : 0<p) : ℕ :=
  oddProdCap e ell p a+derivativeInverseCap e ell p a hp+crossScaleCap e ell p a i b+
    ratioProdCap e ell p a hp+crossPowerCap e ell p a i b hp+4*(mulCap e ell p+2)+8*(a+i+4)^2+4

theorem crossingGen_exact {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (z : UVBlock f ell) (a i b : ℕ) (t : ℤ)
    (x u : ℕ) (ht : t∈grid a) (hx : x<2^a) (hu : u<2^(i+1)) :
    uvRead hp f ell (crossingGen hp he hv z a i b t x u).result=
      crossCell p a i b t x u (uvRead hp f ell z) ∧
    (crossingGen hp he hv z a i b t x u).steps≤crossingGenCap f.length ell p a i b hp := by
  let d := crossingInt t x u
  have hD : d.natAbs<2^(a+i+2) := cross_width ht hx hu
  let o := oddProdM hp he hv a t
  let f0 := derivativeInverseM hp he hv a
  let D := mulM hp o f0
  let s := crossScaleM hp he hv z a i b d
  let P := ratioProdM hp he hv z a t
  let J := crossPowerM hp he hv z a i b d
  obtain ⟨ho,hoc⟩ := oddProdM_exact hp he hv a t ht
  obtain ⟨hf,hfc⟩ := derivativeInverseM_exact hp he hv a
  obtain ⟨hs,hsc⟩ := crossScaleM_exact hp he hv z a i b d hD
  obtain ⟨hP,hPc⟩ := ratioProdM_exact hp he hv z a t ht
  obtain ⟨hJ,hJc⟩ := crossPowerM_exact hp he hv z a i b d hD
  refine ⟨?_,?_⟩
  · simp only [crossingGen,padCost,mulM_read,ho,hf,hs,hP,hJ,crossCell,d,mul_assoc]
  · change (mulM hp (mulM hp (mulM hp D s) P) J).steps+(8*(a+i+4)^2+4)≤_
    have h0 := mulM_cost hp o f0
    have h1 := mulM_cost hp D s
    have h2 := mulM_cost hp (mulM hp D s) P
    have h3 := mulM_cost hp (mulM hp (mulM hp D s) P) J
    change o.steps≤_ at hoc
    change f0.steps≤_ at hfc
    change s.steps≤_ at hsc
    change P.steps≤_ at hPc
    change J.steps≤_ at hJc
    change D.steps≤_ at h0
    unfold crossingGenCap
    omega

#print axioms crossScaleM_exact
#print axioms crossPowerM_exact
#print axioms crossingGen_exact
end A1R12

