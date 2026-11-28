import A1R12Combine
import J6R18ChildWriteHost
import Mathlib.FieldTheory.Finite.Basic

/-! Inverting a residue-distinct scalar probe difference without a
field/unit oracle. The pre-inverse is computed by binary powering in
the original finite U/V box. A length-p geometric correction then
uses the proved nilpotence of 2, never division in a dyadic quotient.
The operand word is charged separately above its native bit kernel. -/
namespace J6R22Active
open scoped Polynomial
open Polynomial AOracleCoordinates AOracleMachineTime A1R10 A1R11 A1R12
open AOracleSuccinctNative AOracleSuccinctPhysical J6R18ChildWrite

noncomputable def boxTransport {p ell : ℕ} {A B : (ZMod (2^p))[X]} (h : A=B) :
    Truncated A ell →+* Truncated B ell := by
  subst B
  exact RingHom.id _

theorem boxTransport_cast {p ell : ℕ} {A B : (ZMod (2^p))[X]} (h : A=B)
    (x : Truncated A ell) : boxTransport h x=castBox h x := by
  subst B
  rfl

theorem boxTransport_injective {p ell : ℕ} {A B : (ZMod (2^p))[X]} (h : A=B) :
    Function.Injective (boxTransport (ell:=ell) h) := by
  subst B
  exact fun _ _ h=>h

theorem boxTransport_surjective {p ell : ℕ} {A B : (ZMod (2^p))[X]} (h : A=B) :
    Function.Surjective (boxTransport (ell:=ell) h) := by
  subst B
  exact fun a=>⟨a,rfl⟩

section Unit
variable {p ell : ℕ} {fw : List (Word p)}

def stored (x : UVBlock fw ell) : Meter (UVBlock fw ell) :=
  ⟨x,uvWidth fw.length ell p⟩

@[simp] theorem stored_result (x : UVBlock fw ell) : (stored x).result=x := rfl

def subM (hp : 0<p) (he : 0<fw.length)
    (x y : Meter (UVBlock fw ell)) : Meter (UVBlock fw ell) :=
  let z := uvSub hp he x.result y.result
  ⟨z.result,x.steps+y.steps+z.steps+2⟩

@[simp] theorem subM_value (hp : 0<p) (he : 0<fw.length)
    (x y : Meter (UVBlock fw ell)) :
    uvRead hp fw ell (subM hp he x y).result=
      uvRead hp fw ell x.result-uvRead hp fw ell y.result :=
  (uvSub_exact hp he x.result y.result).1

theorem subM_steps (hp : 0<p) (he : 0<fw.length)
    (x y : Meter (UVBlock fw ell)) :
    (subM hp he x y).steps≤x.steps+y.steps+subCap fw.length ell p hp+2 :=
  Nat.add_le_add_right (Nat.add_le_add_left (uvSub_exact hp he x.result y.result).2 _) _

/-- Seed of exponent 2^(n+1)-2, with n actual square/multiply steps.
The previous result is computed once and copied as finite bits. -/
def unitSeed (hp : 0<p) (he : 0<fw.length) (hv : 0<ell)
    (x : UVBlock fw ell) : ℕ→Meter (UVBlock fw ell)
  | 0 => oneM hp he hv
  | n+1 =>
    let y := unitSeed hp he hv x n
    let z := mulM hp (stored y.result) (stored y.result)
    let q := mulM hp (stored x) (stored x)
    padCost (mulM hp z q) (y.steps+4)

def seedStride (e ell p : ℕ) : ℕ :=
  4*uvWidth e ell p+3*(mulCap e ell p+2)+4

theorem unitSeed_exact (hp : 0<p) (he : 0<fw.length) (hv : 0<ell)
    (x : UVBlock fw ell) (n : ℕ) :
    let y := unitSeed hp he hv x n
    uvRead hp fw ell y.result=uvRead hp fw ell x^(2^(n+1)-2) ∧
      y.steps≤uvWidth fw.length ell p+n*seedStride fw.length ell p := by
  dsimp only
  induction n with
  | zero => simp [unitSeed,oneM]
  | succ n ih =>
    let y := unitSeed hp he hv x n
    let z := mulM hp (stored y.result) (stored y.result)
    let q := mulM hp (stored x) (stored x)
    have hpow : 2^(n+1+1)-2=(2^(n+1)-2)+(2^(n+1)-2)+(1+1) := by
      have h : 2≤(2:ℕ)^(n+1) := Nat.le_pow (by omega)
      rw [pow_succ _ (n+1)]
      omega
    constructor
    · change uvRead hp fw ell (mulM hp z q).result=_
      simp only [z,q,mulM_read,stored_result,show y=unitSeed hp he hv x n from rfl,ih.1]
      rw [hpow]
      simp only [pow_add,pow_one]
    · have hz := mulM_cost hp (stored y.result) (stored y.result)
      have hq := mulM_cost hp (stored x) (stored x)
      have hm := mulM_cost hp z q
      change z.steps≤uvWidth fw.length ell p+uvWidth fw.length ell p+mulCap fw.length ell p+2 at hz
      change q.steps≤uvWidth fw.length ell p+uvWidth fw.length ell p+mulCap fw.length ell p+2 at hq
      have hi := ih.2
      change y.steps≤_ at hi
      change (mulM hp z q).steps+(y.steps+4)≤_
      rw [Nat.succ_mul n]
      unfold seedStride at hi ⊢
      omega

/-- Compute one inverse in the full finite U/V extension, from one
encoded scalar whose native mod-2 image is nonzero. -/
def unitInverse (hp : 0<p) (he : 0<fw.length) (hv : 0<ell)
    (x : Meter (UVBlock fw ell)) : Meter (UVBlock fw ell) :=
  let y := unitSeed hp he hv x.result (fw.length-1)
  let z := mulM hp (stored x.result) (stored y.result)
  let w := invM hp he hv z
  padCost (mulM hp (stored y.result) w) (x.steps+y.steps+4)

def inverseFee (e ell p : ℕ) (hp : 0<p) : ℕ :=
  uvWidth e ell p+(e-1)*seedStride e ell p+
    3*uvWidth e ell p+2*(mulCap e ell p+2)+oddCap e ell p hp+6

theorem unit_inverse_cost (hp : 0<p) (he : 0<fw.length) (hv : 0<ell)
    (x : Meter (UVBlock fw ell)) :
    (unitInverse hp he hv x).steps≤x.steps+inverseFee fw.length ell p hp := by
  let y := unitSeed hp he hv x.result (fw.length-1)
  let z := mulM hp (stored x.result) (stored y.result)
  let w := invM hp he hv z
  have hy := (unitSeed_exact hp he hv x.result (fw.length-1)).2
  have hz := mulM_cost hp (stored x.result) (stored y.result)
  have hw := invM_cost hp he hv z
  have hfin := mulM_cost hp (stored y.result) w
  change y.steps≤uvWidth fw.length ell p+(fw.length-1)*seedStride fw.length ell p at hy
  change z.steps≤uvWidth fw.length ell p+uvWidth fw.length ell p+mulCap fw.length ell p+2 at hz
  change w.steps≤z.steps+oddCap fw.length ell p hp+2 at hw
  change (mulM hp (stored y.result) w).steps≤uvWidth fw.length ell p+w.steps+mulCap fw.length ell p+2 at hfin
  change (mulM hp (stored y.result) w).steps+(x.steps+y.steps+4)≤_
  unfold inverseFee
  omega

theorem unit_inverse_value (hp : 0<p) (he : 0<fw.length) (hv : 0<ell)
    (x : Meter (UVBlock fw ell)) (h :
      ∃ b : Truncated (Modulus p hp fw) ell,uvRead hp fw ell x.result^(2^fw.length-1)=1+2*b) :
    uvRead hp fw ell x.result*uvRead hp fw ell (unitInverse hp he hv x).result=1 := by
  let y := unitSeed hp he hv x.result (fw.length-1)
  let z := mulM hp (stored x.result) (stored y.result)
  let w := invM hp he hv z
  have hE : fw.length-1+1=fw.length := by omega
  have hT : 2≤(2:ℕ)^fw.length := Nat.le_pow (by omega)
  have hS : 2^fw.length-1=2^fw.length-2+1 := by omega
  have hY : uvRead hp fw ell y.result=uvRead hp fw ell x.result^(2^fw.length-2) := by
    simpa only [hE] using (unitSeed_exact hp he hv x.result (fw.length-1)).1
  have hZ : uvRead hp fw ell z.result=uvRead hp fw ell x.result^(2^fw.length-1) := by
    simp only [z,mulM_read,stored_result,hY,hS,pow_succ,mul_comm]
  have hQ : uvRead hp fw ell z.result*uvRead hp fw ell w.result=1 := by
    unfold w
    rw [invM_read]
    exact oddInverse_correct p (double_quotient_two_nilpotent (Modulus p hp fw) ell) _
      (hZ.symm ▸ h)
  simpa only [unitInverse,y,z,w,padCost,mulM_read,stored_result,←mul_assoc] using hQ
end Unit

section Native
open NativeProbeRing

theorem fermat_residue (f : ℤ[X]) (hf : f.Monic)
    [Fact (Irreducible (residuePoly f))]
    (x : Residue f) (hx : x≠0) : x^(2^f.natDegree-1)=1 := by
  classical
  let B := (AdjoinRoot.powerBasis (hf.map (Int.castRingHom (ZMod 2))).ne_zero)
  let rep : Residue f ≃ (Fin B.dim → ZMod 2) := B.basis.equivFun.toEquiv
  letI : Fintype (Residue f) := Fintype.ofEquiv _ rep.symm
  have he : B.dim=f.natDegree := (AdjoinRoot.powerBasis_dim (hf.map (Int.castRingHom (ZMod 2))).ne_zero).trans (hf.natDegree_map _)
  have hcard : Fintype.card (Residue f)=2^f.natDegree := by
    rw [Fintype.card_congr rep,Fintype.card_fun,Fintype.card_fin,ZMod.card,he]
  simpa only [hcard] using FiniteField.pow_card_sub_one_eq_one x hx

theorem native_power_is_one_plus_two {p ell : ℕ} (hp : 0<p)
    (f : ℤ[X]) (hf : f.Monic) [Fact (Irreducible (residuePoly f))]
    (x : Scalar p f) (hx : residueMap p hp f x≠0) :
    ∃ b : J6R9Recursive.Box f ell p,
      (J6ActiveInterpolation.scalarIn p f ell x)^(2^f.natDegree-1)=1+2*b := by
  let E := 2^f.natDegree-1
  have hz : residueMap p hp f (x^E-1)=0 := by
    rw [map_sub,map_pow,map_one,fermat_residue f hf _ hx,sub_self]
  obtain ⟨b,hb⟩ := scalar_even p hp f hf (x^E-1) hz
  have hbx : x^E=1+2*b := by
    calc
      _=(x^E-1)+1 := by ring
      _=_ := by rw [hb,add_comm]
  exact ⟨J6ActiveInterpolation.scalarIn p f ell b,by
    rw [←map_pow,hbx,map_add,map_one,map_mul,map_ofNat]⟩

theorem inverse_actual_scalar {p ell : ℕ} (hp : 0<p) {fw : List (Word p)}
    (he : 0<fw.length) (hv : 0<ell) {f : ℤ[X]} (hf : f.Monic)
    [Fact (Irreducible (residuePoly f))]
    (hF : Modulus p hp fw=liftPoly p f) (hD : fw.length=f.natDegree)
    (x : Meter (UVBlock fw ell)) (a : Scalar p f) (ha : residueMap p hp f a≠0)
    (read : boxTransport hF (uvRead hp fw ell x.result)=J6ActiveInterpolation.scalarIn p f ell a) :
    J6ActiveInterpolation.scalarIn p f ell a*
      boxTransport hF (uvRead hp fw ell (unitInverse hp he hv x).result)=1 ∧
    (unitInverse hp he hv x).steps≤x.steps+inverseFee fw.length ell p hp := by
  refine ⟨?_,unit_inverse_cost hp he hv x⟩
  have hU : ∃ b : Truncated (Modulus p hp fw) ell,
      uvRead hp fw ell x.result^(2^fw.length-1)=1+2*b := by
    obtain ⟨b,hb⟩ := native_power_is_one_plus_two (ell:=ell) hp f hf a ha
    obtain ⟨c,rfl⟩ := boxTransport_surjective hF b
    refine ⟨c,boxTransport_injective hF ?_⟩
    simpa only [map_pow,map_add,map_one,map_mul,map_ofNat,read,hD] using hb
  trans boxTransport hF (uvRead hp fw ell x.result*
      uvRead hp fw ell (unitInverse hp he hv x).result)
  · rw [map_mul,read]
  · rw [unit_inverse_value hp he hv x hU,map_one]
end Native

#print axioms boxTransport_cast
#print axioms subM_steps
#print axioms unitSeed_exact
#print axioms unit_inverse_cost
#print axioms unit_inverse_value
#print axioms fermat_residue
#print axioms native_power_is_one_plus_two
#print axioms inverse_actual_scalar
end J6R22Active



