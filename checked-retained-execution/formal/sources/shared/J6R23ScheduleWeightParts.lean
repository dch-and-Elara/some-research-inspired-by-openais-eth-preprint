import A1R12Combine
import HermiteLossDenominator
import P1DyadicGridBridge

/-! Build the odd part and the two-adic exponent of one real signed
grid factor raised to an actual taper order. The huge signed power
does not become a tape value: only its odd residue, and the explicit
binary-sized valuation counter, are written. -/
namespace J6R23ScheduleWeight
open scoped Polynomial
open A1R10 A1R11 A1R12 AOracleCoordinates AOracleMachineTime
open P1DyadicGrid P1DyadicGridBridge HermiteLoss AOracleSuccinctNative

structure Part {p : ℕ} (fw : List (Word p)) (ell : ℕ) where
  two : ℕ
  odd : UVBlock fw ell

variable {p ell : ℕ} {fw : List (Word p)}

def powerPart (hp : 0<p) (he : 0<fw.length) (hv : 0<ell) (w k : ℕ) (z : ℤ) :
    Meter (Part fw ell) :=
  let d := dyadicInt hp w z
  let v := powM hp he hv (scalarM hp he hv d.result.2) k
  ⟨⟨k*d.result.1,v.result⟩,d.steps+v.steps+8*(w+k+3)^2+6⟩

def partCap (e ell p w k : ℕ) : ℕ :=
  dyadicCap p w+2*uvWidth e ell p+k*(mulCap e ell p+4)+8*(w+k+3)^2+8

theorem powerPart_exact (hp : 0<p) (he : 0<fw.length) (hv : 0<ell) (w k : ℕ) (z : ℤ)
    (h : z.natAbs<2^w) :
    let v := powerPart hp he hv w k z
    v.result.two=k*padicValInt 2 z ∧
      uvRead hp fw ell v.result.odd=((oddWord z ^ k:ℤ):Truncated (Modulus p hp fw) ell) ∧
      v.steps≤partCap fw.length ell p w k := by
  let d := dyadicInt hp w z
  let v := powM hp he hv (scalarM hp he hv d.result.2) k
  obtain ⟨hd,hr,hc⟩ := dyadicInt_exact hp w z h
  have he1 : d.result.1=padicValInt 2 z := hd
  have he2 : wordRead d.result.2=(oddWord z:ZMod (2^p)) := hr
  have hd' : d.steps≤dyadicCap p w := hc
  have hv' : v.steps≤uvWidth fw.length ell p+
      (uvWidth fw.length ell p+k*(mulCap fw.length ell p+4))+2 := powM_cost hp he hv _ k
  refine ⟨congrArg (k*·) he1,?_,?_⟩
  · change uvRead hp fw ell v.result=_
    simp only [v,powM_read,scalarM_read,he2,map_intCast,Int.cast_pow]
  · change d.steps+v.steps+8*(w+k+3)^2+6≤_
    unfold partCap
    omega

theorem factor_power_as_odd (x : ℤ) (hx : x≠0) (k : ℕ) :
    x^k=pow₂ (k*padicValInt 2 x)*(oddWord x)^k ∧ Odd ((oddWord x)^k) := by
  obtain ⟨odd,h⟩ := oddWord_factor hx
  refine ⟨?_,odd.pow⟩
  conv_lhs => rw [h,mul_pow]
  unfold pow₂
  rw [←pow_mul,Nat.mul_comm k]

theorem odd_factor_recovers_word {x y : ℤ} {v : ℕ}
    (h : x=pow₂ v*y) (odd : Odd y) :
    level x=v ∧ oddWord x=y := by
  have hv : padicValInt 2 x=v := h.symm ▸ valuation_pow₂_mul_odd v odd
  refine ⟨hv,?_⟩
  unfold oddWord
  rw [hv,h,Int.mul_ediv_cancel_left _ (pow₂_pos _).ne']

theorem grid_neg_width {a : ℕ} {q : ℤ} (hq : q∈grid a) : (-q).natAbs<2^(a+1) := by
  simpa only [zero_sub] using diff_width (zero_mem_grid a) hq

#print axioms powerPart_exact
#print axioms factor_power_as_odd
#print axioms odd_factor_recovers_word
#print axioms grid_neg_width
end J6R23ScheduleWeight

