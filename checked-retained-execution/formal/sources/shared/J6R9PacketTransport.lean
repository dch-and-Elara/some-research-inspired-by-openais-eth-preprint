import J6R9PacketLocal
import J6R9PacketReceive
import Mathlib.Tactic

/-! The exact rational identity is lifted to a polynomial identity
over TwoLocal before passing to the receiving ring. No homomorphism
from the rationals to characteristic 2^p is claimed. -/
namespace J6R9PacketTransport
open scoped BigOperators Polynomial
open DenominatorBudget P1DyadicGrid P1DyadicGridBridge
open J6R9PacketCoeff J6R9PacketLocal J6R9PacketReceive
open Polynomial

def k (i x tile j : ℕ) : ℤ := (tile:ℤ)+(2:ℤ)^(i+1)*(j:ℤ)-(x:ℤ)

noncomputable def Bpoly (a i h : ℕ) (u : ℤ) (j : ℕ) : TwoLocal[X] :=
  C (u:TwoLocal)+C ((2:TwoLocal)^(a+1-h))*X-C ((2:TwoLocal)^(i+1-h)*(j:TwoLocal))

private theorem eval_Bpoly {R : Type*} [CommRing R] (φ : TwoLocal →+* R)
    (a i h : ℕ) (u : ℤ) (j : ℕ) (z : R) :
    (Bpoly a i h u j).eval₂ φ z = B a h u z-(2:R)^(i+1-h)*(j:R) := by
  let E := Polynomial.eval₂RingHom φ z
  change E (Bpoly a i h u j) = _
  rw [Bpoly,map_sub,map_add,map_mul]
  have hc (v : TwoLocal) : E (C v) = φ v := Polynomial.eval₂_C φ z
  have hx : E X = z := Polynomial.eval₂_X _ _
  have htwo : φ (2:TwoLocal)=(2:R) := by
    change φ ((2:ℕ):TwoLocal) = ((2:ℕ):R)
    exact map_natCast φ 2
  simp [hc,hx,B,htwo]

private theorem eval_target {R : Type*} [CommRing R] (φ : TwoLocal →+* R)
    (a h : ℕ) (t : ℤ) (z : R) :
    (C ((2:TwoLocal)^(a+1-h))*X*cHat a t).eval₂ φ z =
      (2:R)^(a+1-h)*z*(cHat a t).eval₂ φ z := by
  rw [Polynomial.eval₂_mul,Polynomial.eval₂_mul,Polynomial.eval₂_C,Polynomial.eval₂_X]
  have htwo : φ (2:TwoLocal)=(2:R) := by
    change φ ((2:ℕ):TwoLocal) = ((2:ℕ):R)
    exact map_natCast φ 2
  simp [htwo]

theorem normalized_cross_polynomial {a i : ℕ} {t : ℤ} {x tile : ℕ} (j : ℕ)
    (ht : t∈grid a) (hk : k i x tile j∈grid a) (hi : i≤a) (d : Crossing t x tile i) :
    W a t (k i x tile j)*Bpoly a i d.level d.oddPart j =
      C ((2:TwoLocal)^(a+1-d.level))*X*cHat a t := by
  apply Polynomial.map_injective twoLocalRat twoLocalRat_injective
  apply Polynomial.funext
  intro z
  simp only [Polynomial.eval_map]
  rw [Polynomial.eval₂_mul,W_eval_rat ht hk,eval_Bpoly,eval_target]
  let T := (t:ℚ)+(2:ℚ)^(a+1)*z
  let H := (2:ℚ)^d.level
  let D := B a d.level d.oddPart z - (2:ℚ)^(i+1-d.level)*(j:ℚ)
  change printedW a (k i x tile j) T * D =
      (2:ℚ)^(a+1-d.level)*z*(cHat a t).eval₂ twoLocalRat z
  have hH : H ≠ 0 := pow_ne_zero _ (by decide)
  have hh : H*(2:ℚ)^(i+1-d.level) = (2:ℚ)^(i+1) := by
    unfold H
    rw [← pow_add,Nat.add_sub_of_le (d.level_le.trans (Nat.le_succ _))]
  have hA : H*(2:ℚ)^(a+1-d.level) = (2:ℚ)^(a+1) := by
    unfold H
    rw [← pow_add,Nat.add_sub_of_le (d.level_le.trans (hi.trans (Nat.le_succ _)))]
  have hD : H*D=T-(k i x tile j:ℤ) := by
    unfold D T k
    push_cast
    rw [mul_sub,← denominator_normalized hi d z,← mul_assoc,hh]
    unfold crossingInt
    push_cast
    ring
  apply mul_left_cancel₀ hH
  calc
    _ = printedW a (k i x tile j) T*(H*D) := by ring
    _ = sourceNumerator a T / (((cauchyPolynomial a).derivative.eval 0 : ℤ):ℚ) := by
      rw [hD,canceled_identity hk]
    _ = _ := by rw [normalized_numerator ht z,← hA]; ring

/-- The actual canceled port entry at a native receiving probe equals
the exact truncated tile expansion, including any signed center. -/
theorem actual_W_receives {R : Type*} [CommRing R]
    {a i : ℕ} {t : ℤ} {x tile : ℕ} (j : ℕ)
    (ht : t∈grid a) (hk : k i x tile j∈grid a) (hi : i≤a) (d : Crossing t x tile i)
    (p : ℕ) (hp : 0<p) (hnil : (2:R)^p=0) (z : R) :
    (W a t (k i x tile j)).eval₂ (J6ZeroTransport.reduceAt p hnil) z =
      ∑ b ∈ Finset.range (p-1), mode a p hnil hi d z b * (j:R)^b := by
  let φ := J6ZeroTransport.reduceAt p hnil
  let D := B a d.level d.oddPart z-(2:R)^(i+1-d.level)*(j:R)
  have hh := congrArg (fun f : TwoLocal[X] => f.eval₂ φ z) (normalized_cross_polynomial j ht hk hi d)
  change (W a t (k i x tile j)*Bpoly a i d.level d.oddPart j).eval₂ φ z =
    (C ((2:TwoLocal)^(a+1-d.level))*X*cHat a t).eval₂ φ z at hh
  rw [Polynomial.eval₂_mul,eval_Bpoly,eval_target] at hh
  change (W a t (k i x tile j)).eval₂ φ z*D = _ at hh
  have hd :
      D * (∑ b ∈ Finset.range (p-1), mode a p hnil hi d z b * (j:R)^b) =
        (2:R)^(a+1-d.level)*z*(cHat a t).eval₂ φ z :=
    printed_receive a p hp hnil hi d z _
  have hU : IsUnit D := by
    have hlev := d.level_le
    have hP (n : ℕ) (hn : 1≤n) (c : R) : (2:R) ∣ (2:R)^n*c := by
      have h := pow_dvd_pow (2:R) hn
      exact (show (2:R) ∣ (2:R)^n by simpa using h).trans (dvd_mul_right _ _)
    have hv : (2:R) ∣ (2:R)^(a+1-d.level)*z-(2:R)^(i+1-d.level)*(j:R) :=
      dvd_sub (hP _ (by omega) _) (hP _ (by omega) _)
    have hDeq : D=(d.oddPart:R)+((2:R)^(a+1-d.level)*z-(2:R)^(i+1-d.level)*(j:R)) := by
      unfold D B
      ring
    rw [hDeq]
    exact odd_plus_even_unit p hnil d.oddPart d.odd _ hv
  exact hU.mul_left_cancel (by rw [mul_comm D _,hh,← hd])

#print axioms normalized_cross_polynomial
#print axioms actual_W_receives
end J6R9PacketTransport
