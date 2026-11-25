import Mathlib.Algebra.Polynomial.Div

/-! Nilpotent specialization of an actual truncated polynomial jet.
This file does not assert a rank or runtime lower bound. -/

namespace NativeJetEvaluation

open Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

theorem eval_eq_of_sub_dvd_X_pow (f : R →+* S) (p q : R[X])
    (x : S) (h : ℕ) (hx : x ^ h = 0)
    (hpq : (X : R[X]) ^ h ∣ p - q) :
    p.eval₂ f x = q.eval₂ f x := by
  obtain ⟨a, ha⟩ := hpq
  have he := congrArg (fun b : R[X] => b.eval₂ f x) ha
  simp only [eval₂_sub, eval₂_mul, eval₂_X_pow, hx, zero_mul] at he
  exact sub_eq_zero.mp he

theorem eval_truncated_jet (f : R →+* S) (p : R[X])
    (x : S) (h : ℕ) (hx : x ^ h = 0) :
    (p %ₘ (X : R[X]) ^ h).eval₂ f x = p.eval₂ f x := by
  apply eval₂_modByMonic_eq_self_of_root (monic_X.pow h)
  simpa only [eval₂_X_pow] using hx

theorem nilpotent_power_for_precision (pi : S) (p b h : ℕ)
    (hp : pi ^ p = 0) (hbh : p ≤ b * h) :
    (pi ^ b) ^ h = 0 := by
  rw [← pow_mul]
  exact pow_eq_zero_of_le hbh hp

theorem eval_truncated_at_precision (f : R →+* S) (poly : R[X])
    (pi : S) (p b h : ℕ) (hp : pi ^ p = 0) (hbh : p ≤ b * h) :
    (poly %ₘ (X : R[X]) ^ h).eval₂ f (pi ^ b) = poly.eval₂ f (pi ^ b) := by
  exact eval_truncated_jet f poly (pi ^ b) h
    (nilpotent_power_for_precision pi p b h hp hbh)

#print axioms eval_eq_of_sub_dvd_X_pow
#print axioms eval_truncated_jet
#print axioms nilpotent_power_for_precision
#print axioms eval_truncated_at_precision

end NativeJetEvaluation
