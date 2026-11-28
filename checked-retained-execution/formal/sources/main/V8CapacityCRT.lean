import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

/-! Integral polynomial selectors for v8 A3/A4's whole residue fibers.
Their coefficients live in the original coefficient ring; only the evaluation
uses the finite receiving ring. Distinct chosen residues must have unit
differences, with no assumptions on characteristic or on search for digits. -/
namespace V8CapacityCRT
open scoped BigOperators Polynomial Classical
open Polynomial

noncomputable section

variable {O S I : Type*} [CommRing O] [CommRing S]
variable [Fintype I] [DecidableEq I]

def recip (d : I → O) (sep : ∀ a b, a≠b → IsUnit (d a-d b)) (a b : I) : O :=
  if h : a≠b then ↑((sep a b h).unit⁻¹) else 0

omit [Fintype I] in
theorem recip_exact (d : I → O) (sep : ∀ a b, a≠b → IsUnit (d a-d b)) {a b : I} (h : a≠b) :
    recip d sep a b * (d a-d b)=1 := by
  let u := (sep a b h).unit
  have hu : (u:O)=d a-d b := (sep a b h).unit_spec
  rw [recip,dif_pos h]
  change (↑(u⁻¹):O)*(d a-d b)=1
  rw [← hu]
  exact Units.inv_mul u

def base (d : I → O) (sep : ∀ a b, a≠b → IsUnit (d a-d b)) (a : I) : O[X] :=
  ∏ c ∈ Finset.univ.erase a, C (recip d sep a c)*(X-C (d c))

theorem base_at_center (φ : O →+* S) (d : I → O) (sep : ∀ a b, a≠b → IsUnit (d a-d b)) (a b : I) :
    (base d sep a).eval₂ φ (φ (d b)) = if b=a then 1 else 0 := by
  let E := Polynomial.eval₂RingHom φ (φ (d b))
  change E (base d sep a)=_
  rw [base,map_prod]
  have hc (c : I) : E (C (recip d sep a c)*(X-C (d c))) =
      φ (recip d sep a c)*(φ (d b)-φ (d c)) := by
    rw [map_mul,map_sub]
    change (C (recip d sep a c)).eval₂ φ (φ (d b)) *
      ((X:O[X]).eval₂ φ (φ (d b))-(C (d c)).eval₂ φ (φ (d b))) = _
    simp only [eval₂_C,eval₂_X]
  simp only [hc]
  by_cases hb : b=a
  · rw [if_pos hb]
    apply Finset.prod_eq_one
    intro c hC
    rw [hb,← map_sub,← map_mul,recip_exact d sep (Finset.ne_of_mem_erase hC).symm,map_one]
  · rw [if_neg hb]
    exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hb,Finset.mem_univ b⟩) (by simp)

omit [Fintype I] [DecidableEq I] in
theorem nil_of_factor {x y : S} (n : ℕ) (hx : x^n=0) (h : x∣y) : y^n=0 := by
  rcases h with ⟨z,rfl⟩
  rw [mul_pow,hx,zero_mul]

omit [Fintype I] [DecidableEq I] in
theorem eval₂_diff_dvd (φ : O →+* S) (P : O[X]) (x y : S) :
    x-y ∣ P.eval₂ φ x-P.eval₂ φ y := by
  simpa only [eval_map] using sub_dvd_eval_sub x y (P.map φ)

def sharpen (n : ℕ) (P : O[X]) : O[X] := 1-(1-P^n)^n

omit [Fintype I] [DecidableEq I] in
theorem sharpen_eval (φ : O →+* S) (P : O[X]) (x : S) (n : ℕ) :
    (sharpen n P).eval₂ φ x = 1-(1-(P.eval₂ φ x)^n)^n := by
  let E := Polynomial.eval₂RingHom φ x
  change E (sharpen n P)=_
  simp only [sharpen,map_sub,map_pow,map_one]
  rfl

/-- An explicit replacement for an existential CRT witness. The same
integral source polynomial separates the whole neighborhoods. -/
def selector (d : I → O) (sep : ∀ a b, a≠b → IsUnit (d a-d b)) (n : ℕ) (a : I) : O[X] :=
  sharpen n (base d sep a)

theorem selector_at_nilpotent (φ : O →+* S) (d : I → O)
    (sep : ∀ a b, a≠b → IsUnit (d a-d b)) (n : ℕ) (a b : I) (x : S)
    (hx : (x-φ (d b))^n=0) :
    (selector d sep n a).eval₂ φ x = if b=a then 1 else 0 := by
  let y := (base d sep a).eval₂ φ x
  have hd := eval₂_diff_dvd φ (base d sep a) x (φ (d b))
  rw [base_at_center] at hd
  change x-φ (d b) ∣ y-(if b=a then 1 else 0) at hd
  rw [selector,sharpen_eval]
  change 1-(1-y^n)^n = _
  by_cases hb : b=a
  · rw [if_pos hb] at hd ⊢
    have hy : (y-1)^n=0 := nil_of_factor n hx hd
    have hy' : (1-y)^n=0 := by rw [← neg_sub y 1,neg_pow,hy,mul_zero]
    have hd' : (1-y) ∣ 1-y^n :=
      ⟨∑ i ∈ Finset.range n,y^i,(mul_neg_geom_sum y n).symm⟩
    rw [nil_of_factor n hy' hd',sub_zero]
  · rw [if_neg hb,sub_zero] at hd
    rw [if_neg hb,nil_of_factor n hx hd,sub_zero,one_pow,sub_self]

omit [Fintype I] [DecidableEq I] in
theorem pow_vanish_of_le {s : S} {u j : ℕ} (hs : s^u=0) (h : u≤j) : s^j=0 := by
  rw [← Nat.add_sub_of_le h,pow_add,hs,zero_mul]

/-- The exact v8 exponent P+k−1 for the native receiver's two
truncations. Neither a field nor a domain is assumed. -/
theorem two_ideal_power (π z x y : S) (P k : ℕ)
    (hπ : π^P=0) (hz : z^k=0) :
    (π*x+z*y)^(P+k-1)=0 := by
  rw [add_pow]
  apply Finset.sum_eq_zero
  intro j hj
  have hj' : j≤P+k-1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [mul_pow,mul_pow]
  by_cases h : P≤j
  · rw [pow_vanish_of_le hπ h,zero_mul,zero_mul,zero_mul]
  · have h' : k≤P+k-1-j := by omega
    rw [pow_vanish_of_le hz h',zero_mul,mul_zero,zero_mul]

theorem selector_on_jet (φ : O →+* S) (d : I → O)
    (sep : ∀ a b, a≠b → IsUnit (d a-d b)) (P k : ℕ)
    (π z v w : S) (hπ : π^P=0) (hz : z^k=0) (a b : I) :
    (selector d sep (P+k-1) a).eval₂ φ (φ (d b)+(π*v+z*w)) = if b=a then 1 else 0 := by
  apply selector_at_nilpotent
  rw [add_sub_cancel_left]
  exact two_ideal_power π z v w P k hπ hz

#print axioms recip_exact
#print axioms base_at_center
#print axioms eval₂_diff_dvd
#print axioms sharpen_eval
#print axioms selector_at_nilpotent
#print axioms two_ideal_power
#print axioms selector_on_jet
end
end V8CapacityCRT
