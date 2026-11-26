import P5P3Precision
import Mathlib.Algebra.Polynomial.Div

/-! Literal Lagrange/Hermite carrier for one retained node. The two
integral factors are derived from the actual product, once the
reciprocals of centers and cross differences are integral. -/
namespace Paper5.P3
open scoped BigOperators Polynomial
open Polynomial

variable {K : Type*} [Field K] {T : Type*} [Fintype T] [DecidableEq T]

noncomputable def shift (a : K) : K[X]→+*K[X] := compRingHom (C a+X)

@[simp] theorem shift_C (a x : K) : shift a (C x) = C x := by
  change (C x).comp (C a+X) = C x
  rw [C_comp]

@[simp] theorem shift_X (a : K) : shift a X = C a+X := by
  change X.comp (C a+X) = _
  rw [X_comp]

noncomputable def carrier (u : T→K) (q : T→ℕ) (t : T) : K[X] :=
  ∏ s ∈ Finset.univ.erase t, ((X-C (u s))*C ((u t-u s)⁻¹))^(q s)

noncomputable def carrierZero (u : T→K) (q : T→ℕ) (t : T) : K :=
  ∏ s ∈ Finset.univ.erase t, ((-u s)*(u t-u s)⁻¹)^(q s)

noncomputable def anchorNorm (O : Subring K) (u : T→K) (q : T→ℕ) (t : T)
    (hc : ∀ s,(u s)⁻¹∈O) : O[X] :=
  ∏ s ∈ Finset.univ.erase t, (1-C (⟨(u s)⁻¹,hc s⟩:O)*X)^(q s)

noncomputable def localNorm (O : Subring K) (u : T→K) (q : T→ℕ) (t : T)
    (hd : ∀ s,(u t-u s)⁻¹∈O) : O[X] :=
  ∏ s ∈ Finset.univ.erase t, (1+C (⟨(u t-u s)⁻¹,hd s⟩:O)*X)^(q s)

theorem anchor_factor (O : Subring K) (u : T→K) (q : T→ℕ) (t : T)
    (hn : ∀ s,u s≠0) (hc : ∀ s,(u s)⁻¹∈O) :
    carrier u q t = C (carrierZero u q t) * (anchorNorm O u q t hc).map O.subtype := by
  unfold carrier carrierZero anchorNorm
  simp only [Polynomial.map_prod,Polynomial.map_pow,Polynomial.map_sub,Polynomial.map_one,
    Polynomial.map_mul,Polynomial.map_C,Polynomial.map_X,Subring.subtype_apply]
  rw [map_prod,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro s _
  rw [map_pow,←mul_pow]
  apply congrArg (fun p : K[X] => p^(q s))
  have hmul : C (-u s) * C (u s)⁻¹ = -(1:K[X]) := by
    rw [←map_mul,neg_mul,mul_inv_cancel₀ (hn s),map_neg,map_one]
  rw [map_mul]
  calc
    (X-C (u s))*C (u t-u s)⁻¹ =
       (C (-u s)*(1-C (u s)⁻¹*X))*C (u t-u s)⁻¹ := by
      congr 1
      rw [mul_sub,mul_one,←mul_assoc,hmul,neg_mul,one_mul,map_neg]
      ring
    _ = C (-u s)*C (u t-u s)⁻¹*(1-C (u s)⁻¹*X) := by ring

theorem local_factor (O : Subring K) (u : T→K) (q : T→ℕ) (t : T)
    (hi : Function.Injective u) (hd : ∀ s,(u t-u s)⁻¹∈O) :
    shift (u t) (carrier u q t) = (localNorm O u q t hd).map O.subtype := by
  unfold carrier localNorm
  simp only [Polynomial.map_prod,Polynomial.map_pow,Polynomial.map_add,Polynomial.map_one,
    Polynomial.map_mul,Polynomial.map_C,Polynomial.map_X,Subring.subtype_apply,map_prod,map_pow]
  apply Finset.prod_congr rfl
  intro s hs
  have hn : u t-u s≠0 := sub_ne_zero.mpr (fun h => (Finset.ne_of_mem_erase hs) (hi h).symm)
  have hmul : C (u t-u s) * C (u t-u s)⁻¹ = (1:K[X]) := by
    rw [←map_mul,mul_inv_cancel₀ hn,map_one]
  simp only [map_mul,map_sub,shift_X,shift_C]
  have he : (C (u t)+X-C (u s):K[X]) = C (u t-u s)+X := by rw [map_sub]; ring
  rw [he,add_mul,hmul,mul_comm X]

theorem anchorNorm_constant (O : Subring K) (u : T→K) (q : T→ℕ) (t : T)
    (hc : ∀ s,(u s)⁻¹∈O) : (anchorNorm O u q t hc).coeff 0 = 1 := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  unfold anchorNorm
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_one
  intro s _
  simp

theorem localNorm_constant (O : Subring K) (u : T→K) (q : T→ℕ) (t : T)
    (hd : ∀ s,(u t-u s)⁻¹∈O) : (localNorm O u q t hd).coeff 0 = 1 := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  unfold localNorm
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_one
  intro s _
  simp

theorem carrierZero_eq (O : Subring K) (u : T→K) (q : T→ℕ) (t : T)
    (hn : ∀ s,u s≠0) (hc : ∀ s,(u s)⁻¹∈O) :
    (carrier u q t).coeff 0 = carrierZero u q t := by
  rw [anchor_factor O u q t hn hc,coeff_C_mul,Polynomial.coeff_map,
    anchorNorm_constant,map_one,mul_one]

theorem carrierZero_ne (u : T→K) (q : T→ℕ) (t : T)
    (hn : ∀ s,u s≠0) (hi : Function.Injective u) : carrierZero u q t≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro s hs
  have hne : u t-u s≠0 := sub_ne_zero.mpr (fun h => (Finset.ne_of_mem_erase hs) (hi h).symm)
  exact pow_ne_zero _ (mul_ne_zero (neg_ne_zero.mpr (hn s)) (inv_ne_zero hne))

section FiniteTruncation
variable {R : Type*} [CommRing R]

noncomputable def truncate (n : ℕ) (f : R[X]) : R[X] :=
  ∑ j : Fin n, monomial j.val (f.coeff j.val)

theorem truncate_small (n : ℕ) (f : R[X]) (j : Fin n) :
    (truncate n f).coeff j.val = f.coeff j.val := by
  rw [truncate,Polynomial.finset_sum_coeff,Finset.sum_eq_single j]
  · simp
  · intro i _ hi
    have h : i.val≠j.val := fun h => hi (Fin.ext h)
    simp [Polynomial.coeff_monomial,h]
  · simp

theorem truncate_sub_dvd (n : ℕ) (f : R[X]) : X^n ∣ f-truncate n f := by
  apply Polynomial.X_pow_dvd_iff.mpr
  intro j hj
  rw [coeff_sub,truncate_small n f ⟨j,hj⟩,sub_self]

noncomputable def geomInverse (n : ℕ) (f : R[X]) : R[X] :=
  ∑ j ∈ Finset.range n, (1-f)^j

theorem geomIdentity (f : R[X]) (n : ℕ) :
    f*geomInverse n f = 1-(1-f)^n := by
  induction n with
  | zero => simp [geomInverse]
  | succ n ih =>
    rw [show geomInverse (n+1) f = geomInverse n f + (1-f)^n
      by simp only [geomInverse,Finset.sum_range_succ],mul_add,ih,pow_succ]
    ring

theorem geom_inverse_mod (f : R[X]) (n : ℕ) (hf : f.coeff 0=1) :
    X^n ∣ f*geomInverse n f-1 := by
  have h : X ∣ 1-f := by
    rw [Polynomial.X_dvd_iff,coeff_sub,coeff_one_zero,hf,sub_self]
  rw [geomIdentity,sub_right_comm,sub_self,zero_sub]
  exact dvd_neg.mpr (pow_dvd_pow_of_dvd h n)

theorem geomInverse_constant (f : R[X]) {n : ℕ} (hn : 0<n) (hf : f.coeff 0=1) :
    (geomInverse n f).coeff 0=1 := by
  rw [Polynomial.coeff_zero_eq_eval_zero,geomInverse,Polynomial.eval_finset_sum]
  have he : eval 0 f = 1 := (Polynomial.coeff_zero_eq_eval_zero f).symm.trans hf
  simp only [eval_pow,eval_sub,eval_one,he,sub_self]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j _ hj
    simp [hj]
  · simp [hn]
end FiniteTruncation

#print axioms anchor_factor
#print axioms local_factor
#print axioms carrierZero_eq
#print axioms carrierZero_ne
#print axioms truncate_small
#print axioms truncate_sub_dvd
#print axioms geom_inverse_mod
#print axioms geomInverse_constant
end Paper5.P3
