import P5P3Normalization

/-! The actual single-node fixed decoder coefficient and sharp envelope.
The product is expanded in the same polynomial coordinates as §7:
u=t/alpha, local z=w-u, and output w. -/
namespace Paper5.P3
open scoped BigOperators Polynomial
open Polynomial

variable {K : Type*} [Field K]

theorem shift_monomial (u a : K) (n : ℕ) :
    shift u (monomial n a) = C a * (C u+X)^n := by
  rw [←C_mul_X_pow_eq_monomial,map_mul,map_pow,shift_C,shift_X]

theorem scaled_plus_power (O : Subring K) (u : K) (hn : u≠0) (hi : u⁻¹∈O) (m : ℕ) :
    (C u+X)^m = C (u^m)*(((1-C (-(⟨u⁻¹,hi⟩:O))*X)^m : O[X]).map O.subtype) := by
  have h : C u * C (u⁻¹) = (1:K[X]) := by rw [←map_mul,mul_inv_cancel₀ hn,map_one]
  have he : C u+X = C u * (1-C (-u⁻¹)*X) := by
    simp only [map_neg,neg_mul,mul_sub,mul_one]
    rw [mul_neg,←mul_assoc,h,one_mul,sub_neg_eq_add]
  rw [he,mul_pow,map_pow]
  simp only [Polynomial.map_pow,Polynomial.map_sub,Polynomial.map_one,Polynomial.map_mul,
    Polynomial.map_C,Subring.coe_neg,Polynomial.map_X,Subring.subtype_apply]

theorem scaled_truncate_shift (O : Subring K) (u : K) (hn : u≠0) (hi : u⁻¹∈O)
    (q m n : ℕ) (f : O[X]) (hcount : ∀ j : Fin q,j.val≤n) :
    ∃ g : O[X], shift (-u) (truncate q (C (u^m)*f.map O.subtype)) =
      C (u^(m+n))*g.map O.subtype := by
  let v : O := ⟨u⁻¹,hi⟩
  refine ⟨∑ j : Fin q,C (f.coeff j.val * v^(n-j.val))*(C v*X-1)^j.val,?_⟩
  unfold truncate
  simp only [map_sum,shift_monomial,Polynomial.map_sum,Polynomial.map_mul,Polynomial.map_pow,
    Polynomial.map_sub,Polynomial.map_one,Polynomial.map_C,Polynomial.map_X,Subring.subtype_apply,
    Subring.coe_mul,Subring.coe_pow,coeff_C_mul,Polynomial.coeff_map,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hbase : C (-u)+X = C u*(C u⁻¹*X-1) := by
    have he : C u*C u⁻¹=(1:K[X]) := by rw [←map_mul,mul_inv_cancel₀ hn,map_one]
    rw [mul_sub,←mul_assoc,he,one_mul,mul_one,map_neg]
    ring
  have hpow : u^n*(u⁻¹)^(n-j.val)=u^j.val := by
    calc
      u^n*(u⁻¹)^(n-j.val) = (u^j.val*u^(n-j.val))*(u⁻¹)^(n-j.val) := by
        rw [←pow_add,Nat.add_sub_of_le (hcount j)]
      _ = u^j.val := by
        rw [inv_pow,mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ hn),mul_one]
  change C (u^m * ((f.coeff j.val : O):K)) * (C (-u)+X)^j.val =
    C (u^(m+n))* (C (((f.coeff j.val : O):K)*(u⁻¹)^(n-j.val)) * (C u⁻¹*X-1)^j.val)
  rw [hbase,mul_pow,←mul_assoc,←mul_assoc,←map_pow,←map_mul,←map_mul]
  congr 2
  rw [pow_add]
  calc
    u^m*((f.coeff j.val : O):K)*u^j.val =
      (u^m*u^n)*(((f.coeff j.val : O):K)*(u⁻¹)^(n-j.val)) := by
      rw [←hpow]
      ring

theorem truncate_top_shift (q : ℕ) (hq : 0<q) (f : K[X]) :
    truncate q (X^(q-1)*f) = monomial (q-1) (f.coeff 0) := by
  let j : Fin q := ⟨q-1,by omega⟩
  unfold truncate
  rw [Finset.sum_eq_single j]
  · change monomial (q-1) ((X^(q-1)*f).coeff (q-1)) = _
    rw [coeff_X_pow_mul',if_pos le_rfl,Nat.sub_self]
  · intro i _ hi
    have hn : ¬ (q - 1 ≤ i.val) := by
      have hil : i.val < q := i.isLt
      intro h
      exact hi (Fin.ext (by change i.val = q - 1; omega))
    rw [coeff_X_pow_mul',if_neg hn,monomial_zero_right]
  · simp

variable {T : Type*} [Fintype T] [DecidableEq T]

noncomputable def singleDecoder (O : Subring K) (u : T→K) (q : T→ℕ) (t : T)
    (hd : ∀ r s,(u r-u s)⁻¹∈O) (y : K[X]) : K[X] :=
  carrier u q t * shift (-u t)
    (truncate (q t) (y*(geomInverse (q t) (localNorm O u q t (hd t))).map O.subtype))

noncomputable def decoderEntry (O : Subring K) (u : T→K) (q : T→ℕ) (b : ℕ)
    (hd : ∀ r s,(u r-u s)⁻¹∈O) (r : Slot q) (i j : Fin b) : K :=
  (singleDecoder O u q r.1 hd (X^r.2.val * (C (u r.1)+X)^j.val)).coeff i.val

theorem decoder_envelope (O : Subring K) (u : T→K) (q : T→ℕ) (b : ℕ)
    (hn : ∀ t,u t≠0) (hi : ∀ t,(u t)⁻¹∈O) (hd : ∀ r s,(u r-u s)⁻¹∈O)
    (r : Slot q) (i j : Fin b) :
    InLattice O (carrierZero u q r.1 * (u r.1)^((b-1)+(q r.1-1)))
      (decoderEntry O u q b hd r i j) := by
  let t : T := r.1
  let w : K := u t
  let m := j.val
  let n := (b-1)-m+(q t-1)
  let f : O[X] := X^r.2.val *
    (1-C (-(⟨w⁻¹,hi t⟩:O))*X)^m * geomInverse (q t) (localNorm O u q t (hd t))
  have hf : X^r.2.val*(C w+X)^m*(geomInverse (q t) (localNorm O u q t (hd t))).map O.subtype =
      C (w^m) * f.map O.subtype := by
    rw [scaled_plus_power O w (hn t) (hi t) m]
    simp only [f,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X]
    ring
  have hn' (l : Fin (q t)) : l.val≤n := by
    have hl := l.isLt
    dsimp [n]
    omega
  obtain ⟨g,hg⟩ := scaled_truncate_shift O w (hn t) (hi t) (q t) m n f hn'
  have he : m+n = (b-1)+(q t-1) := by
    have hj := j.isLt
    dsimp [m,n] at *
    omega
  refine ⟨((anchorNorm O u q t hi)*g).coeff i.val,?_⟩
  unfold decoderEntry singleDecoder
  change (carrier u q t * shift (-w)
    (truncate (q t) (X^r.2.val*(C w+X)^m*(geomInverse (q t) (localNorm O u q t (hd t))).map O.subtype))).coeff i.val = _
  rw [hf,hg,he,anchor_factor O u q t hn hi]
  have hpoly : C (carrierZero u q t) * (anchorNorm O u q t hi).map O.subtype *
      (C (w^((b-1)+(q t-1)))*g.map O.subtype) =
      C (carrierZero u q t * w^((b-1)+(q t-1))) * ((anchorNorm O u q t hi)*g).map O.subtype := by
    rw [map_mul,Polynomial.map_mul]
    ring
  rw [hpoly,coeff_C_mul,Polynomial.coeff_map]
  rfl

theorem decoder_top_constant (O : Subring K) (u : T→K) (q : T→ℕ) (b : ℕ)
    (hb : 0<b) (t : T) (hq : 0<q t)
    (hn : ∀ t,u t≠0) (hi : ∀ t,(u t)⁻¹∈O) (hd : ∀ r s,(u r-u s)⁻¹∈O) :
    decoderEntry O u q b hd ⟨t,⟨q t-1,by omega⟩⟩ ⟨0,hb⟩ ⟨b-1,by omega⟩ =
      carrierZero u q t * (-u t)^(q t-1) * (u t)^(b-1) := by
  unfold decoderEntry singleDecoder
  change (carrier u q t * shift (-u t)
      (truncate (q t) (X^(q t-1)*(C (u t)+X)^(b-1)*
        (geomInverse (q t) (localNorm O u q t (hd t))).map O.subtype))).coeff 0 = _
  have he : (X^(q t-1)*(C (u t)+X)^(b-1)*
        (geomInverse (q t) (localNorm O u q t (hd t))).map O.subtype) =
      X^(q t-1)*((C (u t)+X)^(b-1)*(geomInverse (q t) (localNorm O u q t (hd t))).map O.subtype) := by ring
  have hc : (((C (u t)+X)^(b-1)) *
        (geomInverse (q t) (localNorm O u q t (hd t))).map O.subtype).coeff 0 = (u t)^(b-1) := by
    rw [coeff_zero_eq_eval_zero,eval_mul,eval_pow,eval_add,eval_C,eval_X,add_zero,←coeff_zero_eq_eval_zero,
      Polynomial.coeff_map,geomInverse_constant _ hq (localNorm_constant O u q t (hd t)),
      map_one,mul_one]
  rw [he,truncate_top_shift _ hq,hc,shift_monomial]
  rw [coeff_zero_eq_eval_zero,eval_mul,eval_mul,eval_pow,eval_add,eval_C,eval_C,eval_X,add_zero,
    ←coeff_zero_eq_eval_zero,carrierZero_eq O u q t hn hi]
  ring

#print axioms scaled_truncate_shift
#print axioms truncate_top_shift
#print axioms decoder_envelope
#print axioms decoder_top_constant
end Paper5.P3
