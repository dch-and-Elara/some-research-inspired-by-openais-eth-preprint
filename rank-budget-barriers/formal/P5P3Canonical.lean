import P5P3Decoder
import Mathlib.RingTheory.AdjoinRoot

/-! The explicit fixed Hermite formula meets the actual retained jets.
This is a transfer between literal polynomial congruence classes and
the single-node coefficient formula, not a substituted decoder. -/
namespace Paper5.P3
open scoped BigOperators Polynomial
open Polynomial

variable {K : Type*} [Field K]

theorem shift_add_composite (u v : K) : (shift u).comp (shift v) = shift (u+v) := by
  apply Polynomial.ringHom_ext
  · intro a
    change shift u (shift v (C a)) = shift (u+v) (C a)
    simp
  · change shift u (shift v X) = shift (u+v) X
    rw [shift_X,map_add,shift_C,shift_X,shift_X,map_add]
    ring

theorem shift_zero_id (p : K[X]) : shift 0 p = p := by
  change p.comp (C 0+X) = _
  rw [map_zero,zero_add,comp_X]

theorem shift_inverse (u : K) (p : K[X]) : shift u (shift (-u) p) = p := by
  change ((shift u).comp (shift (-u))) p = _
  rw [shift_add_composite,add_neg_cancel,shift_zero_id]

variable {T : Type*} [Fintype T] [DecidableEq T]

theorem single_matches_own_jet (O : Subring K) (u : T→K) (q : T→ℕ) (t : T)
    (hi : Function.Injective u) (hd : ∀ r s,(u r-u s)⁻¹∈O) (y : K[X]) :
    AdjoinRoot.mk (X^(q t)) (shift (u t) (singleDecoder O u q t hd y)) =
      AdjoinRoot.mk (X^(q t)) y := by
  let d := localNorm O u q t (hd t)
  let inv := geomInverse (q t) d
  let M := AdjoinRoot.mk (X^(q t):K[X])
  have h0 : X^(q t) ∣ d*inv-1 := geom_inverse_mod d (q t) (localNorm_constant O u q t (hd t))
  have h1 : (X^(q t):K[X]) ∣ d.map O.subtype*inv.map O.subtype-1 := by
    have h := map_dvd (Polynomial.mapRingHom O.subtype) h0
    change ((X^(q t):O[X]).map O.subtype) ∣ (d*inv-1).map O.subtype at h
    simpa only [Polynomial.map_pow,Polynomial.map_X,Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_one] using h
  have h2 : M (d.map O.subtype)*M (inv.map O.subtype)=1 := by
    rw [←map_mul,←map_one M]
    exact AdjoinRoot.mk_eq_mk.mpr h1
  have ht : M (truncate (q t) (y*inv.map O.subtype)) = M (y*inv.map O.subtype) :=
    (AdjoinRoot.mk_eq_mk.mpr (truncate_sub_dvd (q t) (y*inv.map O.subtype))).symm
  unfold singleDecoder
  change M (shift (u t) (carrier u q t * shift (-u t) (truncate (q t) (y*inv.map O.subtype)))) = M y
  rw [map_mul,shift_inverse,local_factor O u q t hi (hd t),map_mul,ht,map_mul]
  change M (d.map O.subtype) * (M y * M (inv.map O.subtype)) = M y
  rw [mul_comm (M y),←mul_assoc,h2,one_mul]

theorem carrier_vanish_other (u : T→K) (q : T→ℕ) {t s : T} (h : s≠t) :
    (X-C (u s))^(q s) ∣ carrier u q t := by
  unfold carrier
  exact (pow_dvd_pow_of_dvd (dvd_mul_right (X-C (u s)) _) (q s)).trans
    (Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨h,Finset.mem_univ _⟩))

theorem single_vanishes_other_jet (O : Subring K) (u : T→K) (q : T→ℕ) {t s : T} (h : s≠t)
    (hd : ∀ r a,(u r-u a)⁻¹∈O) (y : K[X]) :
    AdjoinRoot.mk (X^(q s)) (shift (u s) (singleDecoder O u q t hd y)) = 0 := by
  obtain ⟨a,ha⟩ := carrier_vanish_other u q h
  have hshift : shift (u s) ((X-C (u s))^q s*a) = X^q s * shift (u s) a := by
    rw [map_mul,map_pow,map_sub,shift_X,shift_C,add_sub_cancel_left]
  unfold singleDecoder
  rw [ha,map_mul (shift (u s)),hshift,map_mul,map_mul,AdjoinRoot.mk_self,zero_mul,zero_mul]

noncomputable def fixedInterpolate (O : Subring K) (u : T→K) (q : T→ℕ)
    (hd : ∀ r s,(u r-u s)⁻¹∈O) (y : T→K[X]) : K[X] :=
  ∑ t,singleDecoder O u q t hd (y t)

theorem fixed_interpolate_jets (O : Subring K) (u : T→K) (q : T→ℕ)
    (hi : Function.Injective u) (hd : ∀ r s,(u r-u s)⁻¹∈O) (y : T→K[X]) (t : T) :
    AdjoinRoot.mk (X^(q t)) (shift (u t) (fixedInterpolate O u q hd y)) =
      AdjoinRoot.mk (X^(q t)) (y t) := by
  unfold fixedInterpolate
  simp only [map_sum]
  rw [Finset.sum_eq_single t]
  · exact single_matches_own_jet O u q t hi hd (y t)
  · intro i _ h
    exact single_vanishes_other_jet O u q (Ne.symm h) hd (y i)
  · simp

#print axioms shift_add_composite
#print axioms shift_inverse
#print axioms single_matches_own_jet
#print axioms carrier_vanish_other
#print axioms single_vanishes_other_jet
#print axioms fixed_interpolate_jets
end Paper5.P3
