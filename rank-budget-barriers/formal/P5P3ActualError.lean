import P5P3Canonical
import P5P3ExactCriterion

/-! The independent perturbation expression is the actual fixed
Hermite interpolation of products with encoded test monomials. -/
namespace Paper5.P3
open scoped BigOperators Polynomial
open Polynomial

variable {K : Type*} [Field K]

theorem truncate_add (q : ℕ) (x y : K[X]) :
    truncate q (x+y) = truncate q x+truncate q y := by
  simp only [truncate,coeff_add,monomial_add,Finset.sum_add_distrib]

theorem truncate_C_mul (q : ℕ) (a : K) (x : K[X]) :
    truncate q (C a*x)=C a*truncate q x := by
  simp only [truncate,coeff_C_mul,Finset.mul_sum,C_mul_monomial]

variable {T : Type*} [Fintype T] [DecidableEq T]

theorem single_add (O : Subring K) (u : T→K) (q : T→ℕ) (t : T)
    (hd : ∀ r s,(u r-u s)⁻¹∈O) (x y : K[X]) :
    singleDecoder O u q t hd (x+y)=singleDecoder O u q t hd x+singleDecoder O u q t hd y := by
  simp only [singleDecoder,add_mul,truncate_add,map_add,mul_add]

theorem single_C_mul (O : Subring K) (u : T→K) (q : T→ℕ) (t : T)
    (hd : ∀ r s,(u r-u s)⁻¹∈O) (a : K) (x : K[X]) :
    singleDecoder O u q t hd (C a*x)=C a*singleDecoder O u q t hd x := by
  unfold singleDecoder
  rw [mul_assoc,truncate_C_mul,map_mul,shift_C]
  ring

theorem single_sum {J : Type*} (O : Subring K) (u : T→K) (q : T→ℕ) (t : T)
    (hd : ∀ r s,(u r-u s)⁻¹∈O) (S : Finset J) (x : J→K[X]) :
    singleDecoder O u q t hd (∑ j∈S,x j)=∑ j∈S,singleDecoder O u q t hd (x j) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [singleDecoder,truncate]
  | insert i S hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi,single_add,ih]

noncomputable def perturbedLocalProduct (O : Subring K) (u : T→K) (q : T→ℕ)
    (a : T→K) (e : Slot q→O) (m : ℕ) (t : T) : K[X] :=
  (∑ j : Fin (q t),monomial j.val (a t*(e ⟨t,j⟩:K))) * shift (u t) (X^m)

theorem actual_perturbation_entry (O : Subring K) (u : T→K) (q : T→ℕ) (b : ℕ)
    (hd : ∀ r s,(u r-u s)⁻¹∈O) (a : T→K) (e : Slot q→O) (i j : Fin b) :
    (fixedInterpolate O u q hd (perturbedLocalProduct O u q a e j.val)).coeff i.val =
      ∑ x : Slot q,decoderEntry O u q b hd x i j*a x.1*(e x:K) := by
  unfold fixedInterpolate
  rw [Polynomial.finset_sum_coeff,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro t _
  unfold perturbedLocalProduct
  rw [map_pow,shift_X,Finset.sum_mul,single_sum,Polynomial.finset_sum_coeff]
  apply Finset.sum_congr rfl
  intro z _
  rw [←C_mul_X_pow_eq_monomial,mul_assoc,single_C_mul,coeff_C_mul]
  unfold decoderEntry
  dsimp
  ring

def ActualCertified (O : Subring K) (u : T→K) (q : T→ℕ) (b : ℕ)
    (hd : ∀ r s,(u r-u s)⁻¹∈O) (a : T→K) (p : K) : Prop :=
  ∀ (e : Slot q→O) (i j : Fin b), InLattice O p
    ((fixedInterpolate O u q hd (perturbedLocalProduct O u q a e j.val)).coeff i.val)

theorem actual_certified_p1 (O : Subring K) (π : Kˣ)
    (hm : ∀ n : ℤ,(↑(π^n):K)∈O ↔ 0≤n)
    (u : T→K) (q : T→ℕ) (b : ℕ) (hb : 0<b)
    (P loss c : T→ℤ) (p : ℤ)
    (hn : ∀ t,u t≠0) (hi : ∀ t,(u t)⁻¹∈O) (hd : ∀ r s,(u r-u s)⁻¹∈O)
    (hu : ∀ t,0<q t → ∃ w : Oˣ,u t=(↑(π^(-loss t)):K)*((w:O):K))
    (hc : ∀ t,0<q t → ∃ w : Oˣ,carrierZero u q t=(↑(π^(c t)):K)*((w:O):K)) :
    ActualCertified O u q b hd (fun t => (↑(π^(P t)):K)) (↑(π^p):K) ↔
      ∀ t,0<q t → (↑b+↑(q t)-2)*loss t ≤ P t-p+c t := by
  unfold ActualCertified
  simp_rw [actual_perturbation_entry]
  exact fixed_decoder_p1 O π hm u q b hb P loss c p hn hi hd hu hc

#print axioms single_add
#print axioms single_C_mul
#print axioms actual_perturbation_entry
#print axioms actual_certified_p1
end Paper5.P3
