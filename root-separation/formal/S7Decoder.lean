import HermiteJetTransport
import PrecisionLattice
import S7Window
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.Polynomial.Identities

/-! The canonical decoder in the common variable w = T/α, at the centers x_t = t/α. -/
namespace S7
open Finset Polynomial HermiteJetTransport
open scoped BigOperators
noncomputable section
variable {K I : Type*} [Field K]

def trunc (q : ℕ) (f : K[X]) : K[X] :=
  ∑ j ∈ range q, monomial j (f.coeff j)

@[simp] theorem coeff_trunc (q : ℕ) (f : K[X]) (j : ℕ) :
    (trunc q f).coeff j = if j < q then f.coeff j else 0 := by
  classical
  simp [trunc, finset_sum_coeff, coeff_monomial]

theorem trunc_degree (q : ℕ) (f : K[X]) : (trunc q f).degree < ↑q := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  simp [not_lt_of_ge hm]

theorem dvd_sub_trunc (q : ℕ) (f : K[X]) : X^q ∣ f - trunc q f := by
  rw [X_pow_dvd_iff]
  intro j hj
  simp [hj]

theorem trunc_eq_of_dvd_sub (q : ℕ) (f g : K[X]) (h : X^q ∣ f-g) :
    trunc q f = trunc q g := by
  ext j
  by_cases hj : j < q
  · simpa [hj, sub_eq_zero] using X_pow_dvd_iff.mp h j hj
  · simp [hj]

abbrev subst (g : K[X]) : K[X] →+* K[X] := eval₂RingHom C g

@[simp] theorem subst_X (g : K[X]) : subst g X = g := by simp
@[simp] theorem subst_C (g : K[X]) (z : K) : subst g (C z) = C z := by simp

theorem subst_shift_cancel (x : K) (f : K[X]) :
    subst (X-C x) (subst (X+C x) f) = f := by
  change (f.comp (X+C x)).comp (X-C x) = f
  rw [comp_assoc]
  have h : (X+C x).comp (X-C x) = X := by
    change subst (X-C x) (X+C x) = X
    simp
  rw [h, comp_X]

theorem jet_subst_trunc (x : K) (q : ℕ) (f : K[X]) :
    jet x q (subst (X-C x) (trunc q f)) = jet x q (subst (X-C x) f) := by
  obtain ⟨g,hg⟩ := dvd_sub_trunc q f
  have h : nodePower x q ∣ subst (X-C x) f - subst (X-C x) (trunc q f) := by
    refine ⟨subst (X-C x) g, ?_⟩
    simpa [nodePower] using congrArg (subst (X-C x)) hg
  have hz := (jet_zero_iff x q _).2 h
  rwa [map_sub, sub_eq_zero, eq_comm] at hz

def geometricInverse (q : ℕ) (g : K[X]) : K[X] :=
  ∑ j ∈ range q, (1-g)^j

theorem geometricInverse_mul (q : ℕ) (g : K[X]) :
    g * geometricInverse q g = 1 - (1-g)^q := by
  rw [mul_comm]
  simpa [geometricInverse] using geom_sum_mul_neg (1-g) q

variable [Fintype I] [DecidableEq I]

def cardinal (x : I → K) (q : I → ℕ) (t : I) : K[X] :=
  ∏ s ∈ univ.erase t, (C (x t - x s)⁻¹ * (X-C (x s))) ^ q s

def localFactor (x : I → K) (q : I → ℕ) (t : I) : K[X] :=
  subst (X+C (x t)) (cardinal x q t)

theorem localFactor_constant (x : I → K) (hx : Function.Injective x)
    (q : I → ℕ) (t : I) : (localFactor x q t).eval 0 = 1 := by
  rw [localFactor, cardinal, map_prod]
  simp only [map_pow, map_mul, map_sub, subst_C, subst_X, eval_prod, eval_pow, eval_mul,
    eval_sub, eval_add, eval_X, eval_C, zero_add]
  apply prod_eq_one
  intro s hs
  have hd : x t - x s ≠ 0 := sub_ne_zero.mpr (hx.ne (Ne.symm (mem_erase.mp hs).1))
  rw [inv_mul_cancel₀ hd, one_pow]

theorem localFactor_linearProduct (x : I → K) (hx : Function.Injective x)
    (q : I → ℕ) (t : I) :
    localFactor x q t =
    ∏ s ∈ univ.erase t, (1+C (x t-x s)⁻¹*X)^q s := by
  rw [localFactor, cardinal, map_prod]
  apply prod_congr rfl
  intro s hs
  have hd : x t - x s ≠ 0 := sub_ne_zero.mpr (hx.ne (Ne.symm (mem_erase.mp hs).1))
  simp only [map_pow, map_mul, map_sub, subst_C, subst_X]
  rw [add_sub_assoc, ← map_sub, mul_add, ← map_mul, inv_mul_cancel₀ hd, map_one, add_comm]

def piece (x : I → K) (q : I → ℕ) (t : I) (y : K[X]) : K[X] :=
  cardinal x q t *
    subst (X-C (x t)) (trunc (q t) (y * geometricInverse (q t) (localFactor x q t)))

theorem piece_here (x : I → K) (hx : Function.Injective x) (q : I → ℕ) (t : I)
    (y : K[X]) :
    jet (x t) (q t) (piece x q t y) =
      jet (x t) (q t) (subst (X-C (x t)) y) := by
  let g := localFactor x q t
  have hg : X ∣ 1-g := by
    rw [← pow_one X, X_pow_dvd_iff]
    intro j hj
    have : j = 0 := by omega
    subst j
    simp [coeff_zero_eq_eval_zero, g, localFactor_constant x hx]
  obtain ⟨f,hf⟩ := pow_dvd_pow_of_dvd hg (q t)
  let J := jet (x t) (q t)
  let U := subst (X-C (x t))
  have hz : J (U ((1-g)^q t)) = 0 := (jet_zero_iff ..).2
    ⟨U f, by simpa [J, U, nodePower] using congrArg U hf⟩
  change J (cardinal x q t * U (trunc (q t) (y * geometricInverse (q t) g))) = J (U y)
  rw [map_mul, jet_subst_trunc]
  have hback : cardinal x q t = U g := (subst_shift_cancel _ _).symm
  rw [hback, ← map_mul, ← map_mul]
  rw [show g * (y * geometricInverse (q t) g) =
    y * (g * geometricInverse (q t) g) by ac_rfl, geometricInverse_mul]
  rw [map_mul, map_sub, map_one, map_mul, map_sub, map_one, hz, sub_zero, mul_one]

theorem piece_elsewhere (x : I → K) (q : I → ℕ) (t s : I) (h : s ≠ t) (y : K[X]) :
    jet (x s) (q s) (piece x q t y) = 0 := by
  apply (jet_zero_iff ..).2
  apply dvd_mul_of_dvd_left _ _
  unfold cardinal
  apply dvd_trans _ (dvd_prod_of_mem _ (mem_erase.mpr ⟨h,mem_univ s⟩))
  rw [mul_pow, mul_comm]
  exact dvd_mul_right _ _

theorem cardinal_natDegree_le (x : I → K) (q : I → ℕ) (t : I) :
    (cardinal x q t).natDegree ≤ ∑ s ∈ univ.erase t, q s := by
  unfold cardinal
  apply le_trans (natDegree_prod_le _ _)
  apply sum_le_sum
  intro s _
  rw [natDegree_pow]
  have h : (C (x t - x s)⁻¹ * (X-C (x s))).natDegree ≤ 1 :=
    natDegree_mul_le.trans (by simp)
  simpa using Nat.mul_le_mul_left (q s) h

theorem piece_degree (x : I → K) (q : I → ℕ) (t : I) (hq : 0 < q t) (y : K[X]) :
    (piece x q t y).degree < ↑(∑ s, q s) := by
  have htr : ∀ f : K[X], (trunc (q t) f).natDegree < q t := by
    intro f
    by_cases hf : trunc (q t) f = 0
    · simpa [hf] using hq
    · exact (natDegree_lt_iff_degree_lt hf).2 (trunc_degree _ _)
  have hs := sum_erase_add univ q (mem_univ t)
  by_cases hp : piece x q t y = 0
  · rw [hp, degree_zero]
    exact WithBot.bot_lt_coe _
  rw [← natDegree_lt_iff_degree_lt hp]
  have hb : (subst (X-C (x t)) (trunc (q t)
      (y * geometricInverse (q t) (localFactor x q t)))).natDegree < q t := by
    exact natDegree_comp_le.trans_lt (by simpa only [natDegree_X_sub_C, mul_one] using htr _)
  exact natDegree_mul_le.trans_lt (by
    have := cardinal_natDegree_le x q t
    omega)

/-- The explicit local formula gives the unique canonical Hermite representative of all jets. -/
theorem canonical_sum (x : I → K) (hx : Function.Injective x) (q : I → ℕ)
    (hq : ∀ t, 0 < q t) (y : I → K[X]) :
    (((hermiteEquiv x hx q).symm (fun t =>
      jet (x t) (q t) (subst (X-C (x t)) (y t)))) : K[X]) =
      ∑ t, piece x q t (y t) := by
  let w : degreeLT K (∑ t, q t) :=
    ⟨∑ t, piece x q t (y t), mem_degreeLT.2 (by
      rw [degree_lt_iff_coeff_zero]
      intro j hj
      rw [finset_sum_coeff]
      exact sum_eq_zero fun t _ => (degree_lt_iff_coeff_zero _ _).1
        (piece_degree x q t (hq t) _) j hj)⟩
  change _ = w.val
  apply congrArg Subtype.val
  apply (hermiteEquiv x hx q).symm_apply_eq.mpr
  funext s
  change jet (x s) (q s) (subst (X-C (x s)) (y s)) = jet (x s) (q s) (∑ t, piece x q t (y t))
  rw [map_sum, sum_eq_single s]
  · exact (piece_here x hx q s (y s)).symm
  · intro t _ ht
    exact piece_elsewhere x q t s (Ne.symm ht) (y t)
  · simp

/-- The column produced by a single error in z^j, evaluated at the test monomial w^k. -/
def errorPolynomial (x : I → K) (q : I → ℕ) (t : I) (j k : ℕ) : K[X] :=
  piece x q t (X^j * (X+C (x t))^k)

theorem trunc_top (q : ℕ) (hq : 0 < q) (f : K[X]) :
    trunc q (X^(q-1) * f) = monomial (q-1) (f.coeff 0) := by
  ext m
  by_cases hm : m = q-1
  · subst m
    rw [coeff_trunc, if_pos (by omega), coeff_monomial, if_pos rfl]
    simpa using coeff_X_pow_mul f (q-1) 0
  · rw [coeff_trunc, coeff_monomial, if_neg (Ne.symm hm)]
    split_ifs with hk
    · apply X_pow_dvd_iff.mp (dvd_mul_right _ _)
      omega
    · rfl

/-- P.3 as an equality of field elements. -/
theorem highestJet_constant (x : I → K) (hx : Function.Injective x)
    (q : I → ℕ) (t : I) (hq : 0 < q t) (k : ℕ) :
    (errorPolynomial x q t (q t-1) k).coeff 0 =
      (cardinal x q t).eval 0 * (-x t)^(q t-1) * (x t)^k := by
  have hgeo : (geometricInverse (q t) (localFactor x q t)).eval 0 = 1 := by
    rw [geometricInverse, eval_finset_sum]
    simp only [eval_pow, eval_sub, eval_one, localFactor_constant x hx, sub_self]
    rw [sum_eq_single 0]
    · simp
    · intro m _ hm
      simp [zero_pow hm]
    · simp [hq]
  rw [errorPolynomial, piece, mul_assoc, trunc_top _ hq, coeff_zero_eq_eval_zero, eval_mul]
  simp only [coeff_zero_eq_eval_zero, eval_mul, eval_pow, eval_add, eval_X, eval_C, zero_add, hgeo,
    mul_one, subst]
  change _ * (eval 0 ((monomial _ _).comp _)) = _
  rw [eval_comp, eval_monomial]
  simp
  ring

end
end S7
