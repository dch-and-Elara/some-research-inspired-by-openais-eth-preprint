
import S11ProbeErrors
import S11Kernel

noncomputable section
namespace RootSeparation.Solver

open S11 Polynomial
open scoped BigOperators

variable {K I J : Type*} [Field K] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

private theorem trunc_add (q : ℕ) (f g : K[X]) :
    S7.trunc q (f+g) = S7.trunc q f + S7.trunc q g := by
  ext j
  by_cases h : j < q <;> simp [S7.coeff_trunc, coeff_add, h]

private theorem trunc_C_mul (q : ℕ) (c : K) (f : K[X]) :
    S7.trunc q (C c*f) = C c*S7.trunc q f := by
  ext j
  simp [S7.coeff_trunc, coeff_C_mul, mul_ite]

def pieceLinear (x : I → K) (q : I → ℕ) (t : I) : K[X] →ₗ[K] K[X] where
  toFun := S7.piece x q t
  map_add' f g := by
    unfold S7.piece
    rw [add_mul, trunc_add, map_add, mul_add]
  map_smul' c f := by
    simp only [RingHom.id_apply, smul_eq_C_mul]
    unfold S7.piece
    rw [mul_assoc, trunc_C_mul, map_mul, S7.subst_C]
    ring

/-- The source local quotient uses only the first q_t coefficients,
    also when Lagrange is supplied the full probe list. -/
theorem piece_trunc (x : I → K) (q : I → ℕ) (t : I) (f : K[X]) :
    S7.piece x q t (S7.trunc (q t) f) = S7.piece x q t f := by
  unfold S7.piece
  congr 2
  apply S7.trunc_eq_of_dvd_sub
  rw [← sub_mul]
  have hp : X^(q t) ∣ S7.trunc (q t) f - f := by
    rw [show S7.trunc (q t) f - f = -(f - S7.trunc (q t) f) by ring]
    exact dvd_neg.2 (S7.dvd_sub_trunc (q t) f)
  exact dvd_mul_of_dvd_left hp _

/-- Formula (contraction 275–345), with T measured in units alpha.
    Lagrange is followed by multiplication by each truncated reciprocal,
    the centered evaluation shift, and the cardinal-polynomial sum. -/
def readout (x : I → K) (q : I → ℕ) (ζ : I → J → K) : (I → J → K) →ₗ[K] K :=
  ∑ t, (lcoeff K 0).comp ((pieceLinear x q t).comp
    ((Lagrange.interpolate Finset.univ (ζ t)).comp (LinearMap.proj t)))

theorem readout_apply (x : I → K) (q : I → ℕ) (ζ : I → J → K) (f : I → J → K) :
    readout x q ζ f =
      ∑ t, (S7.piece x q t (Lagrange.interpolate Finset.univ (ζ t) (f t))).eval 0 := by
  simp [readout,pieceLinear,coeff_zero_eq_eval_zero]

private theorem readout_columns (x : I → K) (q : I → ℕ) (ζ : I → J → K) (f : I → J → K) :
    readout x q ζ f =
      ∑ j : Σ t, Fin (q t),
        ((Lagrange.interpolate Finset.univ (ζ j.1) (f j.1)).coeff j.2) *
        (S7.errorPolynomial x q j.1 j.2 0).coeff 0 := by
  rw [readout_apply, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro t _
  let Q := Lagrange.interpolate Finset.univ (ζ t) (f t)
  change (S7.piece x q t Q).eval 0 = _
  rw [← piece_trunc x q t Q]
  change ((pieceLinear x q t) (S7.trunc (q t) Q)).eval 0 = _
  unfold S7.trunc
  change _ = ∑ j : Fin (q t), Q.coeff j.val * (S7.errorPolynomial x q t j.val 0).coeff 0
  rw [map_sum, eval_finset_sum,
    Fin.sum_univ_eq_sum_range (fun j : ℕ => Q.coeff j * (S7.errorPolynomial x q t j 0).coeff 0)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← C_mul_X_pow_eq_monomial, ← smul_eq_C_mul, map_smul,
    eval_smul, smul_eq_mul]
  simp [pieceLinear,S7.errorPolynomial,coeff_zero_eq_eval_zero,Q]

theorem readout_exact (x : I → K) (hx : Function.Injective x)
    (q : I → ℕ) (hq : ∀ t, 0 < q t) (ζ : I → J → K)
    (hζ : ∀ t, Function.Injective (ζ t)) (F : K[X])
    (hF : F.degree < ↑(∑ t, q t))
    (hloc : ∀ t, (F.comp (X+C (x t))).degree < ↑(Fintype.card J)) :
    readout x q ζ (fun t j => F.eval (x t + ζ t j)) = F.eval 0 := by
  classical
  let y : I → K[X] := fun t => F.comp (X+C (x t))
  have hy (t : I) :
      Lagrange.interpolate Finset.univ (ζ t) (fun j => F.eval (x t + ζ t j)) = y t := by
    symm
    apply Lagrange.eq_interpolate_of_eval_eq _ (hζ t).injOn
    · simpa [y] using hloc t
    · intro j _
      simp [y,eval_comp,add_comm]
  let b : degreeLT K (∑ t, q t) := ⟨F,mem_degreeLT.2 hF⟩
  have hm : (HermiteJetTransport.hermiteEquiv x hx q) b =
      fun t => HermiteJetTransport.jet (x t) (q t)
        (S7.subst (X-C (x t)) (y t)) := by
    funext t
    change _ = HermiteJetTransport.jet (x t) (q t) (S7.subst (X-C (x t)) (S7.subst (X+C (x t)) F))
    rw [S7.subst_shift_cancel]
    rfl
  have hr := S7.canonical_sum x hx q hq y
  rw [← hm,LinearEquiv.symm_apply_apply] at hr
  rw [readout_apply]
  simp_rw [hy, ← eval_finset_sum]
  rw [← hr]

variable [CharZero K]

/-- No Hermite-return hypothesis is needed: correctness on exact probes
    and the printed precision budget are composed for this decoder. -/
theorem recover_modular (v : AddValuation K (WithTop ℤ)) (h₂ : v (2:K) = 1)
    (M a u p : ℕ) (hM : 0 < M) (hu : 0 < u) (huM : u ≤ M)
    (ζ : Active a u → J → K)
    (hint : ∀ t j, 0 ≤ v (ζ t j))
    (hunit : ∀ t i j, i ≠ j → v (ζ t i-ζ t j) = 0)
    (F : K[X])
    (hF : F.degree < ↑(∑ t : Active a u, multiplicity M u t.val))
    (hlocal : ∀ t : Active a u, (F.comp (X+C (S7.scaledCenter a t.val))).degree < ↑(Fintype.card J))
    (lifted : Active a u → J → K)
    (herr : ∀ t j, (↑(precision p M a u (2^a) t.val:ℤ):WithTop ℤ) ≤
      v (lifted t j - F.eval (S7.scaledCenter a t.val + ζ t j))) :
    ∃ e : K, 0 ≤ v e ∧
      readout (fun t : Active a u => S7.scaledCenter a t.val)
        (fun t => multiplicity M u t.val) ζ lifted = F.eval 0 + (2:K)^p*e := by
  classical
  let x : Active a u → K := fun t => S7.scaledCenter a t.val
  let q : Active a u → ℕ := fun t => multiplicity M u t.val
  let trueProbes (t : Active a u) (j : J) := F.eval (x t + ζ t j)
  let D := readout x q ζ
  have hζ (t) : Function.Injective (ζ t) := by
    intro i j he
    by_contra! hn
    have h := hunit t i j hn
    rw [he,sub_self,v.map_zero] at h
    exact WithTop.top_ne_coe h
  have hq (t : Active a u) : 0 < q t := by
    have hh := three_mul_le_taper_mul (M := M) hu
    have hn : 0 < taper M u := by
      by_contra! h
      have he : taper M u = 0 := by omega
      rw [he,zero_mul] at hh
      omega
    have hl := active_level t
    exact Nat.mul_pos hn (by omega)
  have htrue : D trueProbes = F.eval 0 :=
    readout_exact x (fun t s h => Subtype.ext (S7.scaledCenter_injective v h₂ a h))
      q hq ζ hζ F hF hlocal
  obtain ⟨e,he,heq⟩ := printed_probe_error_clearing v h₂ M a u p hM hu huM ζ hint hunit
    (lifted-trueProbes) herr
  refine ⟨e,he,?_⟩
  change D lifted = _
  have hh : D (lifted-trueProbes) = 2^p*e := by
    dsimp [D]
    rw [readout_columns]
    exact heq
  rw [map_sub,htrue] at hh
  exact sub_eq_iff_eq_add'.1 hh

#print axioms piece_trunc
#print axioms readout_exact
#print axioms recover_modular

end RootSeparation.Solver

