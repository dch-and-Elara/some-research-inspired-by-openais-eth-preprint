
import S11NativeWindow

noncomputable section
namespace S11

open Polynomial
open scoped BigOperators

variable {K J : Type*} [Field K] [Fintype J] [DecidableEq J]
variable (v : AddValuation K (WithTop ℤ))

theorem lagrange_probe_errors (ζ : J → K)
    (hint : ∀ j, 0 ≤ v (ζ j)) (hunit : ∀ i j, i ≠ j → v (ζ i-ζ j) = 0)
    (p : ℕ) (err : J → K) (herr : ∀ j, (↑(p:ℤ):WithTop ℤ) ≤ v (err j)) :
    S7.CoeffBound v (↑(p:ℤ)) (Lagrange.interpolate Finset.univ ζ err) := by
  have hb (j : J) : S7.CoeffBound v 0 (Lagrange.basis Finset.univ ζ j) := by
    unfold Lagrange.basis
    apply S7.integral_prod v
    intro k hk
    unfold Lagrange.basisDivisor
    have hh := hunit j k (Finset.mem_erase.1 hk).1.symm
    have hv : v ((ζ j-ζ k)⁻¹) = 0 := by rw [v.map_inv,hh,neg_zero]
    have hC := S7.bound_C v ((ζ j-ζ k)⁻¹)
    rw [hv] at hC
    simpa only [zero_add, sub_eq_add_neg] using S7.bound_mul v hC
      (S7.bound_add v (S7.bound_X v) (S7.bound_neg v (S7.bound_weaken v (hint k) (S7.bound_C v _))))
  rw [Lagrange.interpolate_apply]
  apply S7.bound_sum v
  intro j _
  simpa only [add_zero] using S7.bound_mul v
    (S7.bound_weaken v (herr j) (S7.bound_C v _)) (hb j)

variable [CharZero K]

/-- Propagate each independently lifted probe error through the actual
    two source stages. The output is the origin coefficient of the
    native Hermite error, with its scaled centers and printed p_t. -/
theorem printed_probe_error_clearing (h₂ : v (2:K) = 1)
    (M a u p : ℕ) (hM : 0 < M) (hu : 0 < u) (huM : u ≤ M)
    (ζ : Active a u → J → K)
    (hint : ∀ t j, 0 ≤ v (ζ t j))
    (hunit : ∀ t i j, i ≠ j → v (ζ t i-ζ t j) = 0)
    (err : Active a u → J → K)
    (herr : ∀ t j, (↑(precision p M a u (2^a) t.val:ℤ):WithTop ℤ) ≤ v (err t j)) :
    let q := fun t : Active a u => multiplicity M u t.val
    let x := fun t : Active a u => S7.scaledCenter a t.val
    ∃ e : K, 0 ≤ v e ∧
      (∑ j : Σ t, Fin (q t),
        ((Lagrange.interpolate Finset.univ (ζ j.1) (err j.1)).coeff j.2) *
        (S7.errorPolynomial x q j.1 j.2 0).coeff 0) = 2^p*e := by
  classical
  dsimp only
  let q := fun t : Active a u => multiplicity M u t.val
  let eps := fun j : (Σ t, Fin (q t)) =>
    ((Lagrange.interpolate Finset.univ (ζ j.1) (err j.1)).coeff j.2)
  have hcoeff (j : Σ t, Fin (q t)) :
      (↑(precision p M a u (2^a) j.1.val:ℤ):WithTop ℤ) ≤ v (eps j) :=
    lagrange_probe_errors v (ζ j.1) (hint j.1) (hunit j.1) _ (err j.1) (herr j.1) j.2
  have h := source_taper_certified v h₂ M a u p hM hu huM
  exact (S7.valuation_threshold v h₂ p _).1 (h eps hcoeff ⟨0,by decide⟩ ⟨0,by decide⟩)

#print axioms lagrange_probe_errors
#print axioms printed_probe_error_clearing

end S11

