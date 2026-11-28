
import OuterNodePacking
import PrecisionErasure

namespace OuterPrecision
open scoped Polynomial
open OuterNodePacking
variable {P V R O Q W : Type*} [DecidableEq P] [DecidableEq V]
  [CommSemiring R] [CommSemiring O]

/-- J9 lower precision at every supplied certified outer-node layout.
    The coefficient structural input is the result of P5 for the actual
    set of unshifted independent old-equality bits. -/
theorem menu_const_of_outer_geometry {L : ℕ} (N p : ℕ)
    (packets : Finset P) (rowReal colReal : Slot P L → Bool)
    (oldEq : Finset V) (owner : Slot P L → V)
    (hL : 0 < L) (hEq : oldEq.card = 4 * N)
    (hPack : packets.card * L ≤ 3 * (24 * N))
    (hp : (p : ℚ) ≤ (24 * (N : ℚ)) / 6 - 3 * (24 * (N : ℚ)) / L)
    (ψ : R →+* O) (hzero : (2 : O) ^ p = 0)
    (coeffs : W → Q → R[X]) (z : Q → O) (k v : Q → ℕ)
    (hv : ∀ q, k q ≤ v q)
    (hCoeff : ∀ w q j, (2 : R) ^
      ((untouched oldEq owner (matchedColumns packets rowReal colReal ((L : ℤ) - 1))).card
        - k q - j) ∣ (coeffs w q).coeff j) :
    ∀ w, (fun q => (2 : O) ^ (v q) * z q ^ (k q) *
      (coeffs w q).eval₂ ψ (2 * z q)) = 0 := by
  intro w
  funext q
  let K := (untouched oldEq owner
      (matchedColumns packets rowReal colReal ((L : ℤ) - 1))).card
  have hK : p ≤ K := by
    exact_mod_cast hp.trans (j9_four_clone packets rowReal colReal oldEq owner N hL hEq hPack)
  have h := PrecisionErasure.every_slot_erased ψ (coeffs w q) (z q)
    K (k q) (v q) (hv q) (hCoeff w q)
  have h' := (pow_dvd_pow (2 : O) hK).trans h
  rw [hzero, zero_dvd_iff] at h'
  exact h'

/-- No decoder at any computational power can separate two distinct
    targets given the same complete native menu. -/
theorem not_decode_const_menu {A : Type*} (output : W → A) (menu : W → Q → O)
    (h : ∀ w, menu w = 0) (a b : W) (hne : output a ≠ output b) :
    ¬ ∃ decode : (Q → O) → A, ∀ w, decode (menu w) = output w := by
  rintro ⟨decode, hdec⟩
  exact hne ((hdec a).symm.trans
    ((congrArg decode ((h a).trans (h b).symm)).trans (hdec b)))

#print axioms menu_const_of_outer_geometry
#print axioms not_decode_const_menu
end OuterPrecision

