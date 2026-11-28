import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Dense finite-ring arithmetic for J8/J9

This file certifies a concrete postprocessing primitive, not the cost
of acquiring native completed slots. It uses dense degree-e coordinates
over Z/(2^p), schoolbook convolution and descending monic reduction.
Counts are for the printed dense loop in a scalar-word cost model.
-/

open scoped BigOperators Polynomial

namespace V9BitCost

section Word

theorem modulus_pos (p : ℕ) : 0 < (2:ℕ)^p := by positivity

/-- The exact words used by the dense schedule: product temporaries use
at most 2p bits and addition and offset subtraction at most p+1 bits.
Reduction modulo the power of two keeps only the low p bits. -/
theorem word_bounds (p x y : ℕ) (hx : x < 2^p) (hy : y < 2^p) :
    x+y < (2:ℕ)^(p+1) ∧ x+(2^p-y) < (2:ℕ)^(p+1) ∧
    x*y < (2:ℕ)^(p+p) ∧
    (x+y)%(2^p) < 2^p ∧ (x+(2^p-y))%(2^p) < 2^p ∧ (x*y)%(2^p) < 2^p := by
  have h2 : (2:ℕ)^(p+1) = 2^p * 2 := by rw [pow_succ]
  have hxy : x*y < (2:ℕ)^p * 2^p :=
    (Nat.mul_le_mul_left x hy.le).trans_lt (Nat.mul_lt_mul_of_pos_right hx (modulus_pos p))
  rw [← pow_add] at hxy
  exact ⟨by omega, by omega, hxy, Nat.mod_lt _ (modulus_pos p),
    Nat.mod_lt _ (modulus_pos p), Nat.mod_lt _ (modulus_pos p)⟩

/-- Canonical residues really do have p-bit unsigned representatives. -/
theorem canonical_width (p : ℕ) (x : ZMod (2^p)) : x.val < 2^p := by
  letI : NeZero ((2:ℕ)^p) := ⟨(modulus_pos p).ne'⟩
  exact ZMod.val_lt x

end Word

section Dense

open Polynomial
variable {R : Type*} [CommRing R]

/-- Represent e basis coordinates by the usual dense polynomial. -/
noncomputable def dense {e : ℕ} (a : Fin e → R) : R[X] :=
  ∑ i : Fin e, monomial i.val (a i)

/-- One multiplication and one accumulating addition for each ordered
pair of input coordinates. The product is not yet reduced. -/
noncomputable def convolution {e : ℕ} (a b : Fin e → R) : R[X] :=
  ∑ i : Fin e, ∑ j : Fin e, monomial (i.val+j.val) (a i*b j)

theorem convolution_eq {e : ℕ} (a b : Fin e → R) :
    convolution a b = dense a * dense b := by
  simp only [convolution, dense, Finset.sum_mul, Finset.mul_sum, monomial_mul_monomial]
  rw [Finset.sum_comm]

theorem convolution_high_zero {e : ℕ} (a b : Fin e → R) {k : ℕ} (hk : e+(e-1) ≤ k) :
    (convolution a b).coeff k = 0 := by
  simp only [convolution, Polynomial.finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  have hi := i.isLt
  have hj := j.isLt
  exact Polynomial.coeff_monomial_of_ne _ (by omega)

/-- One descending elimination takes the current high coefficient and
subtracts that coefficient times X^j f. -/
noncomputable def eliminate (f : R[X]) (j : ℕ) (P : R[X]) : R[X] :=
  P - X^j * (C (P.coeff (f.natDegree+j)) * f)

theorem eliminate_coeff (f P : R[X]) (j k : ℕ) :
    (eliminate f j P).coeff k =
      P.coeff k - if j ≤ k then P.coeff (f.natDegree+j) * f.coeff (k-j) else 0 := by
  rw [eliminate, Polynomial.coeff_sub, Polynomial.coeff_X_pow_mul']
  split <;> simp

theorem eliminate_top {f : R[X]} (hf : f.Monic) (P : R[X]) (j : ℕ) :
    (eliminate f j P).coeff (f.natDegree+j) = 0 := by
  rw [eliminate_coeff, if_pos (by omega), Nat.add_sub_cancel, hf.coeff_natDegree, mul_one, sub_self]

/-- The only potentially changed lower coordinates are exactly j through
j+e-1; the coordinate j+e is explicitly cleared. -/
theorem eliminate_untouched (f P : R[X]) (j k : ℕ)
    (h : k < j ∨ j+f.natDegree < k) :
    (eliminate f j P).coeff k = P.coeff k := by
  rw [eliminate_coeff]
  rcases h with h | h
  · rw [if_neg (by omega), sub_zero]
  · have hf : f.coeff (k-j) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [if_pos (by omega), hf, mul_zero, sub_zero]

theorem eliminate_same_class (f P : R[X]) (j : ℕ) :
    AdjoinRoot.mk f (eliminate f j P) = AdjoinRoot.mk f P := by
  simp only [eliminate, map_sub, map_mul, AdjoinRoot.mk_self, mul_zero, sub_zero]

/-- Actual descending loop j=s-1,s-2,...,0. -/
noncomputable def descending (f : R[X]) : ℕ → R[X] → R[X]
  | 0, P => P
  | j+1, P => descending f j (eliminate f j P)

theorem descending_same_class (f : R[X]) (s : ℕ) (P : R[X]) :
    AdjoinRoot.mk f (descending f s P) = AdjoinRoot.mk f P := by
  induction s generalizing P with
  | zero => rfl
  | succ s ih =>
    rw [descending, ih, eliminate_same_class]

theorem descending_high_zero {f : R[X]} (hf : f.Monic) {s : ℕ} {P : R[X]}
    (h : ∀ k, f.natDegree+s ≤ k → P.coeff k = 0) :
    ∀ k, f.natDegree ≤ k → (descending f s P).coeff k = 0 := by
  induction s generalizing P with
  | zero => simpa only [descending, Nat.add_zero] using h
  | succ s ih =>
    rw [descending]
    apply ih
    intro k hk
    by_cases he : k = f.natDegree+s
    · rw [he, eliminate_top hf P s]
    · rw [eliminate_untouched f P s k (Or.inr (by omega))]
      exact h k (by omega)

/-- Finite multiplier for the native power basis. No division is used,
and no assertion about acquiring one completed slot is part of it. -/
noncomputable def multiplyDense (f : R[X]) (a b : Fin f.natDegree → R) : R[X] :=
  descending f (f.natDegree-1) (convolution a b)

theorem multiplyDense_correct {f : R[X]} (hf : f.Monic)
    (a b : Fin f.natDegree → R) :
    AdjoinRoot.mk f (multiplyDense f a b) =
        AdjoinRoot.mk f (dense a) * AdjoinRoot.mk f (dense b) ∧
      (∀ k, f.natDegree ≤ k → (multiplyDense f a b).coeff k = 0) := by
  constructor
  · rw [multiplyDense, descending_same_class, convolution_eq, map_mul]
  · exact descending_high_zero hf (fun _ hk => convolution_high_zero a b hk)

end Dense

/-- Index sets of the dense loops: one term per ordered input pair,
or one correction to a lower coefficient in each elimination column. -/
abbrev ConvolutionUpdate (e : ℕ) := Fin e × Fin e
abbrev ReductionUpdate (e : ℕ) := Fin (e-1) × Fin e

theorem update_counts (e : ℕ) :
    Fintype.card (ConvolutionUpdate e) + Fintype.card (ReductionUpdate e) =
      e*e + (e-1)*e := by simp

/-- Count one scalar coefficient multiplication and one accumulating
addition/subtraction per update. Assigning the canceled leading
coefficient to zero costs no coefficient multiplication. -/
def coefficientUpdates (e : ℕ) : ℕ := e*e + (e-1)*e

theorem coefficientUpdates_le (e : ℕ) : coefficientUpdates e ≤ 2*e^2 := by
  unfold coefficientUpdates
  have h : (e-1)*e ≤ e*e := Nat.mul_le_mul_right e (by omega)
  nlinarith

/-- An explicit schoolbook word-operation envelope, conditional on the
usual bit-serial primitive cost (each p-bit shifted addition takes at
most p+1 carry steps; a multiplication uses at most p such rows).
The constant covers reading and storing the scalar words and erasing
the canceled coefficient. The loop count itself is exact above. -/
def ringMulEnvelope (e p : ℕ) : ℕ := 8*coefficientUpdates e*(p+1)^2 + (2*e+1)*(p+1)

theorem ringMulEnvelope_le (e p : ℕ) :
    ringMulEnvelope e p ≤ 20*(e+1)^2*(p+1)^2 := by
  have hq := coefficientUpdates_le e
  have h₁ := Nat.mul_le_mul_right ((p+1)^2) (Nat.mul_le_mul_left 8 hq)
  have h₂ : (2*e+1)*(p+1) ≤ 3*(e+1)^2*(p+1)^2 := by
    have he : 2*e+1 ≤ 3*(e+1)^2 := by nlinarith
    have hp : p+1 ≤ (p+1)^2 := by nlinarith
    exact Nat.mul_le_mul he hp
  have h₃ : 16*e^2 ≤ 17*(e+1)^2 := by nlinarith
  have h₄ := Nat.mul_le_mul_right ((p+1)^2) h₃
  unfold ringMulEnvelope
  nlinarith

/-- The input family itself has e bits per probe, even though each
returned dense residue uses e words of p bits. -/
theorem binary_coordinate_card (e : ℕ) :
    Fintype.card (Fin e → Bool) = 2^e := by simp

#print axioms word_bounds
#print axioms canonical_width
#print axioms eliminate_coeff
#print axioms multiplyDense_correct
#print axioms update_counts
#print axioms ringMulEnvelope_le
#print axioms binary_coordinate_card

end V9BitCost

