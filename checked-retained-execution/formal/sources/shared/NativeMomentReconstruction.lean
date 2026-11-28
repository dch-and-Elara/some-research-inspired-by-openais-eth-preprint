import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Recovering pin values from a finite tile's power moments

An address `b : Fin n` is the order of the moment; a site `i : Fin n` is
one unknown port at a distinct public coordinate. Known nonpin ports are
absorbed into the background. The decoder removes public, possibly
order-dependent scales and this background, then multiplies by the inverse
Vandermonde matrix. Its determinant is a unit by coordinate injectivity.

For arbitrary finite assignment weights we prove the power-sum identity
by distributing the actual weighted Boolean assignment sum. If nonzero
weight forces a bit, its marginal equals the pin after division by the
nonzero total. In J7 a child returns the unnormalized source moment and
the baseline is its total weight. In J8 the native first coefficient uses
an order-dependent, nonzero scalar times this normalized moment. Source
realization, interpolation precision and bit complexity are written parts
of J7/J8. The finite algebra below is over any field, including Q.
-/

namespace NativeMomentReconstruction

open scoped BigOperators

variable {F Ω : Type*} [Field F] {n : ℕ}

/-- The first `n` power sums of masses on the given coordinates. -/
def moments (coordinate mass : Fin n → F) (b : Fin n) : F :=
  ∑ i, mass i * coordinate i ^ (b : ℕ)

/-- Recover the vector by right multiplying the observed row by V inverse. -/
noncomputable def invertMoments (coordinate observed : Fin n → F) : Fin n → F :=
  Matrix.vecMul observed (Matrix.vandermonde coordinate)⁻¹

/-- Coordinate distinctness, including the one-site case, supplies the
nonsingularity used by the explicit decoder. -/
theorem invert_moments (coordinate mass : Fin n → F)
    (hd : Function.Injective coordinate) :
    invertMoments coordinate (moments coordinate mass) = mass := by
  have hdet : IsUnit (Matrix.vandermonde coordinate).det :=
    isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hd)
  change Matrix.vecMul (Matrix.vecMul mass (Matrix.vandermonde coordinate))
    (Matrix.vandermonde coordinate)⁻¹ = mass
  rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hdet, Matrix.vecMul_one]

/-- Equality of all `n` observations forces equality of every mass. -/
theorem moments_injective (coordinate : Fin n → F)
    (hd : Function.Injective coordinate) : Function.Injective (moments coordinate) :=
  Function.LeftInverse.injective (fun mass => invert_moments coordinate mass hd)

/-- Distinct nonnegative slot coordinates stay distinct on exact rational
recovery, even if several are congruent modulo two. -/
theorem rational_coordinates (coordinate : Fin n → ℕ)
    (hd : Function.Injective coordinate) :
    Function.Injective (fun i => (coordinate i : ℚ)) := by
  intro i j h
  exact hd (Nat.cast_inj.mp h)

/-- Scale may differ at each order; background is its known unscaled
additive contribution. -/
noncomputable def decode (coordinate scale background observed : Fin n → F) : Fin n → F :=
  invertMoments coordinate (fun b => observed b / scale b - background b)

theorem decode_scaled (coordinate scale background observed mass : Fin n → F)
    (hd : Function.Injective coordinate) (hs : ∀ b, scale b ≠ 0)
    (ho : ∀ b, observed b = scale b * (background b + moments coordinate mass b)) :
    decode coordinate scale background observed = mass := by
  have h : (fun b => observed b / scale b - background b) = moments coordinate mass := by
    funext b
    rw [ho b, mul_div_cancel_left₀ _ (hs b), add_sub_cancel_left]
  unfold decode
  rw [h, invert_moments coordinate mass hd]

def bitValue (b : Bool) : F := if b then 1 else 0

variable [Fintype Ω]

/-- The true sum of all weights; it may use signed weights. -/
def total (w : Ω → F) : F := ∑ a, w a

def marginalNumerator (w : Ω → F) (sample : Ω → Fin n → Bool) (i : Fin n) : F :=
  ∑ a, w a * bitValue (sample a i)

def marginal (w : Ω → F) (sample : Ω → Fin n → Bool) (i : Fin n) : F :=
  marginalNumerator w sample i / total w

def backgroundNumerator (w : Ω → F) (other : Fin n → Ω → F) (b : Fin n) : F :=
  ∑ a, w a * other b a

/-- The genuine form of a singleton source moment: weight every assignment
by the sum of its nonpin contribution and all selected unknown pin bits
at this order. No independence between coordinates is needed. -/
def sourceMoment (w : Ω → F) (sample : Ω → Fin n → Bool)
    (coordinate : Fin n → F) (other : Fin n → Ω → F) (b : Fin n) : F :=
  ∑ a, w a * (other b a + ∑ i, bitValue (sample a i) * coordinate i ^ (b : ℕ))

/-- Distribute the original finite assignment sum port by port. -/
theorem source_moment_decomposition (w : Ω → F) (sample : Ω → Fin n → Bool)
    (coordinate : Fin n → F) (other : Fin n → Ω → F) (b : Fin n) :
    sourceMoment w sample coordinate other b =
      backgroundNumerator w other b + moments coordinate (marginalNumerator w sample) b := by
  unfold sourceMoment backgroundNumerator moments marginalNumerator
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm (s := (Finset.univ : Finset Ω)) (t := (Finset.univ : Finset (Fin n)))]

private theorem moments_div (coordinate mass : Fin n → F) (z : F) (b : Fin n) :
    moments coordinate mass b / z = moments coordinate (fun i => mass i / z) b := by
  unfold moments
  simp only [div_eq_mul_inv, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun _ _ => by ac_rfl)

/-- The normalized source moment is the known nonpin background plus the
power sum of the normalized marginals. -/
theorem normalized_source_moment (w : Ω → F) (sample : Ω → Fin n → Bool)
    (coordinate : Fin n → F) (other : Fin n → Ω → F) (b : Fin n) :
    sourceMoment w sample coordinate other b / total w =
      backgroundNumerator w other b / total w + moments coordinate (marginal w sample) b := by
  rw [source_moment_decomposition, add_div, moments_div]
  rfl

/-- The numerator of a pin supported on one bit is the product of the
actual total weight and its 0-or-1 value. -/
theorem pinned_numerator (w : Ω → F) (sample : Ω → Fin n → Bool) (i : Fin n) (pin : Bool)
    (hpin : ∀ a, w a ≠ 0 → sample a i = pin) :
    marginalNumerator w sample i = total w * bitValue pin := by
  unfold marginalNumerator total
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hw : w a = 0
  · simp [hw]
  · rw [hpin a hw]

theorem pinned_marginal (w : Ω → F) (sample : Ω → Fin n → Bool) (i : Fin n) (pin : Bool)
    (hz : total w ≠ 0) (hpin : ∀ a, w a ≠ 0 → sample a i = pin) :
    marginal w sample i = bitValue pin := by
  unfold marginal
  rw [pinned_numerator w sample i pin hpin, mul_div_cancel_left₀ _ hz]

/-- The completed-coefficient and individual-child forms share this
decoder whenever their actual observed values have the displayed scales. -/
theorem recover_marginals (w : Ω → F) (sample : Ω → Fin n → Bool)
    (coordinate scale observed : Fin n → F) (other : Fin n → Ω → F)
    (hd : Function.Injective coordinate) (hs : ∀ b, scale b ≠ 0)
    (ho : ∀ b, observed b = scale b * (sourceMoment w sample coordinate other b / total w)) :
    decode coordinate scale (fun b => backgroundNumerator w other b / total w) observed =
      marginal w sample := by
  apply decode_scaled _ _ _ _ _ hd hs
  intro b
  rw [ho b, normalized_source_moment]

/-- Direct specialization to the unnormalized source child. Its additional
public baseline is the common scale at every order. -/
theorem recover_raw_child (w : Ω → F) (sample : Ω → Fin n → Bool)
    (coordinate : Fin n → F) (other : Fin n → Ω → F)
    (hd : Function.Injective coordinate) (hz : total w ≠ 0) :
    decode coordinate (fun _ => total w) (fun b => backgroundNumerator w other b / total w)
      (sourceMoment w sample coordinate other) = marginal w sample := by
  apply recover_marginals _ _ _ _ _ _ hd (fun _ => hz)
  intro b
  exact (mul_div_cancel₀ _ hz).symm

/-- A deterministic Boolean decoder extracts 1 exactly when the
reconstructed field coordinate equals 1. -/
noncomputable def decodeBits (coordinate scale background observed : Fin n → F) : Fin n → Bool :=
  fun i => by
    classical
    exact decide (decode coordinate scale background observed i = 1)

/-- Recover the full word from its actual weighted observations. The total
and every public scale are nonzero. Assignments with zero weight may have
arbitrary bit values. -/
theorem recover_pins (w : Ω → F) (sample : Ω → Fin n → Bool) (pins : Fin n → Bool)
    (coordinate scale observed : Fin n → F) (other : Fin n → Ω → F)
    (hd : Function.Injective coordinate) (hs : ∀ b, scale b ≠ 0) (hz : total w ≠ 0)
    (hp : ∀ i a, w a ≠ 0 → sample a i = pins i)
    (ho : ∀ b, observed b = scale b * (sourceMoment w sample coordinate other b / total w)) :
    decodeBits coordinate scale (fun b => backgroundNumerator w other b / total w)
      observed = pins := by
  classical
  have hm := recover_marginals w sample coordinate scale observed other hd hs ho
  funext i
  unfold decodeBits
  rw [hm, pinned_marginal w sample i (pins i) hz (hp i)]
  cases pins i <;> simp [bitValue]

section ProductWeights

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {A : V → Type*} [∀ v, Fintype (A v)]

/-- The total on independent original column tables factors into their
local totals. The local assignment domains may have different sizes. -/
theorem product_total (w : ∀ v, A v → F) :
    total (fun x : (v : V) → A v => ∏ i, w i (x i)) = ∏ i, ∑ a, w i a :=
  (Fintype.prod_sum w).symm

/-- For the product-weight zero-probe child, a feature on one original
column can be evaluated from that column's bounded table. This applies
to its selected bit by taking the feature to be 0 or 1. -/
theorem product_local_mean (w feature : ∀ v, A v → F) (v : V)
    (hz : ∀ i, (∑ a, w i a) ≠ 0) :
    (∑ x : (i : V) → A i, (∏ i, w i (x i)) * feature v (x v)) /
      total (fun x : (i : V) → A i => ∏ i, w i (x i)) =
        (∑ a, w v a * feature v a) / (∑ a, w v a) := by
  classical
  let modified : ∀ i, A i → F := fun i a => w i a * (if i = v then feature i a else 1)
  let rest : F := ∏ i ∈ ({v} : Finset V)ᶜ, ∑ a, w i a
  have hrest : rest ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hz i)
  have hnum : (∑ x : (i : V) → A i, (∏ i, w i (x i)) * feature v (x v)) =
      (∑ a, w v a * feature v a) * rest := by
    calc
      _ = ∑ x : (i : V) → A i, ∏ i, modified i (x i) := by
        apply Finset.sum_congr rfl
        intro x _
        simp only [modified, Finset.prod_mul_distrib, Fintype.prod_ite_eq']
      _ = ∏ i, ∑ a, modified i a := (Fintype.prod_sum modified).symm
      _ = _ := by
        rw [Fintype.prod_eq_mul_prod_compl v (fun i => ∑ a, modified i a)]
        congr 1
        · simp [modified]
        · apply Finset.prod_congr rfl
          intro i hi
          have hne : i ≠ v := by simpa using hi
          simp [modified, hne]
  rw [hnum, product_total, Fintype.prod_eq_mul_prod_compl v (fun i => ∑ a, w i a)]
  change ((∑ a, w v a * feature v a) * rest) / ((∑ a, w v a) * rest) =
    (∑ a, w v a * feature v a) / (∑ a, w v a)
  apply (div_eq_div_iff (mul_ne_zero (hz v) hrest) (hz v)).mpr
  ac_rfl

end ProductWeights

#print axioms invert_moments
#print axioms moments_injective
#print axioms rational_coordinates
#print axioms decode_scaled
#print axioms source_moment_decomposition
#print axioms normalized_source_moment
#print axioms pinned_numerator
#print axioms pinned_marginal
#print axioms recover_marginals
#print axioms recover_raw_child
#print axioms recover_pins
#print axioms product_total
#print axioms product_local_mean

end NativeMomentReconstruction
