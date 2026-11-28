
import NativeInterpolation
import NativeMomentReconstruction
import TargetDerivative

namespace NativeCompletedRecovery
open scoped Polynomial BigOperators

variable {O Ω I : Type*} [CommRing O] [Fintype Ω] {n : ℕ}

/-- The exact completed singleton, represented in the source rational ring
    for the algebraic first-order audit, with one targeted allocation. -/
noncomputable def completed (s : Finset I) (pubPoly source : ℚ[X])
    (kernel target : I → ℚ[X]) : ℚ[X] :=
  (pubPoly * source) * ∑ i ∈ s, kernel i * target i

/-- Finite J8 pipeline: actual unit-separated finite-ring probes, a
    denominator-clearing lift, the source/target first-coefficient identity,
    and original weighted pin recovery. The original compiler must supply the
    indicated realization of the rational slot and bound its numerator. -/
theorem recovery {prec : ℕ} (hp : 0 < prec) (hnil : (2 : O)^prec = 0)
    (probes : Fin (prec+1) → O) (hu : ∀ i j, i ≠ j → IsUnit (probes j - probes i))
    (embed : ZMod (2^prec) →+* O) (project : O → ZMod (2^prec))
    (left : Function.LeftInverse project embed)
    (v : Fin n → ℕ) (hv : ∀ b, 1 ≤ v b)
    (c : Fin n → ℕ → O) (D a : Fin n → ℤ) (hD : ∀ b, D b ≠ 0)
    (fits : ∀ b, a b * 2 ∈ Set.Ioc (-(↑((2:ℕ)^prec)) : ℤ) ↑((2:ℕ)^prec))
    (lifted : ∀ b, (D b : O) * ((2 : O)^v b * c b 0) =
        embed (a b : ZMod (2^prec)))
    (s : Fin n → Finset I) (hs : ∀ b, (s b).Nonempty)
    (pubPoly source : Fin n → ℚ[X]) (kernel target : Fin n → I → ℚ[X])
    (vanish : ∀ b i, i ∈ s b → (kernel b i).coeff 0 = 0)
    (positive : ∀ b, 0 < (pubPoly b).coeff 0)
    (negK : ∀ b i, i ∈ s b → (kernel b i).coeff 1 < 0)
    (negT : ∀ b i, i ∈ s b → (target b i).coeff 0 < 0)
    (numerator : ∀ b, (a b : ℚ) =
      D b * (completed (s b) (pubPoly b) (source b) (kernel b) (target b)).coeff 1)
    (w : Ω → ℚ) (sample : Ω → Fin n → Bool) (pins : Fin n → Bool)
    (coord : Fin n → ℚ) (other : Fin n → Ω → ℚ)
    (hd : Function.Injective coord) (hz : 0 < NativeMomentReconstruction.total w)
    (hpin : ∀ i x, w x ≠ 0 → sample x i = pins i)
    (hsrc : ∀ b, (source b).coeff 0 =
      NativeMomentReconstruction.sourceMoment w sample coord other b) :
    let scale := fun b => ((pubPoly b).coeff 0 *
      ∑ i ∈ s b, (kernel b i).coeff 1 * (target b i).coeff 0) *
        NativeMomentReconstruction.total w
    let obs := fun b => ((project ((D b : O) * NativeInterpolation.decode probes
      (fun j => (NativeInterpolation.normalized prec (v b) 1 (c b)).eval (probes j))
      ⟨1, by omega⟩)).valMinAbs : ℚ) / D b
    NativeMomentReconstruction.decodeBits coord scale
      (fun b => NativeMomentReconstruction.backgroundNumerator w other b /
        NativeMomentReconstruction.total w) obs = pins := by
  dsimp only
  apply NativeMomentReconstruction.recover_pins _ _ _ _ _ _ _ hd _ hz.ne' hpin
  · intro b
    rw [NativeInterpolation.lift_rational_after_interpolation prec (v b) hp (hv b) hnil
      (c b) probes hu embed project left (D b) (a b) (hD b) _ (fits b) (lifted b) (numerator b)]
    rw [completed, TargetDerivative.first_completed_target _ _ _ _ _ (vanish b), hsrc b]
    rw [mul_assoc ((pubPoly b).coeff 0 * ∑ i ∈ s b, (kernel b i).coeff 1 * (target b i).coeff 0),
      mul_div_cancel₀ _ hz.ne']
  · intro b
    apply mul_ne_zero _ hz.ne'
    exact (TargetDerivative.completed_scale_positive (s b) (hs b)
      ((pubPoly b).coeff 0) (fun i => (kernel b i).coeff 1) (fun i => (target b i).coeff 0)
      (positive b) (negK b) (negT b)).ne'

#print axioms recovery
end NativeCompletedRecovery

