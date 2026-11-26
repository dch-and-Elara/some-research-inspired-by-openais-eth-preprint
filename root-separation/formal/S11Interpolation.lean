
import HermiteJetTransport
import IntegralOutputTransfer
import Mathlib.LinearAlgebra.Lagrange

noncomputable section

namespace S11
open scoped BigOperators
open Polynomial

variable {K I J : Type*} [Field K] [Fintype I] [Fintype J]

/-- Translate from the local z coordinate back to the global T coordinate. -/
def backShift (t α : K) : K[X] →ₗ[K] K[X] where
  toFun f := f.comp (C α⁻¹ * (X - C t))
  map_add' _ _ := add_comp
  map_smul' c f := smul_comp c f _

private theorem shift_cancel (f : K[X]) (t α : K) (hα : α ≠ 0) :
    backShift t α (f.comp (C t + C α * X)) = f := by
  change (f.comp (C t + C α * X)).comp (C α⁻¹ * (X - C t)) = f
  rw [comp_assoc, add_comp, C_comp, mul_comp, C_comp, X_comp, ← mul_assoc, ← C_mul,
    mul_inv_cancel₀ hα, C_1, one_mul, add_sub_cancel, comp_X]

/-- The printed two-stage linear decoder. For each t, interpolate all
    local samples, convert to the jet at t in global coordinates, then
    take the constant coefficient of the Hermite reconstruction. -/
def probeDecoder [DecidableEq J] (t : I → K) (ht : Function.Injective t) (q : I → ℕ)
    (ζ : I → J → K) (α : K) : (I → J → K) →ₗ[K] K :=
  (Polynomial.lcoeff K 0).comp
    ((degreeLT K _).subtype.comp ((HermiteJetTransport.hermiteEquiv t ht q).symm.toLinearMap.comp
      (LinearMap.pi fun i =>
        ((Ideal.Quotient.mkₐ K (HermiteJetTransport.nodeIdeal (t i) (q i))).toLinearMap.comp
          ((backShift (t i) α).comp ((Lagrange.interpolate Finset.univ (ζ i)).comp
            (LinearMap.proj i)))))))

theorem probeDecoder_exact [DecidableEq J] (t : I → K) (ht : Function.Injective t) (q : I → ℕ)
    (ζ : I → J → K) (hζ : ∀ i, Function.Injective (ζ i)) (α : K) (hα : α ≠ 0)
    (F : K[X]) (hF : F.degree < ↑(∑ i, q i))
    (hlocal : ∀ i, (F.comp (C (t i) + C α * X)).degree < ↑(Fintype.card J)) :
    probeDecoder t ht q ζ α (fun i j => F.eval (t i + α * ζ i j)) = F.eval 0 := by
  classical
  let y : degreeLT K (∑ i, q i) := ⟨F, mem_degreeLT.2 hF⟩
  have hy : (HermiteJetTransport.hermiteEquiv t ht q) y =
      fun i => HermiteJetTransport.jet (t i) (q i) (backShift (t i) α
        (Lagrange.interpolate Finset.univ (ζ i) (fun j => F.eval (t i + α * ζ i j)))) := by
    funext i
    have hi : Lagrange.interpolate Finset.univ (ζ i) (fun j => F.eval (t i + α * ζ i j)) =
        F.comp (C (t i) + C α * X) := by
      symm
      apply Lagrange.eq_interpolate_of_eval_eq _ (hζ i).injOn
      · simpa using hlocal i
      · intro j _
        simp [eval_comp]
    rw [hi, shift_cancel F _ _ hα]
    rfl
  unfold probeDecoder
  change constantCoeff ((HermiteJetTransport.hermiteEquiv t ht q).symm
    (fun i => HermiteJetTransport.jet (t i) (q i) (backShift (t i) α
      (Lagrange.interpolate Finset.univ (ζ i) (fun j => F.eval (t i + α * ζ i j)))))).val = _
  rw [← hy, LinearEquiv.symm_apply_apply]
  simp [y, coeff_zero_eq_eval_zero]

private def probeUnit [DecidableEq I] [DecidableEq J] (i : I) (j : J) : I → J → K :=
  fun a b => if a = i then if b = j then 1 else 0 else 0

/-- A fixed sample coordinate of the linear reconstruction. -/
def probeWeight [DecidableEq I] [DecidableEq J]
    (D : (I → J → K) →ₗ[K] K) (i : I) (j : J) : K :=
  D (probeUnit i j)

theorem weighted_probes [DecidableEq I] [DecidableEq J]
    (D : (I → J → K) →ₗ[K] K) (x : I → J → K) :
    D x = ∑ i, ∑ j, probeWeight D i j * x i j := by
  have hx : x = ∑ i, ∑ j, x i j • (probeUnit i j : I → J → K) := by
    funext i j
    simp [Finset.sum_apply, probeUnit, mul_ite]
  conv_lhs => rw [hx]
  simp [probeWeight, mul_comm]

/-- Local units stay integral in the Lagrange stage, even though
    reconstruction is carried out in the field. -/
theorem lagrange_basis_integral {R : Type*} [CommRing R] (embed : R →+* K)
    [DecidableEq J] (ζ : J → R) (hu : ∀ i j, i ≠ j → IsUnit (ζ i - ζ j)) (i : J) :
    ∃ b : R[X], b.map embed = Lagrange.basis Finset.univ (embed ∘ ζ) i := by
  classical
  have inv (j : J) (h : j ≠ i) :
      ∃ v : R, embed v = (embed (ζ i) - embed (ζ j))⁻¹ := by
    obtain ⟨u, hu⟩ := hu i j h.symm
    refine ⟨↑u⁻¹, ?_⟩
    have he : embed (↑u : R) = embed (ζ i) - embed (ζ j) := by simp [hu]
    rw [← he]
    have hm : embed (↑u⁻¹ : R) * embed (↑u : R) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    exact eq_inv_of_mul_eq_one_left hm
  let v (j : J) : R := if h : j ≠ i then Classical.choose (inv j h) else 0
  refine ⟨∏ j ∈ Finset.univ.erase i, C (v j) * (X - C (ζ j)), ?_⟩
  simp only [Lagrange.basis, Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro j hj
  have h := (Finset.mem_erase.1 hj).1
  have hv : embed (v j) = (embed (ζ i) - embed (ζ j))⁻¹ := by
    dsimp [v]
    rw [dif_pos h]
    exact Classical.choose_spec (inv j h)
  simp [Lagrange.basisDivisor, hv]

/-- Once each source coefficient's denominator has been cleared, finite
    precision transfer uses only errors in the stated independent ideals. -/
theorem decoder_congruence {R : Type*} [CommRing R] [DecidableEq I] [DecidableEq J]
    (embed : R →+* K) (D : (I → J → K) →ₗ[K] K)
    (p : ℕ) (prec : I → ℕ)
    (orig sample err cleared : I → J → R)
    (herr : ∀ i j, sample i j = orig i j + 2 ^ prec i * err i j)
    (hclear : ∀ i j, probeWeight D i j * embed (2 ^ prec i) =
      embed (2 ^ p * cleared i j)) :
    D (fun i j => embed (sample i j)) =
      D (fun i j => embed (orig i j)) +
      embed (2 ^ p * ∑ i, ∑ j, cleared i j * err i j) := by
  have h (i : I) (j : J) : probeWeight D i j * embed (sample i j) =
      probeWeight D i j * embed (orig i j) + embed (2 ^ p * (cleared i j * err i j)) := by
    rw [herr, map_add, mul_add, map_mul, ← mul_assoc, hclear]
    simp only [map_mul]
    ring
  rw [weighted_probes D (fun i j => embed (sample i j)),
    weighted_probes D (fun i j => embed (orig i j))]
  simp_rw [h, Finset.sum_add_distrib, ← map_sum, ← Finset.mul_sum]

#print axioms probeDecoder_exact
#print axioms weighted_probes
#print axioms lagrange_basis_integral
#print axioms decoder_congruence

end S11

