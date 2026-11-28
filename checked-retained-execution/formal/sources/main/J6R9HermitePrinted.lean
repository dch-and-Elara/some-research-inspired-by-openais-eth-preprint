import J6R9HermiteNative
import J6R9RecursiveWeights

/-! Coordinate-valued finite Hermite readout with the actual exact
polynomial on the signed grid, rather than a hypothesized global
weighted identity. -/
namespace J6R9Hermite
open scoped BigOperators Polynomial
open Polynomial J6ActiveSchedule J6ActiveUniqueness J6ActivePrintedHermite
open DyadicProbeCompiler NativeProbeRing

variable {K : Type*} [CommRing K] [Nontrivial K] [Algebra ℚ K]

/-- A scalar coefficient in the source basis has the correct reconstructed
residue. The only finite input hypothesis is receipt of the actual
retained divided-jet coefficients for that coordinate. -/
theorem printed_coordinate_native (a M u p : ℕ) (hu : 0<u) (hM : u≤M)
    (F : K[X]) (hdeg : F.natDegree ≤ J9PrintedSchedule.degreeBound M (2^a))
    (read : K→ₗ[ℚ]ℚ) (out : Source)
    (origin : J8EndToEnd.rationalMap out = read (F.eval 0))
    (truth : ℤ→ℕ→Source)
    (literalQuot : ∀ t∈active a M u, ∀ j<order M u t,
      J8EndToEnd.rationalMap (truth t j) =
        read ((J6R9Recursive.divided a M u (atNode (dyadicUnit a) (t:K) F) t).coeff j))
    (menu : (t : ℤ)→ℕ→Base (childPrecision p a M u t))
    (receipt : ∀ t∈active a M u, ∀ j<order M u t,
      menu t j = coeffReduction (childPrecision p a M u t) (truth t j)) :
    ∃ z : Source, J8EndToEnd.rationalMap z =
      recompose a M u (fun t j => ((menu t j).val:ℚ)) ∧
      coeffReduction p z = coeffReduction p out := by
  let exactJet (t : ℤ) (j : ℕ) : K :=
    (J6R9Recursive.divided a M u (atNode (dyadicUnit a) (t:K) F) t).coeff j
  have he : linearRecompose a M u exactJet = F.eval 0 := by
    simpa only [linearRecompose,exactJet,Algebra.smul_def] using
      (J6R9Recursive.exact_origin_weights a M u hu hM F hdeg
        (fun t => atNode (dyadicUnit a) (t:K) F) (fun _ _ _ _ => rfl))
  have hread := congrArg read he
  rw [recompose_coordinate,←origin] at hread
  apply finite_native_receive a M u p hM truth out menu ?_ receipt
  rw [← hread]
  unfold recompose
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro j hj
  exact congrArg (fun x : ℚ => HermiteLoss.weight a u (HermiteLoss.sourceH M u) j t*x)
    (literalQuot t ht j (Finset.mem_range.mp hj))
#print axioms printed_coordinate_native
end J6R9Hermite

