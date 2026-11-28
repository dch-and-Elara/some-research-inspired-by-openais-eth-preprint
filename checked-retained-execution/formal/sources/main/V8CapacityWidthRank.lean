import V8CapacityLift
import Mathlib.LinearAlgebra.Matrix.Rank

/-! These are ordinary matrix ranks and genuine R_p factorizations.
No assumption that an integral factor can be obtained by reducing a
nonintegral K factor termwise is made. -/
namespace V8CapacityWidthRank
open scoped Classical BigOperators
open V8CapacityCRTJet V8CapacityLift Module

noncomputable section
set_option linter.unusedSectionVars false

variable {O K I J T : Type*}
variable [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
variable [Field K] [Algebra O K] [IsFractionRing O K]
variable [Fintype I] [Fintype J] [Fintype T]

theorem separated_sum_rank (l : I → T → K) (r : T → J → K) :
    (Matrix.of fun i j => ∑ t : T, l i t*r t j).rank≤Fintype.card T := by
  let L : Matrix I T K := Matrix.of l
  let R : Matrix T J K := Matrix.of r
  change (L*R).rank≤_
  exact (Matrix.rank_mul_le_left L R).trans (Matrix.rank_le_card_width L)

/-- An arbitrary integral lift has residue-ring width at most its
ordinary fraction-field rank. The factorization is built over O first. -/
theorem residue_factor_of_krank (π : O) (p : ℕ) (A : Matrix I J O) :
    ∃ n ≤ (A.map (algebraMap O K)).rank,
      ∃ l : Matrix I (Fin n) (BaseMod O π p),
      ∃ r : Matrix (Fin n) J (BaseMod O π p),
        A.map (coeffMod O π p)=l*r := by
  let T₀ : Matrix I J K := A.map (algebraMap O K)
  let N := LinearMap.range T₀.mulVecLin
  let b := Module.finBasis K N
  let L : (Fin T₀.rank → K) →ₗ[K] (I → K) :=
    N.subtype.comp b.equivFun.symm.toLinearMap
  have hc (j : J) : ∃ w, L w=liftRows (fun i => A i j) := by
    have h₀ : T₀.mulVec (Pi.single j (1:K))=liftRows (fun i => A i j) := by
      funext i
      change (∑ a : J, T₀ i a * (Pi.single j (1:K) : J→K) a) = algebraMap O K (A i j)
      rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ _) (fun a _ ha => by simp [ha])]
      simp [T₀]
    let z : N := ⟨liftRows (fun i => A i j),⟨Pi.single j 1,h₀⟩⟩
    refine ⟨b.equivFun z,?_⟩
    change (b.equivFun.symm (b.equivFun z) : N).val = _
    rw [LinearEquiv.symm_apply_apply]
  obtain ⟨n,hn,l,r,h⟩ := integral_factor_through L (fun j i => A i j) hc
  refine ⟨n,by simpa using hn,Matrix.of (fun i t => coeffMod O π p (l i t)),
    Matrix.of (fun t j => coeffMod O π p (r t j)),?_⟩
  ext i j
  exact quotient_factor_through π p (fun j i => A i j) l r h i j

/-- A K-separated congruence to an integral output supplies an integral
lift of the same rank; one need not assume the separated factors are
individually integral. -/
theorem integral_congruent_low_rank (π : O) (p : ℕ) (target : Matrix I J O)
    (l : I → T → K) (r : T → J → K)
    (agrees : ∀ i j, ∃ e : O, algebraMap O K (target i j)-
        (∑ t : T, l i t*r t j)=algebraMap O K (π^p*e)) :
    ∃ B : Matrix I J O, B.map (coeffMod O π p)=target.map (coeffMod O π p) ∧
      (B.map (algebraMap O K)).rank≤Fintype.card T := by
  choose e he using agrees
  let B : Matrix I J O := Matrix.of fun i j => target i j-π^p*e i j
  refine ⟨B,?_,?_⟩
  · ext i j
    change coeffMod O π p (target i j-π^p*e i j)=coeffMod O π p (target i j)
    have hzero : coeffMod O π p (π^p)=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    rw [map_sub,map_mul,hzero,zero_mul,sub_zero]
  · have hB : B.map (algebraMap O K)=Matrix.of (fun i j => ∑ t : T, l i t*r t j) := by
      ext i j
      change algebraMap O K (target i j-π^p*e i j)=∑ t : T, l i t*r t j
      rw [map_sub,← he]
      ring
    rw [hB]
    exact separated_sum_rank l r

#print axioms separated_sum_rank
#print axioms residue_factor_of_krank
#print axioms integral_congruent_low_rank
end
end V8CapacityWidthRank

