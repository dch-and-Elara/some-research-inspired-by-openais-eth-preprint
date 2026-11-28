import V8CapacitySpecialProfile
import V8CapacitySpecialSmithSplit
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Rank-zero part of the actual Smith image equals matrix rank over
the residue field. Comparing different evaluation grids is done at
raw polynomial level, not by falsely identifying normalized Newton
functions on lifts of one residue value. -/
namespace V8CapacitySpecialRankCompare
open scoped Classical BigOperators
open V8CapacitySpecialSplit V8CapacitySpecialProfile V8CapacitySmith

noncomputable section
set_option linter.unusedSectionVars false

variable {O I J T : Type*} [CommRing O] [IsDomain O] [IsLocalRing O]
variable [Fintype I] [Fintype J] [Fintype T]

local notation "κ" => IsLocalRing.ResidueField O
local notation "ρ" => IsLocalRing.residue O

theorem range_reduces (π : O) (M : Matrix I J O) :
    satSpan π 0 (matrixImage M) = LinearMap.range (M.map ρ).mulVecLin := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨z,rfl⟩
    have hz := z.property
    change (π^0:O) • z.val∈matrixImage M at hz
    rw [pow_zero,one_smul] at hz
    obtain ⟨a,ha⟩ := hz
    refine ⟨red a,?_⟩
    funext i
    change (M.map ρ).mulVec (ρ ∘ a) i = ρ (z.val i)
    rw [← RingHom.map_mulVec]
    exact congrArg ρ (congrFun ha i)
  · rintro _ ⟨a,rfl⟩
    choose a' ha using (fun j : J => IsLocalRing.residue_surjective (a j))
    let z : saturation π 0 (matrixImage M) := ⟨M.mulVec a',by
      change (π^0:O) • M.mulVec a'∈matrixImage M
      rw [pow_zero,one_smul]
      exact ⟨a',rfl⟩⟩
    apply Submodule.subset_span
    refine ⟨z,?_⟩
    funext i
    have e : ρ ∘ a'=a := funext ha
    change ρ (M.mulVec a' i)=(M.map ρ).mulVec a i
    rw [RingHom.map_mulVec,e]

variable [IsPrincipalIdealRing O]

theorem units_count_from_rank (π : O) (hπ : π≠0)
    (hMax : IsLocalRing.maximalIdeal O=Ideal.span ({π}:Set O)) (M : Matrix I J O) :
    (M.map ρ).rank = Fintype.card (V8CapacityWidthUpper.Active (matrixPowered π hMax M).2 1) := by
  let S := (matrixPowered π hMax M).2
  have h := profile_card (fromSmith S) hπ hMax 0
  rw [range_reduces] at h
  change (M.map ρ).rank=Fintype.card {i : Fin (matrixPowered π hMax M).1 // S.exponent i≤0} at h
  refine h.trans (Fintype.card_congr ?_)
  exact
    { toFun := fun i => ⟨i.val,by have hi := i.property; change S.exponent i.val<1; omega⟩
      invFun := fun i => ⟨i.val,by have hi := i.property; change S.exponent i.val<1 at hi; omega⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- Genuine rank equality, even with duplicate chosen Newton residues:
it requires recovery from a row restriction of the raw matrix. -/
theorem same_rank_of_raw_evaluation (C : Matrix I J O)
    (V : Matrix I I O) (unit : IsUnit V.det)
    (G : Matrix T I κ) (B : Matrix T J κ) (take : I → T)
    (whole : B=G*(C.map ρ)) (small : B.submatrix take id=(V.map ρ)*(C.map ρ)) :
    B.rank=(C.map ρ).rank := by
  apply le_antisymm
  · rw [whole]
    exact Matrix.rank_mul_le_right G (C.map ρ)
  · have hv : ((V⁻¹).map ρ)*(V.map ρ)=(1:Matrix I I κ) := by
      rw [← Matrix.map_mul,Matrix.nonsing_inv_mul V unit,Matrix.map_one]
      · exact map_zero _
      · exact map_one _
    have hrecover : ((V⁻¹).map ρ)*(B.submatrix take id)=C.map ρ := by
      rw [small,← Matrix.mul_assoc,hv,Matrix.one_mul]
    calc
      _ = (((V⁻¹).map ρ)*(B.submatrix take id)).rank := congrArg Matrix.rank hrecover.symm
      _ ≤ (B.submatrix take id).rank := Matrix.rank_mul_le_right _ _
      _ ≤ _ := Matrix.rank_submatrix_le take (Equiv.refl J) B

#print axioms range_reduces
#print axioms units_count_from_rank
#print axioms same_rank_of_raw_evaluation
end
end V8CapacitySpecialRankCompare

