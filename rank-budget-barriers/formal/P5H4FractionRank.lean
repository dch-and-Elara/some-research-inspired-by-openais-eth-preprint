import P5H4Final

/-! The normal rank defined by exact nonzero minors is also the actual
matrix rank after passing to the rational function field. -/
namespace P5H4
open Polynomial Matrix
open scoped BigOperators Classical

variable {K m n : Type*} [Field K] [Fintype m] [Fintype n]

set_option maxHeartbeats 5200000 in
theorem normalRank_fraction_field (A : Matrix m n K[X]) (P : GeneralProfile A) :
    (A.map (algebraMap K[X] (FractionRing K[X]))).rank = P.normalRank := by
  obtain ⟨r,e,a,U,Z,C,T,ha,hU,hu,hC,hT⟩ := rectangular_chart A
  let φ : K[X] →+* FractionRing K[X] := algebraMap ..
  have hφ : Function.Injective φ := IsFractionRing.injective _ _
  have hrZ : (A.map φ).rank = (Z.map φ).rank := by
    refine le_antisymm ?_ ?_
    · rw [← hC,Matrix.map_mul]
      exact Matrix.rank_mul_le_left _ _
    · rw [← hT,Matrix.map_mul]
      exact Matrix.rank_mul_le_left _ _
  have hdv := chart_minors_of A e a U Z C T hU hu hC hT
  have hr : r = P.normalRank := by
    refine le_antisymm ?_ ?_
    · exact (P.minor_support r).mp ((normal_minor_support A a ha r (hdv r)).mpr le_rfl)
    · exact (normal_minor_support A a ha P.normalRank (hdv P.normalRank)).mp
        ((P.minor_support P.normalRank).mpr le_rfl)
  have hUZ : ((rowDiagonal e a).map φ).rank = (Z.map φ).rank := by
    obtain ⟨u,rfl⟩ := hU
    rw [←hu,Matrix.map_mul]
    have hi : u.inv.map φ * u.val.map φ = 1 := by
      rw [←Matrix.map_mul,u.inv_val]
      simp
    refine le_antisymm (Matrix.rank_mul_le_right _ _) ?_
    have he : u.inv.map φ * (u.val.map φ * Z.map φ) = Z.map φ := by
      rw [←Matrix.mul_assoc,hi,Matrix.one_mul]
    calc
      (Z.map φ).rank = (u.inv.map φ * (u.val.map φ * Z.map φ)).rank := congrArg Matrix.rank he.symm
      _ ≤ _ := Matrix.rank_mul_le_right (u.inv.map φ) (u.val.map φ * Z.map φ)
  have hsub : (((rowDiagonal e a).map φ).submatrix e id) =
      diagonal (fun i => φ (a i)) := by
    apply Matrix.ext
    intro i j
    change φ (if e i = e j then a j else 0) = _
    by_cases h : i=j
    · subst j
      simp
    · simp [h,e.injective.ne h]
  have hdiag : (diagonal (fun i => φ (a i))).rank = r := by
    have hn (i) : φ (a i) ≠ 0 := by
      intro hz
      exact ha i (hφ (hz.trans (map_zero φ).symm))
    simp [Matrix.rank_diagonal,hn]
  have hD : ((rowDiagonal e a).map φ).rank = r := by
    refine le_antisymm (by simpa using Matrix.rank_le_card_width ((rowDiagonal e a).map φ)) ?_
    calc
      r = (diagonal (fun i => φ (a i))).rank := hdiag.symm
      _ = ((((rowDiagonal e a).map φ).submatrix e id)).rank := congrArg Matrix.rank hsub.symm
      _ ≤ _ := Matrix.rank_submatrix_le e (Equiv.refl _) _
  change (A.map φ).rank = P.normalRank
  exact hrZ.trans (hUZ.symm.trans (hD.trans hr))

#print axioms normalRank_fraction_field
end P5H4
