import V8CapacityUnifiedObservation
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! U7/S6: rank can be charged blockwise in the same final row/column
matrix even when individual representatives are fractional. It is the
sum that has integral entries and an invertible reduction. -/
namespace V8CapacityUnified.U7
open scoped Classical BigOperators
open Module V8CapacityCRTJet

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

variable {K X Y T : Type*} [Field K] [Fintype X] [Fintype Y]

theorem rank_add_le (A B : Matrix X Y K) : (A+B).rank≤A.rank+B.rank := by
  let a := LinearMap.range A.mulVecLin
  let b := LinearMap.range B.mulVecLin
  have h : LinearMap.range (A+B).mulVecLin≤a⊔b := by
    rintro u ⟨v,rfl⟩
    apply Submodule.mem_sup.mpr
    refine ⟨A.mulVec v,⟨v,rfl⟩,B.mulVec v,⟨v,rfl⟩,?_⟩
    change A.mulVec v+B.mulVec v=(A+B).mulVec v
    rw [Matrix.add_mulVec]
  have hr := Submodule.finrank_mono h
  have hs := Submodule.finrank_sup_add_finrank_inf_eq a b
  change Module.finrank K (LinearMap.range (A+B).mulVecLin)≤
    Module.finrank K a+Module.finrank K b
  omega

theorem rank_sum_le (s : Finset T) (A : T → Matrix X Y K) :
    (∑ j ∈ s, A j).rank≤∑ j ∈ s, (A j).rank := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj hi =>
    simp only [Finset.sum_insert hj]
    exact (rank_add_le _ _).trans (Nat.add_le_add_left hi _)

variable {O : Type*} [CommRing O] [IsDomain O] [IsLocalRing O]
variable [Algebra O K] [IsFractionRing O K] [Fintype T]

/-- A sum of possibly fractional block matrices that is congruent to
one integral target is itself an integral lift; the full residue rank
of that target implies a nonzero determinant over K. -/
theorem integral_sum_full_rank (π : O) (hz : IsLocalRing.residue O π=0)
    (target : Matrix X X O) (A : T → Matrix X X K)
    (full : (target.map (IsLocalRing.residue O)).det≠0)
    (agree : ∀ x y, ∃ e : O, algebraMap O K (target x y)-(∑ b, A b x y)=
      algebraMap O K (π*e)) :
    (∑ b, A b).rank=Fintype.card X := by
  choose e he using agree
  let integral : Matrix X X O := Matrix.of fun x y => target x y-π*e x y
  have hk : integral.map (algebraMap O K)=∑ b, A b := by
    ext x y
    have h:=he x y
    simp only [Matrix.map_apply,Matrix.of_apply,Matrix.sum_apply,integral,map_sub] at *
    linear_combination h
  have hr : integral.map (IsLocalRing.residue O)=target.map (IsLocalRing.residue O) := by
    ext x y
    simp [integral,hz]
  have hdet : integral.det≠0 := by
    intro h0
    have hm : (IsLocalRing.residue O) integral.det=(integral.map (IsLocalRing.residue O)).det :=
      RingHom.map_det (IsLocalRing.residue O) integral
    rw [h0,map_zero,hr] at hm
    exact full hm.symm
  have hdetK : (integral.map (algebraMap O K)).det≠0 := by
    have hm : algebraMap O K integral.det=(integral.map (algebraMap O K)).det :=
      RingHom.map_det (algebraMap O K) integral
    rw [← hm]
    exact (map_ne_zero_iff _ (IsFractionRing.injective O K)).mpr hdet
  rw [← hk]
  exact Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr hdetK))

theorem budget_of_square_blocks (π : O) (hz : IsLocalRing.residue O π=0)
    (target : Matrix X X O) (A : T → Matrix X X K) (bound : T → ℕ)
    (full : (target.map (IsLocalRing.residue O)).det≠0)
    (agree : ∀ x y, ∃ e : O, algebraMap O K (target x y)-(∑ b, A b x y)=
      algebraMap O K (π*e))
    (rankBlock : ∀ b, (A b).rank≤bound b) :
    Fintype.card X≤∑ b, min (Fintype.card X) (bound b) := by
  have h := integral_sum_full_rank π hz target A full agree
  exact h.ge.trans ((rank_sum_le Finset.univ A).trans (Finset.sum_le_sum fun b _ =>
    le_min (Matrix.rank_le_card_width (A b)) (rankBlock b)))

#print axioms rank_add_le
#print axioms rank_sum_le
#print axioms integral_sum_full_rank
#print axioms budget_of_square_blocks
end
end V8CapacityUnified.U7
