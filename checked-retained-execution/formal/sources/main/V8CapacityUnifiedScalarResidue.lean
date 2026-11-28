import V8CapacityUnifiedScalarSharp

/-! The residue-field specialization of S3 has ordinary field rank
exactly H, not just chain-ring inner width. Empty messages give H=1. -/
namespace V8CapacityUnified.Scalar
open scoped Classical BigOperators
open V8CapacityDigits

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1100000

variable {H : Type*} [Fintype H]

theorem zero_messages_count [IsEmpty H] (q P : ℕ) (v : H → ℕ) (hp : 0<P) :
    Nat.card (S2Raw q P v)=1 := by
  let f : H → ℕ := fun i => isEmptyElim i
  let j : S2Raw q P v := ⟨f,by simpa [weight] using hp⟩
  let e : S2Raw q P v ≃ Unit :=
    {toFun := fun _ => (), invFun := fun _ => j,
     left_inv := fun _ => Subtype.ext (funext fun i => isEmptyElim i),
     right_inv := fun _ => rfl}
  exact (Nat.card_congr e).trans (by simp)

variable {O : Type*} [CommRing O] [IsDomain O] [IsLocalRing O]
variable {π : O} {q : ℕ} (D : Digits π q) (hq : 0<q)
variable (hq₂ : 2≤q) (h0 : D.d ⟨0,hq⟩=0) (hπ : π≠0)
variable (hMax : IsLocalRing.maximalIdeal O=Ideal.span ({π}:Set O))
variable (s : PublicClass (O:=O) (H:=H)) (L : ℕ)

local notation "I" => S2Index q (L+1) s.depth
local notation "G" => normalGrid D hq hq₂ h0 hπ s (L+1)
local notation "M" => S3_matrix D hq hq₂ h0 hπ s L 1
local notation "ρ" => IsLocalRing.residue O

theorem S3_same_normal_level_one : M=G := by
  ext r j
  change π^(weight q s.depth (indexDegree j)-L)*G r j=G r j
  have hj : weight q s.depth (indexDegree j)<L+1 := j.property
  rw [show weight q s.depth (indexDegree j)-L=0 from by omega,pow_zero,one_mul]

include hMax in
theorem S3_exact_residue_field_rank :
    (Matrix.map M ρ).rank=Nat.card (S2Raw q (L+1) s.depth) := by
  letI : DecidableEq I := Classical.decEq _
  rw [S3_same_normal_level_one D hq hq₂ h0 hπ s L,← s2_is_exact_count q (L+1) hq s.depth]
  obtain ⟨A,hA⟩ := grid_has_left D hq hq₂ h0 hπ s (L+1) hMax
  have hm : (A.map ρ)*(Matrix.map G ρ)=1 := by
    have e := congrArg (fun F : Matrix I I O => RingHom.mapMatrix ρ F) hA
    change RingHom.mapMatrix ρ (A*(G))=RingHom.mapMatrix ρ (1:Matrix I I O) at e
    rw [map_mul,map_one] at e
    exact e
  have h := Matrix.rank_mul_le_right (A.map ρ) (Matrix.map G ρ)
  rw [hm,Matrix.rank_one] at h
  exact le_antisymm (Matrix.rank_le_card_width _) h

#print axioms zero_messages_count
#print axioms S3_same_normal_level_one
#print axioms S3_exact_residue_field_rank
end
end V8CapacityUnified.Scalar
