import V8NativeMessageN7LiteralSupportColumnRows
import V8NativeMessageN7LiteralSupportLocal

/-! At a negative genuine shift scalar the old-column orientation has
strictly positive rational zero-mode value for every sign word. This
lemma uses the same layout and all its real old column bits. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped Classical Polynomial BigOperators
open Polynomial J6R10Repack J6R9PacketTiles P11FullPacking
open Paper5.HybridClosure Paper5.D1Literal
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
set_option maxRecDepth 2000
noncomputable section

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀v,GraphCutMoments.degree F v=3)
local notation "E" => (DWire F)
local notation "D" => (MainClonedCNF.Port F)
variable {a : ℕ}
variable (P : PhysicalPacking (oldColumnNetwork F reg) a (Fin 64))

theorem literal_column_argument_is_zero_or_coefficient {R : Type} [CommRing R]
    (t : ℤ) (κ : R) (y : E→Bool) (r : E) :
    actualColumnArgument F reg P t κ y r=0 ∨ actualColumnArgument F reg P t κ y r=κ := by
  unfold actualColumnArgument
  by_cases present : ∃ q,Matches P t r q
  · obtain ⟨q,hq⟩ := present
    rw [literal_port_bit_unique P t _ r q hq]
    cases h : y q
    · left; simp [bit,h]
    · right; simp [bit,h]
  · left
    rw [literal_unmatched_port_zero P t _ r (fun q hq=>present ⟨q,hq⟩),mul_zero]

theorem actual_subdivision_positive {κ : ℚ} (negative : κ<0) (t : ℤ)
    (y : E→Bool) (q : D) :
    0<literalSubdivisionWeight F reg P t κ y q := by
  have H (r : E) : actualColumnArgument F reg P t κ y r≤0 := by
    rcases literal_column_argument_is_zero_or_coefficient F reg P t κ y r with h|h
    · rw [h]
    · simpa only [h] using negative.le
  exact actual_equality₂_positive (H (q,false)) (H (q,true))

theorem true_old_columns_strictly_positive {t : ℤ} (ht : t≠0)
    (i : Fin a) (hv : padicValInt 2 t=i.val)
    {κ : ℚ} (negative : κ<0) (σ : W→Bool) :
    0<signedRoot P i t κ (oldColumnTruth F reg σ) := by
  rw [full_root_at_zero_has_literal_two_cubes P i ht hv,actual_old_column_rows_summed]
  have pos (y : E→Bool) : 0<∏ q : D,literalSubdivisionWeight F reg P t κ y q :=
    Finset.prod_pos fun q _=>actual_subdivision_positive F reg P negative t y q
  apply Finset.sum_pos'
  · intro y _
    split
    · exact (pos y).le
    · rfl
  · refine ⟨columnWitness F σ,Finset.mem_univ _,?_⟩
    rw [if_pos (original_columns_have_joint_word F reg σ)]
    exact pos _

theorem every_actual_unit_subdivision_fits_seven (y : E→Bool) (q : D) :
    |literalSubdivisionWeight F reg P (-1) (-1:ℤ) y q|≤7 := by
  have h := literal_column_argument_is_zero_or_coefficient F reg P (-1) (-1:ℤ) y (q,false)
  have j := literal_column_argument_is_zero_or_coefficient F reg P (-1) (-1:ℤ) y (q,true)
  rcases h with h|h <;> rcases j with j|j <;>
    norm_num [literalSubdivisionWeight,equalityPair,h,j]

end
end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.literal_column_argument_is_zero_or_coefficient
#print axioms V8NativeMessage.N7LiteralSupport.actual_subdivision_positive
#print axioms V8NativeMessage.N7LiteralSupport.true_old_columns_strictly_positive
#print axioms V8NativeMessage.N7LiteralSupport.every_actual_unit_subdivision_fits_seven
