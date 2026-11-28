import A4R45LiteralValue
import V8NativeMessageN7LiteralSupportZero
import V8NativeMessageN7LiteralSupportSigned
import J6R12RepackReadNatural

/-! The A6 product is the value of the single actual signed completed
slot at the original legal zero probe, with literal binary source entries.
Integer division follows the bounded lift, not division by a nonunit in
the receiving ring. -/
namespace A4R45NativeA6
open scoped BigOperators Polynomial Classical
open Polynomial Acquisition DenominatorBudget J6R9Recursive J6R10Repack
open J6R10Integral J6R11Integral J6R12Repack P11FullPacking AAcquisitionCost
open A4R45LiteralNetwork A4R45LiteralTables A4R45LiteralValue V8NativeMessage.N7LiteralSupport
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3300000

noncomputable section
variable {E V₂ V₃ U C G : Type}
variable [Fintype E] [DecidableEq E] [Fintype V₂] [DecidableEq V₂]
variable [Fintype V₃] [DecidableEq V₃] [Fintype U] [DecidableEq U]
variable [Fintype C] [DecidableEq C] [LinearOrder G] [Fintype G] {a : ℕ}
local notation "W" => Wire V₂ V₃ U
local notation "N" => network (V₂:=V₂) (V₃:=V₃) (U:=U)
variable (P : PhysicalPacking (A4R45LiteralNetwork.network (V₂:=V₂) (V₃:=V₃) (U:=U)) a G) (i : Fin a) (hi : i.val=0)
variable (seat : A4R45LiteralNetwork.Wire V₂ V₃ U ≃ Physical a P.copies G) (same : ∀ w : A4R45LiteralNetwork.Wire V₂ V₃ U,P.seat w=seat w)
variable (f : ℤ[X]) (p₀ p : ℕ) (hf : f.Monic) (hd : 0<f.natDegree)

def originalSlot : Residue f 1 p :=
  V8PooledMenu.slot P i (t:=(-1:ℤ)) (by decide) (by simp [hi]) p
    (box_two_nil p f 1) 0 (sourceFile f p₀) hf 0

include same hd

omit [DecidableEq E] [DecidableEq C] in
/-- The polynomial/block-normalization and the two-cube proof refer to the
same actual P, not a shift-permutation of another certified input. -/
theorem actual_slot_equals_literal_register (h₀ : 0<p₀)
    (cols : Var V₂ V₃ U ≃ CoverCol E V₃ C) :
    originalSlot P i hi f p₀ p hf =
      literalShiftedRegister (coverTables (K:=Residue f 1 p)) cols (wirePred seat) := by
  have hval : padicValInt 2 (-1)=i.val := by simp [hi]
  have ht : (-1:ℤ)≠0 := by decide
  let R := Residue f 1 p
  let h : TwoLocal→+*R := J6ZeroTransport.reduceAt p (box_two_nil p f 1)
  change V8PooledMenu.slot P i ht hval p (box_two_nil p f 1) 0
      (V8PooledMenu.binaryFile f p₀ trueFlags) hf 0 = _
  rw [actual_zero_slot_is_reduction P i ht hval trueFlags p₀ p h₀ hf hd]
  change h ((V8PooledMenu.wholeScaled P i (-1) trueFlags).eval 0) = _
  rw [full_signed_root_is_zero_polynomial P i (-1) trueFlags, map_signed_root,
    rho_at_actual_unit_shift, map_neg, map_one,
    full_root_at_zero_has_literal_two_cubes P i ht hval]
  exact native_flat_eq_literal_predecessor P seat same cols

theorem actual_A6_in_native_ring (h₀ : 0<p₀)
    (at₂ : V₂→Fin 2→E) (at₃ : V₃→Fin 3→E) (stray : U→Option C)
    (cols : Var V₂ V₃ U ≃ CoverCol E V₃ C)
    (planted : ∀ (r : CoverRow V₂ V₃ U) (j : CoverPort r),
      (wirePred seat (⟨r,j⟩,true)).map (cols ∘ Prod.fst) = coverSources at₂ at₃ stray r j)
    (even : Even (Fintype.card V₃)) :
    originalSlot P i hi f p₀ p hf =
      (coverCount at₂ at₃ * publicFactor stray : ℕ) := by
  rw [actual_slot_equals_literal_register P i hi seat same f p₀ p hf hd h₀ cols]
  exact literalCoverRegister_eq at₂ at₃ stray cols (wirePred seat) planted even

theorem actual_A6_integer_then_divide (h₀ : 0<p₀)
    (at₂ : V₂→Fin 2→E) (at₃ : V₃→Fin 3→E)
    (cols : Var V₂ V₃ U ≃ CoverCol E V₃ C)
    (planted : ∀ (r : CoverRow V₂ V₃ U) (j : CoverPort r),
      (wirePred seat (⟨r,j⟩,true)).map (cols ∘ Prod.fst) =
        coverSources at₂ at₃ (compiledStray seat cols) r j)
    (even : Even (Fintype.card V₃)) (hE : 2*Fintype.card E≤Fintype.card W)
    (hC : 2*Fintype.card C≤Fintype.card W) (hp : 2*Fintype.card W<p) :
    boxNatural f 1 p hf (originalSlot P i hi f p₀ p hf) /
      publicFactor (compiledStray seat cols) = coverCount at₂ at₃ := by
  rw [actual_A6_in_native_ring P i hi seat same f p₀ p hf hd h₀ at₂ at₃
    (compiledStray seat cols) cols planted even]
  rw [boxNatural_of_nat f 1 p hf (by omega) (by decide) hd _
      (literalCover_precision at₂ at₃ _ (compiledStray_load_le seat cols) hE hC hp)]
  exact Nat.mul_div_cancel _ (publicFactor_pos _)

#print axioms actual_slot_equals_literal_register
#print axioms actual_A6_in_native_ring
#print axioms actual_A6_integer_then_divide
end
end A4R45NativeA6
