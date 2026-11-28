import A4R45NativeA6
import A4R45ZeroFallback

/-! A4 with the same physical P and the same signed center when the
installed binary probe list has omitted 0. The sampled completed replies
are exactly beta=0, and integer division follows exact nonnegative lift. -/
namespace A4R45OriginalFallback
open scoped Classical Polynomial
open Polynomial Acquisition DenominatorBudget J6R9Recursive J6R10Repack
open J6R10Integral J6R12Repack P11FullPacking AAcquisitionCost P1DyadicGrid
open A4R45LiteralNetwork A4R45LiteralTables A4R45NativeA6
open A4R45ZeroFallback J6R14ZeroMode
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3800000

noncomputable section
variable {E V₂ V₃ U C G : Type}
variable [Fintype E] [DecidableEq E] [Fintype V₂] [DecidableEq V₂]
variable [Fintype V₃] [DecidableEq V₃] [Fintype U] [DecidableEq U]
variable [Fintype C] [DecidableEq C] [LinearOrder G] [Fintype G] {a : ℕ}
local notation "WireType" => A4R45LiteralNetwork.Wire V₂ V₃ U
variable (P : PhysicalPacking (A4R45LiteralNetwork.network (V₂:=V₂) (V₃:=V₃) (U:=U)) a G)
variable (i : Fin a) (hi : i.val=0)
variable (f : ℤ[X]) (p₀ p : ℕ) (hf : f.Monic)
local notation "D" => J9PrintedSchedule.degreeBound (Fintype.card WireType) (2^a)

def noZeroSlot (W : Prescribed f D) : Residue f 1 p :=
  (J6ActiveInterpolation.decoded (prescribedNode W p 1) (fun j =>
    V8PooledMenu.slot P i (t:=(-1:ℤ)) (by decide) (by simp [hi]) p
      (box_two_nil p f 1) (prescribedNode W p 1 j) (sourceFile f p₀) hf 0)).eval 0

omit [DecidableEq V₂] [DecidableEq V₃] [DecidableEq U] in
theorem no_zero_recovers_same_original_slot (hp : 0<p) (hd : 0<f.natDegree)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))] (W : Prescribed f D) :
    noZeroSlot P i hi f p₀ p hf W = originalSlot P i hi f p₀ p hf := by
  have hgrid : (-1:ℤ)∈grid a := by
    rw [mem_grid]
    have h := pow₂_pos a
    omega
  exact same_completed_zero_mode_from_original_words P i (by decide : (-1:ℤ)≠0)
    (by simp [hi]) hgrid p hp (sourceFile f p₀) hf hd W

variable (seat : A4R45LiteralNetwork.Wire V₂ V₃ U ≃ Physical a P.copies G)
variable (same : ∀ w : A4R45LiteralNetwork.Wire V₂ V₃ U,P.seat w=seat w)
include same

theorem same_A4_count_from_original_nonzero_words
    (h₀ : 0<p₀) (hd : 0<f.natDegree) [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (W : Prescribed f D)
    (at₂ : V₂→Fin 2→E) (at₃ : V₃→Fin 3→E)
    (cols : Var V₂ V₃ U ≃ CoverCol E V₃ C)
    (planted : ∀ (r : CoverRow V₂ V₃ U) (j : CoverPort r),
      (wirePred seat (⟨r,j⟩,true)).map (cols ∘ Prod.fst) =
        coverSources at₂ at₃ (compiledStray seat cols) r j)
    (even : Even (Fintype.card V₃)) (hE : 2*Fintype.card E≤Fintype.card WireType)
    (hC : 2*Fintype.card C≤Fintype.card WireType) (hp : 2*Fintype.card WireType<p) :
    boxNatural f 1 p hf (noZeroSlot P i hi f p₀ p hf W) /
      publicFactor (compiledStray seat cols) = coverCount at₂ at₃ := by
  rw [no_zero_recovers_same_original_slot P i hi f p₀ p hf (by omega) hd W]
  exact actual_A6_integer_then_divide P i hi seat same f p₀ p hf hd h₀
    at₂ at₃ cols planted even hE hC hp

#print axioms no_zero_recovers_same_original_slot
#print axioms same_A4_count_from_original_nonzero_words
end
end A4R45OriginalFallback
