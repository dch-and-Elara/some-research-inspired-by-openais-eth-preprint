import V8NativeMessageN5MultiMatrix
import V8NativeMessageN4OrdinaryEnd
import IntegralOutputTransfer

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 7600000
set_option maxRecDepth 4500

/-! The multi-coordinate whole-slot sum is reduced termwise with the
original precision at each term's own signed center. Its one common
terminal residue is the original four-copy count. -/
namespace V8NativeMessage.N5
open scoped Classical BigOperators Polynomial
open Paper5.D1Literal J6R9Recursive J6R10Repack N4 SeparatedRank
open V8NativeMessage.C3.Canonical
noncomputable section

variable {X : Type} [Fintype X] [DecidableEq X] {F : Finset (X×X)}
  {reg : ∀ v,GraphCutMoments.degree F v=3} {f : ℤ[X]}
  {P : RootPacking F reg f} {d : LayoutReady F reg f}
  [Fact (Irreducible (ratPoly f))]

variable {H I : Type*} [Fintype H] [Fintype I]
    {coordinate : H → rootKept F f} (Qs : ∀ h,OrdinaryQuery P d (coordinate h)) (hf : f.Monic)
variable (M : PinnedCNF.InducedMatching F I)

def RightMultiTerminal : Prop := ∀ τ : X→Bool,∃ total : IntRing f 1,
  (∑ h, weightedWhole (Qs h) hf τ)=embed f 1 total ∧
  reduce (4*Fintype.card X+1) f 1 total=(nativeCount F reg τ:Residue f 1 (4*Fintype.card X+1))

theorem same_multi_terminal
    (correct : RightMultiTerminal Qs hf) (σ : X→Bool) :
    ∃ total : IntRing f 1,
      sourceFieldMap f total=∑ h,sourceValue (ordinaryBlock (Qs h) hf) σ ∧
      reduce (4*Fintype.card X+1) f 1 total=(nativeCount F reg σ:Residue f 1 (4*Fintype.card X+1)) := by
  obtain ⟨a,ha,hr⟩ := correct σ
  obtain ⟨b,hb,hbρ⟩ := assemble_replacements hf (fun h => weightedWhole (Qs h) hf σ)
    (fun h => weightedSeparate (Qs h) hf σ) a ha
    (fun h => original_ordinary_term_safe (Qs h) hf σ)
  refine ⟨b,?_,hbρ.trans hr⟩
  have he := congrArg (zeroCoordinate (RatScalar f)) hb.symm
  change sourceFieldMap f b=zeroCoordinate (RatScalar f) (∑ h, weightedSeparate (Qs h) hf σ) at he
  rw [map_sum] at he
  simpa only [separate_is_block] using he

variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

theorem same_matching_target_rank (correct : RightMultiTerminal Qs hf) :
    (∑ h,mainMat M (ordinaryBlock (Qs h) hf)).rank=2^Fintype.card I := by
  choose a ha using same_multi_terminal Qs hf correct
  let A : Matrix (I→Bool) (I→Bool) (IntRing f 1) := Matrix.of fun x y=>a (M.restrictSigns x y)
  let modTwo := sourceModTwo f
  let lift := sourceFieldMap f
  have hA : lift.mapMatrix A=∑ h,mainMat M (ordinaryBlock (Qs h) hf) := by
    ext x y
    rw [Matrix.sum_apply]
    exact (ha (M.restrictSigns x y)).1
  have hZ : modTwo.mapMatrix A=M.countMatrix (NativeProbeRing.Residue f) := by
    ext x y
    change modTwo (a (M.restrictSigns x y))=
      (PinnedCNF.modelCount (PinnedCNF.formula F (M.restrictSigns x y)):NativeProbeRing.Residue f)
    have hz := mod_two_of_count_at_creation f hf (ha (M.restrictSigns x y)).2
    simpa only [nativeCount,MainClonedCNF.modelCount_cloned] using hz
  rw [← hA]
  have he := IntegralOutputTransfer.full_rank_of_residue lift modTwo
    (sourceFieldMap_injective f hf) A (M.countMatrix (NativeProbeRing.Residue f)) hZ
    (M.countMatrix_det_isUnit (NativeProbeRing.Residue f)).ne_zero
  simpa only [Fintype.card_fun,Fintype.card_bool] using he

omit [Fintype X] in
theorem imbalance_le_word (U : Finset X) : endpointImbalance M.endpoint U≤Fintype.card I := by
  have a := Finset.card_le_univ (endpointPart M.endpoint U false)
  have b := Finset.card_le_univ (endpointPart M.endpoint U true)
  dsimp [endpointImbalance]
  omega

theorem original_multi_coordinate_N4
    (correct : RightMultiTerminal Qs hf)
    (symbols : rootKept F f→Finset (Fin 64)) (gap : ℕ)
    (fit : gap≤Fintype.card I)
    (simultaneous : ∀ h,gap≤endpointImbalance M.endpoint
      (EmpiricalCutMoments.labelCut (rootLabels F reg f P) id symbols (coordinate h))) :
    2^gap≤∑ h,(Qs h).order*∏ g,(Qs h).pointList.count g := by
  let bound := fun h => (Qs h).order*∏ g,(Qs h).pointList.count g
  have hrank := same_matching_target_rank Qs hf M correct
  have h : 2^Fintype.card I≤(∑ h,bound h)*2^(Fintype.card I-gap) := by
    rw [←hrank,Finset.sum_mul]
    apply (V8CapacityUnified.U7.rank_sum_le Finset.univ _).trans
    refine Finset.sum_le_sum (fun h _=>?_ )
    exact mixed_deficit_rank M (ordinaryBlock (Qs h) hf) symbols gap (simultaneous h)
  rw [show (2:ℕ)^Fintype.card I=2^gap*2^(Fintype.card I-gap) by
    rw [←pow_add,Nat.add_sub_of_le fit]] at h
  exact Nat.le_of_mul_le_mul_right h (pow_pos (by decide) _)

#print axioms same_multi_terminal
#print axioms same_matching_target_rank
#print axioms imbalance_le_word
#print axioms original_multi_coordinate_N4
end
end V8NativeMessage.N5