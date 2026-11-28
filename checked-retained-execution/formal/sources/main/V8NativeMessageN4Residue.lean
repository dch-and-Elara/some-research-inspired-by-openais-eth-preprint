import V8NativeMessageN4Assembly
import V8NativeMessageN4LiteralD
import P5D1LiteralRank

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5900000

/-! The original residue is the finite extension defined by the actual
probe polynomial, not homomorphically squeezed to F₂. Invertibility
of the original OR tensor holds over any nontrivial residue ring. -/
namespace V8NativeMessage.N4
open scoped Classical BigOperators Polynomial
open V8CapacityUnified.U7 Paper5.D1Literal J6R9Recursive J6R10Repack
noncomputable section

variable {W : Type} [Fintype W] [DecidableEq W] {F : Finset (W×W)}
  {reg : ∀ v, GraphCutMoments.degree F v=3} {f : ℤ[X]}
  {P : RootPacking F reg f} {i : rootKept F f}
  {A : Type*} [Field A] [LinearOrder A] {γ : A}
  (C : FourCut P i γ)
variable {R O Z : Type*} [Field R] [CommRing O] [CommRing Z] [Nontrivial Z]
variable (lift : O→+*R) (red : O→+*Z) (hinj : Function.Injective lift)

include hinj in
theorem actual_residue_rank (M : Matrix (Fin C.m→Bool) (Fin C.m→Bool) R)
    (correct : ∀ x y, ∃ o : O, lift o=M x y ∧
      red o=(nativeCount F reg (restriction C.pairs x y):Z)) :
    M.rank=2^C.m := by
  choose a ha using correct
  let B : Matrix (Fin C.m→Bool) (Fin C.m→Bool) O := Matrix.of a
  have hR : B.map lift=M := by ext x y; exact (ha x y).1
  have hZ : B.map red=matchingTarget Z C.m := by
    ext x y
    exact (ha x y).2.trans (literal_count_scalar C.pairs x y)
  have hdZ : red B.det≠0 := by
    have e : red B.det=(B.map red).det := RingHom.map_det red B
    rw [e,hZ]
    exact matching_det_ne_zero Z C.m
  have hdB : B.det≠0 := fun h => hdZ (by rw [h,map_zero])
  have hd : M.det≠0 := by
    have e : lift B.det=(B.map lift).det := RingHom.map_det lift B
    rw [← hR,← e]
    exact (map_ne_zero_iff _ hinj).mpr hdB
  rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr hd))]
  simp

variable {H : Type*} [Fintype H] [Algebra ℚ R] (B : H→Block P i R)

include hinj in
theorem N4_for_true_residue (bypass : (W→Bool)→R)
    (correct : ∀ σ : W→Bool, ∃ o : O, lift o=(∑ h, sourceValue (B h) σ)+bypass σ ∧
      red o=(nativeCount F reg σ:Z)) :
    2^C.m≤(∑ h,privateCapacity (B h))+(bypassMatrix C bypass).rank := by
  let M := (∑ h, blockMatrix C (B h))+bypassMatrix C bypass
  have hM : M.rank=2^C.m := by
    apply actual_residue_rank C lift red hinj M
    intro x y
    simpa only [M,Matrix.add_apply,Matrix.sum_apply,blockMatrix,bypassMatrix,Matrix.of_apply] using
      correct (restriction C.pairs x y)
  rw [← hM]
  apply (rank_add_le _ _).trans
  apply Nat.add_le_add_right
  exact (rank_sum_le Finset.univ _).trans (Finset.sum_le_sum (fun h _ => actual_block_rank C (B h)))

section Literal
variable [Fact (Irreducible (ratPoly f))] [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (hf : f.Monic) (B₀ : H→Block P i (RatScalar f))

include hf in
theorem N4_at_actual_terminal
    (bypass : (W→Bool)→RatScalar f)
    (correct : ∀ σ : W→Bool, ∃ o : IntRing f 1,
      sourceFieldMap f o=(∑ h, sourceValue (B₀ h) σ)+bypass σ ∧
      reduce (4*Fintype.card W+1) f 1 o=(nativeCount F reg σ:Residue f 1 (4*Fintype.card W+1))) :
    2^C.m≤(∑ h,privateCapacity (B₀ h))+(bypassMatrix C bypass).rank := by
  apply N4_for_true_residue C (sourceFieldMap f) (sourceModTwo f) (sourceFieldMap_injective f hf) B₀ bypass
  intro σ
  obtain ⟨o,h₀,h₁⟩ := correct σ
  exact ⟨o,h₀,mod_two_of_count_at_creation f hf h₁⟩

end Literal

#print axioms actual_residue_rank
#print axioms N4_for_true_residue
#print axioms N4_at_actual_terminal
end
end V8NativeMessage.N4
