import V8NativeMessageN4OrdinaryTerms
import V8NativeMessageN4Residue

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 9500000
set_option maxRecDepth 4500

/-! The original printed ordinary weighted whole-slot sums really
descend to the separate child rank model, on the same fixed D1
coordinate and the true four-copy terminal count. -/
namespace V8NativeMessage.N4
open scoped Classical BigOperators Polynomial
open Polynomial Paper5.D1Literal J6R9Recursive J6R10Repack
open V8NativeMessage.C3.NativeAssembly.MainScan V8NativeMessage.C3.Hermite
noncomputable section

theorem shrink_self (J : ℕ) (z : Jet J) :
    shrink (k:=J) (J:=J) le_rfl z=z := by
  obtain ⟨p,rfl⟩ := AdjoinRoot.mk_surjective z
  rw [shrink,AdjoinRoot.algHomOfDvd,AdjoinRoot.liftHom_mk,AdjoinRoot.aeval_eq]

variable {W : Type} [Fintype W] [DecidableEq W] {F : Finset (W×W)}
  {reg : ∀ v, GraphCutMoments.degree F v=3} {f : ℤ[X]}
  {P : RootPacking F reg f} {d : LayoutReady F reg f} {i : rootKept F f}

theorem nativeD_reindex {i' : rootKept F f} {R : Type*} [CommMonoid R]
    (e : i'=i) (D : LocalFactors P i' R) (σ : W→Bool) :
    nativeD (e ▸ D) σ=nativeD D σ := by
  subst i'
  rfl

variable [Fact (Irreducible (ratPoly f))]
variable (B : OrdinaryQuery P d i) (hf : f.Monic)

def ordinaryBlock : Block P i (RatScalar f) where
  groups := B.groups
  nodes := B.nodes
  order := B.order
  kept := B.order
  tuple := B.tuple
  accepted := B.accepted
  points := B.pointList
  keep := le_rfl
  read := (Algebra.linearMap ℚ (RatScalar f)).comp
    (jetNodeLinear B.nodes B.order (B.tuple.node.val+1))
  coefficient := zeroCoordinate (RatScalar f) (ordinaryD B)
  dFactors := B.sameCoordinate ▸ literalFactors d hf B.slot

theorem separate_is_block (σ : W→Bool) :
    sourceValue (ordinaryBlock B hf) σ=zeroCoordinate (RatScalar f) (weightedSeparate B hf σ) := by
  rw [weightedSeparate,map_mul,map_mul,ordinaryM,RingHom.map_rat_algebraMap]
  simp only [sourceValue,mainValue,ordinaryBlock,LinearMap.comp_apply,Algebra.linearMap_apply,shrink_self]
  have hd := nativeD_reindex (P:=P) B.sameCoordinate (literalFactors d hf B.slot) σ
  have hraw := literal_separate_is_raw d hf B.slot σ
  rw [hd,hraw]
  rfl

variable {A : Type*} [Field A] [LinearOrder A] {γ : A} (C : FourCut P i γ)
variable {H : Type*} [Fintype H] (Qs : H→OrdinaryQuery P d i)

include hf in
theorem original_whole_slot_N4 [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (correct : ∀ σ : W→Bool, ∃ total : IntRing f 1,
      (∑ h, weightedWhole (Qs h) hf σ)=embed f 1 total ∧
      reduce (4*Fintype.card W+1) f 1 total=(nativeCount F reg σ:Residue f 1 (4*Fintype.card W+1))) :
    2^C.m≤∑ h, (Qs h).order*∏ g, (Qs h).pointList.count g := by
  let B₀ := fun h => ordinaryBlock (Qs h) hf
  let zeroBypass : (W→Bool)→RatScalar f := fun _=>0
  have hcorrect (σ : W→Bool) : ∃ o : IntRing f 1,
      sourceFieldMap f o=(∑ h, sourceValue (B₀ h) σ)+zeroBypass σ ∧
      reduce (4*Fintype.card W+1) f 1 o=(nativeCount F reg σ:Residue f 1 (4*Fintype.card W+1)) := by
    obtain ⟨a,ha,hr⟩ := correct σ
    obtain ⟨b,hb,hbρ⟩ := original_ordinary_assembly_safe hf Qs σ a ha
    refine ⟨b,?_,hbρ.trans hr⟩
    have he := congrArg (zeroCoordinate (RatScalar f)) hb.symm
    change sourceFieldMap f b=zeroCoordinate (RatScalar f)
      (∑ h, weightedSeparate (Qs h) hf σ) at he
    rw [map_sum] at he
    simp only [zeroBypass,add_zero,B₀,separate_is_block,he]
  have bound := N4_at_actual_terminal C hf B₀ zeroBypass hcorrect
  have hz : bypassMatrix C zeroBypass=(0:Matrix (Fin C.m→Bool) (Fin C.m→Bool) (RatScalar f)) := by
    ext x y
    rfl
  rw [hz,Matrix.rank_zero,Nat.add_zero] at bound
  exact bound

#print axioms shrink_self
#print axioms nativeD_reindex
#print axioms separate_is_block
#print axioms original_whole_slot_N4
end
end V8NativeMessage.N4
