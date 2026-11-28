import V8NativeMessageN7Public

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2700000

/-! The coefficient polynomial of the actual original old-row high
zero slot. Truncation only changes the received word; its native
address, probe, original pin tables and creation precision are fixed. -/
namespace V8NativeMessage.N8Literal
open scoped Classical BigOperators Polynomial
open Polynomial DenominatorBudget P11FullPacking J6R10Repack J6R9Recursive
open J6ActiveRun J6R12Blueprint J6R9PacketScopes
open Paper5.D1Literal Paper5.HybridClosure V8NativeMessage.N6D V8NativeMessage.N7

noncomputable section
variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀v,GraphCutMoments.degree F v=3)
variable {f : ℤ[X]}
variable (P : RootPacking F reg f) (d : N6PublicReady F reg (f:=f))

theorem original_zero_sample_polynomial {R : Type*} [CommRing R]
    (hf : f.Monic) (hd : 0<f.natDegree) (σ : W→Bool) (x : PublicSlot F reg f P d)
    (hzero : x.2.2.val=0) (ψ : Residue f 1 (sitePrecision F reg x.1)→+*R) :
    ψ (wholePublic F reg P d hf σ x) =
      (V8PooledMenu.wholeScaled P (PublicIndex F reg f d x.1) x.1.val
        (oldRowTruth F reg σ)).eval₂
      (ψ.comp (J6ZeroTransport.reduceAt (sitePrecision F reg x.1)
        (J6R10Integral.box_two_nil (sitePrecision F reg x.1) f 1))) (2*ψ (siteProbe F reg d x.1 x.2.1)) := by
  rw [publicSlot_is_literal,hzero,V8PooledMenu.projected_zero_slot]
  have pos : 0<4*Fintype.card W+1 := by omega
  exact (V8PooledMenu.wholeScaled_eval P (PublicIndex F reg f d x.1) x.1.val
    (oldRowTruth F reg σ) (4*Fintype.card W+1) pos hf hd (sitePrecision F reg x.1)
    (J6R10Integral.box_two_nil (sitePrecision F reg x.1) f 1)
    (siteProbe F reg d x.1 x.2.1) ψ).symm

#print axioms original_zero_sample_polynomial
end
end V8NativeMessage.N8Literal
