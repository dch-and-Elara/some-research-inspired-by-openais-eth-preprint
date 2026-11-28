import V8NativeMessageN4RawPrecision

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5500000

/-! The abstract local N4 child factors can be the actual separate
high-precision lifts from D1's recursively generated public reply. -/
namespace V8NativeMessage.N4
open scoped Classical BigOperators Polynomial
open Paper5.D1Literal Paper5.HybridClosure J6R12Blueprint J6ActiveRun J6R9Recursive J1PPrinted
noncomputable section

variable {W : Type} [Fintype W] [DecidableEq W] {F : Finset (W×W)}
  {reg : ∀ v, GraphCutMoments.degree F v=3} {f : ℤ[X]} {P : RootPacking F reg f}
variable (d : LayoutReady F reg f) (hf : f.Monic) (slot : PublicSlot F reg f P d)

def literalFactors : LocalFactors P (atCenter d slot.1) (RatScalar f) :=
  (agendaGroupTerm F reg f P d hf slot).factor

theorem literal_weighted_separate_slot (σ : W→Bool) :
    (agendaGroupTerm F reg f P d hf slot).coeff * nativeD (literalFactors d hf slot) σ =
      zeroCoordinate (RatScalar f) (publicTerm F reg f P d hf σ slot) :=
  agendaGroupTerm_value F reg f P d hf slot σ

theorem literal_separate_is_raw (σ : W→Bool) :
    nativeD (literalFactors d hf slot) σ = sourceFieldMap f (rawSeparate d hf slot σ) := by
  unfold nativeD rawSeparate
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro g _
  unfold literalFactors agendaGroupTerm receiveChild
  apply congrArg (fun b => sourceFieldMap f (representative _ f 1 b))
  apply publicReply_local
  intro v
  simp only [extendSign,dif_pos v.property]

#print axioms literal_weighted_separate_slot
#print axioms literal_separate_is_raw
end
end V8NativeMessage.N4
