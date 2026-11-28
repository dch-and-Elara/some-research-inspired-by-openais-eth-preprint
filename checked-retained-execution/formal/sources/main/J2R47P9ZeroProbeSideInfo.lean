import J2R47P9ZeroProbe
import J2R47P9ZeroProbePublic

/-! Append the actually delivered full-precision zero probes as free
auxiliary queries to any witnessed source menu. Their native precision
tags are kept. Adaptive output and original paid-path cost are exact. -/
namespace J2R47P9ZeroProbe
open scoped Classical Polynomial BigOperators
open Polynomial J6R9Recursive J6R10Repack J6R12Blueprint
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N6D V8NativeMessage.N7
open FiniteWeightedQueryTree
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8000000
set_option maxRecDepth 2500
set_option Elab.async false
set_option linter.unusedSectionVars false
noncomputable section

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀v,GraphCutMoments.degree F v=3)
variable {f : ℤ[X]}
abbrev DeliveredZeroSlot (P : RootPacking F reg f) (d : N6PublicReady F reg (f:=f)) :=
  { x : PublicSlot F reg f P d // siteProbe F reg d x.1 x.2.1=0 }
abbrev FullZeroResponse :=
  Σ t : PublicCenter F reg f,Residue f 1 (sitePrecision F reg t)

def fixedZeroResponse (P : RootPacking F reg f) (d : N6PublicReady F reg (f:=f))
    (x : DeliveredZeroSlot F reg P d) : FullZeroResponse F reg (f:=f) :=
  ⟨x.val.1,0⟩

def actualZeroResponse (P : RootPacking F reg f) (d : N6PublicReady F reg (f:=f))
    (hf : f.Monic) (σ : W→Bool)
    (x : DeliveredZeroSlot F reg P d) : FullZeroResponse F reg (f:=f) :=
  ⟨x.val.1,wholePublic F reg P d hf σ x.val⟩

theorem literal_full_zero_response_is_public
    (P : RootPacking F reg f) (d : N6PublicReady F reg (f:=f))
    (positive negative : F) (reserve : Reserved F reg P positive negative)
    (hf : f.Monic) (hd : 0<f.natDegree) (σ : W→Bool) :
    actualZeroResponse F reg P d hf σ = fixedZeroResponse F reg P d := by
  funext x
  unfold actualZeroResponse fixedZeroResponse
  rw [reserved_endpoints_public_full_zero F reg P d positive negative reserve hf hd σ x.val x.property]

theorem actual_free_full_zero_exact
    (P : RootPacking F reg f) (d : N6PublicReady F reg (f:=f))
    (positive negative : F) (reserve : Reserved F reg P positive negative)
    (hf : f.Monic) (hd : 0<f.natDegree) (σ : W→Bool)
    {Q R : Type*} (oracle : Q→R) (bill : Q→ℕ)
    (tree : DecisionTree (Q⊕DeliveredZeroSlot F reg P d) (R⊕FullZeroResponse F reg (f:=f))) :
    evaluate (withPublic oracle (actualZeroResponse F reg P d hf σ)) tree =
      evaluate oracle (eliminatePublic (fixedZeroResponse F reg P d) tree) ∧
    paid (Sum.elim bill (fun _=>0))
      (withPublic oracle (actualZeroResponse F reg P d hf σ)) tree =
      paid bill oracle (eliminatePublic (fixedZeroResponse F reg P d) tree) := by
  rw [literal_full_zero_response_is_public F reg P d positive negative reserve hf hd σ]
  exact eliminatePublic_exact (fixedZeroResponse F reg P d) oracle bill tree

#print axioms literal_full_zero_response_is_public
#print axioms actual_free_full_zero_exact
end
end J2R47P9ZeroProbe

