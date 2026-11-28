import V8NativeMessageN6DFull
import P5D1LiteralResponse

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 780000
set_option maxRecDepth 2400

/-! The actual printed graph-fixed address carrier for N6 D. -/
namespace V8NativeMessage.N6D
open scoped Classical BigOperators Polynomial
open Polynomial J6R10Repack J6R11Blueprint J6ActiveRun J6R12Blueprint J6R10Reachable
open J6R9Recursive P11FullPacking Paper5.HybridClosure Paper5.D1Literal J1PPrinted J6R12Integral
noncomputable section

section Native
variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀ v, GraphCutMoments.degree F v=3)
variable {f : ℤ[X]}
local notation "S" => (printedParams (f:=f) (ell:=1) (oldRowSize F))
local notation "Δ" => sourceDelta (oldRowSize F)
local notation "r*" => (oldRowRoot F reg f (fun _ => false))

abbrev N6PublicReady := Ready S Δ r*

variable (P : RootPacking F reg f) (d : N6PublicReady F reg (f:=f))

theorem public_word_is_literal (hf : f.Monic) (q : PublicAddress F reg f P d) (σ : W→Bool) :
    let p := registerPrecision S r* q.1
    publicReply F reg f P d hf σ q =
      reduce p f 1 ((actualPacketHost P (PublicIndex F reg f d q.1) (centerNonzero q.1) rfl
        p (J6R10Integral.box_two_nil p f 1) (sampleNode S f 1 r* d.fit q.1 q.2.1)
        (oldRowFile F reg f (4*Fintype.card W+1) σ) q.2.2.1.val q.2.2.2).contract hf) := rfl

#print axioms public_word_is_literal

end Native

section FourClone
variable {V : Type} [Fintype V] [DecidableEq V]
variable (E : Finset (V×V)) (baseCubic : ∀ v, GraphCutMoments.degree E v=3)
variable (loopless : ∀ v,(v,v)∉E)
variable {F : Finset (TriVertex V × TriVertex V)} {reg : ∀ v,GraphCutMoments.degree F v=3}
variable {f : ℤ[X]} (hf : f.Monic)
local notation "S" => (printedParams (f:=f) (ell:=1) (oldRowSize F))
local notation "r*" => (oldRowRoot F reg f (fun _ => false))
variable (P : RootPacking F reg f) (d : N6PublicReady F reg (f:=f))

include loopless in
set_option maxHeartbeats 4000000 in
theorem printed_public_product_colocation [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (same : F=replacedEdges E baseCubic) (q : PublicSlot F reg f P d)
    (correct : ∀ σ, (∏ g : Fin 64,
      parityOfWord f hf (registerPrecision S r* q.1)
        (publicReply F reg f P d hf σ ⟨q.1,q.2.1,q.2.2,g⟩)) =
          UD E baseCubic (NativeProbeRing.Residue f) σ) :
    ∀ e : E, pinOwner F reg P (PublicIndex F reg f d q.1) (seat E baseCubic e false)=
      pinOwner F reg P (PublicIndex F reg f d q.1) (seat E baseCubic e true) := by
  subst F
  let G := replacedEdges E baseCubic
  let i := PublicIndex G reg f d q.1
  let p := registerPrecision (printedParams (f:=f) (ell:=1) (oldRowSize G))
    (oldRowRoot G reg f (fun _=>false)) q.1
  let z := sampleNode (printedParams (f:=f) (ell:=1) (oldRowSize G)) f 1
    (oldRowRoot G reg f (fun _=>false)) d.fit q.1 q.2.1
  refine actual_full_product_colocation E baseCubic loopless P i hf (centerNonzero q.1) rfl p z q.2.2 ?_
  intro σ
  exact correct σ

#print axioms printed_public_product_colocation

end FourClone
end
end V8NativeMessage.N6D
