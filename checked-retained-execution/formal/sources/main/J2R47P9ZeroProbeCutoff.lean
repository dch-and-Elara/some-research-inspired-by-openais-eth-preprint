import J2R47P9ZeroProbeJoint

/-! The complementary statement in the source audit: at an arbitrary
layout, a shortage of physical shifted port pairs leaves an actual OR
unsupported, without any special reservations or parity reduction. -/
namespace J2R47P9ZeroProbe
open scoped Classical Polynomial BigOperators
open Polynomial P11FullPacking J6R9Recursive J6R10Repack
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N6D V8NativeMessage.N7
open V8NativeMessage.N7LiteralSupport
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 9000000
set_option maxRecDepth 2400
set_option Elab.async false
set_option linter.unusedSectionVars false
noncomputable section

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀v,GraphCutMoments.degree F v=3)
local notation "N" => (dNetwork F reg)
local notation "E" => DWire F

theorem actual_finite_OR_cutoff {a : ℕ} (P : PhysicalPacking N a (Fin 64)) (t : ℤ)
    (strict : Nat.card (Page a P.copies (Fin 64))*(2^a-t.natAbs)<F.card) :
    ∃ e : F,∀ b,¬ ∃ q : E,Matches P t (sourceOrPort F e b) q := by
  classical
  by_contra no
  push_neg at no
  choose b q ok using no
  let choosePair (e : F) : Matching P t :=
    ⟨(sourceOrPort F e (b e),q e),ok e⟩
  have inj : Function.Injective choosePair := by
    intro e e' h
    have hh : sourceOrPort F e (b e)=sourceOrPort F e' (b e') :=
      congrArg (fun v : Matching P t=>v.val.1) h
    have hcol : originalOrColumn F e (b e)=originalOrColumn F e' (b e') :=
      congrArg Prod.fst hh
    exact congrArg Prod.fst (originalOrColumn_inj F hcol)
  have pairs := Nat.card_le_card_of_injective _ (matchEmbedding P t).injective
  rw [Nat.card_prod,Nat.card_fin] at pairs
  have masses := (Nat.card_le_card_of_injective choosePair inj).trans pairs
  have same : Nat.card F=F.card := by rw [Nat.card_eq_fintype_card,Fintype.card_coe]
  rw [same] at masses
  exact (not_le_of_gt strict) masses

theorem source_native_full_zero_from_OR_cutoff {f : ℤ[X]}
    (P : RootPacking F reg f) (d : N6PublicReady F reg (f:=f))
    (hf : f.Monic) (hd : 0<f.natDegree) (σ : W→Bool) (x : PublicSlot F reg f P d)
    (zeroProbe : siteProbe F reg d x.1 x.2.1=0)
    (strict : Nat.card (Page ((J6R12Blueprint.printedParams (f:=f) (ell:=1) (oldRowSize F)).levelBits 0)
        P.copies (Fin 64)) *
      (2^((J6R12Blueprint.printedParams (f:=f) (ell:=1) (oldRowSize F)).levelBits 0)
        -x.1.val.natAbs)<F.card) :
    wholePublic F reg P d hf σ x=0 := by
  obtain ⟨e,absent⟩ := actual_finite_OR_cutoff F reg P x.1.val strict
  exact literal_original_shiftless_or_excludes_every_sign F reg P d hf hd σ x zeroProbe e absent

#print axioms actual_finite_OR_cutoff
#print axioms source_native_full_zero_from_OR_cutoff
end
end J2R47P9ZeroProbe

