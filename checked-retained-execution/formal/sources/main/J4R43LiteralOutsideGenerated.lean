import J4R43LiteralOutsideBitNative
import J4R43LiteralOutsideUnitSeedWords
import J4R43LiteralOutsideRawGrid

/-! Complete scalar acquisition for the fixed-band literal evaluator:
enumerate the two true source derivative tapes, strip their common
even content, build fixed-width words, and run the original old-column
marginals. Raw signed integer ops and graph addressing are reported
separately from the finite-word arithmetic primitive table. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators Polynomial
open Polynomial P1DyadicGrid J6ActiveRun J6R12Blueprint J6ActiveSchedule
open J6R9Recursive J6R10Repack J6R9PacketCoeff
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N7LiteralSupport
open A1R10 A1R12 AOracleMachineTime
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 7800000
set_option maxRecDepth 2600
set_option Elab.async false

def generatedNormWords (p : ℕ) (hp : 0<p) (a : ℕ) (t : ℤ) :
    Meter (Word p) × Meter (Word p) :=
  let uv := explicitNormalizeUnit a t
  (signedFixedWord hp (derivativeWidth a+1) uv.numerator,
   signedFixedWord hp (derivativeWidth a+1) uv.denominator)

theorem generated_words_are_native (p a : ℕ) (hp : 0<p) {t : ℤ} (mem : t∈grid a) :
    generatedNormWords p hp a t=originalNormWords p hp a t := by
  unfold generatedNormWords originalNormWords
  rw [explicit_normalize_is_native a mem]

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀ v,GraphCutMoments.degree F v=3)
variable {f : ℤ[X]}
local notation "S" => printedParams (f:=f) (ell:=1) (oldRowSize F)
local notation "a₀" => J6ActiveRun.Shape.levelBits S 0
local notation "root" => oldColumnRoot F reg f (fun _=>false)
local notation "M" => Fintype.card (DWire F)
local notation "u₀" => J6ActiveRun.Shape.levelWidth S 0

def runGeneratedJ4 (P : ColumnPacking F reg (f:=f))
    (d : ColumnReady F reg (f:=f)) (t : ColumnCenter F reg (f:=f)) (σ : W→Bool) :
    Meter (Word (registerPrecision S root t)) :=
  let p := registerPrecision S root t
  let pp := register_positive d t
  let seed := generatedNormWords p pp a₀ t.val
  let k := ratioWord pp seed.1.result seed.2.result
  let run := runScalarCode pp k.result (originalOutsideCode F reg t.val σ P)
  ⟨run.result,seed.1.steps+seed.2.steps+k.steps+run.steps⟩

theorem literal_generated_no_free_unit (P : ColumnPacking F reg (f:=f)) {h : ℕ}
    (G : BandCertificate P h) (d : ColumnReady F reg (f:=f))
    (t : ColumnCenter F reg (f:=f)) (i : Fin a₀) (hv : padicValInt 2 t.val=i.val)
    (wide : 2^a₀-h≤t.val.natAbs) (hf : f.Monic) (hd : 0<f.natDegree) (σ : W→Bool) :
    let p := registerPrecision S root t
    let out := runGeneratedJ4 F reg P d t σ
    originalOppositeSlot F reg P d t i hv 0 0 hf σ=embedBase p f (wordRead out.result) ∧
      out.steps≤38*p+12+ratioWordCap p+(1+oldRowSize F*130)*codeStride p ∧
      (orderedDerivative a₀ t.val).length+(orderedDerivative a₀ 0).length=2*(2*2^a₀-1) ∧
      (explicitNormalizeUnit a₀ t.val).shifts≤2*derivativeWidth a₀ ∧
      (explicitNormalizeUnit a₀ t.val).tests≤derivativeWidth a₀ := by
  let p := registerPrecision S root t
  let pp : 0<p := register_positive d t
  have mem : t.val∈grid a₀ := (active_grid a₀ M u₀ t.property).1
  let seed := originalNormWords p pp a₀ t.val
  let k := ratioWord pp seed.1.result seed.2.result
  let r := runScalarCode pp k.result (originalOutsideCode F reg t.val σ P)
  have H := actual_source_norm_words p pp a₀ mem
  have EQ := literal_native_bit_receipt F reg P G d t i hv wide hf hd σ seed.1.result seed.2.result H.1 H.2.1
  have same := generated_words_are_native p a₀ pp mem
  have normCaps := normalized_unit_is_original a₀ mem
  dsimp only [runGeneratedJ4]
  rw [same]
  refine ⟨EQ.1,?_,?_,?_,?_⟩
  · change seed.1.steps+seed.2.steps+k.steps+r.steps≤_
    have fs : seed.1.steps+seed.2.steps≤38*p+12 := H.2.2
    have fr : k.steps+r.steps≤ratioWordCap p+(1+oldRowSize F*130)*codeStride p := EQ.2
    simpa only [Nat.add_assoc] using Nat.add_le_add fs fr
  · rw [ordered_derivative_len a₀ mem,ordered_derivative_len a₀ (zero_mem_grid a₀)]
    omega
  · rw [explicit_normalize_is_native a₀ mem]
    exact normCaps.2.2.1
  · rw [explicit_normalize_is_native a₀ mem]
    exact normCaps.2.2.2

#print axioms generated_words_are_native
#print axioms literal_generated_no_free_unit
end
end J4R43LiteralOutside

