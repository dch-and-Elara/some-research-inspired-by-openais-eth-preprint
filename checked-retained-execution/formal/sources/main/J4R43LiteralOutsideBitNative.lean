import J4R43LiteralOutsideCodeCompile
import J4R43LiteralOutsideMeterReceive

/-! Same chart, same source register: actual p-bit arithmetic from
the two normalized native derivative words, and a true literal
bit-code for the original table marginalization. The raw signed
derivative preprocessing has a separate receipt; its bits are not
charged as though already resident by this theorem. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators Polynomial
open Polynomial P1DyadicGrid J6ActiveRun J6R12Blueprint J6ActiveSchedule
open J6R9Recursive J6R10Repack J6R9PacketCoeff
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N7LiteralSupport
open A1R10 A1R12 AOracleMachineTime
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 7600000
set_option maxRecDepth 2600
set_option Elab.async false

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀ v,GraphCutMoments.degree F v=3)
variable {f : ℤ[X]}
local notation "S" => printedParams (f:=f) (ell:=1) (oldRowSize F)
local notation "a₀" => J6ActiveRun.Shape.levelBits S 0
local notation "root" => oldColumnRoot F reg f (fun _=>false)
local notation "M" => Fintype.card (DWire F)
local notation "u₀" => J6ActiveRun.Shape.levelWidth S 0

theorem literal_native_bit_receipt (P : ColumnPacking F reg (f:=f)) {h : ℕ}
    (G : BandCertificate P h) (d : ColumnReady F reg (f:=f))
    (t : ColumnCenter F reg (f:=f)) (i : Fin a₀) (hv : padicValInt 2 t.val=i.val)
    (wide : 2^a₀-h≤t.val.natAbs) (hf : f.Monic) (hd : 0<f.natDegree) (σ : W→Bool)
    (n den : Word (registerPrecision S root t))
    (readN : wordRead n=((paidNormalizeUnit a₀ t.val).numerator:NativeProbeRing.Base (registerPrecision S root t)))
    (readD : wordRead den=((paidNormalizeUnit a₀ t.val).denominator:NativeProbeRing.Base (registerPrecision S root t))) :
    let p := registerPrecision S root t
    let positive := register_positive d t
    let k := ratioWord positive n den
    let run := runScalarCode positive k.result (originalOutsideCode F reg t.val σ P)
    originalOppositeSlot F reg P d t i hv 0 0 hf σ=embedBase p f (wordRead run.result) ∧
      k.steps+run.steps≤ratioWordCap p+(1+oldRowSize F*130)*codeStride p := by
  let p := registerPrecision S root t
  let positive : 0<p := register_positive d t
  let k := ratioWord positive n den
  let code := originalOutsideCode F reg t.val σ P
  let run := runScalarCode positive k.result code
  have m : t.val∈grid a₀ := (active_grid a₀ M u₀ t.property).1
  have kr := actual_word_unit positive m n den readN readD
  have fee := actual_code_cost positive k.result code
  have size := original_outside_code_size F reg t.val σ P
  have valid := outside_at_native_width F reg P G d t i hv wide hf hd σ
  have src := (actual_paid_source_unit a₀ m p (NativeProbeRing.base_nilpotent p)).1
  refine ⟨?_,Nat.add_le_add kr.2 (fee.trans (Nat.mul_le_mul_right _ size))⟩
  change originalOppositeSlot F reg P d t i hv 0 0 hf σ=embedBase p f (wordRead run.result)
  have rv := actual_code_read positive k.result code
  change wordRead run.result=code.denote (wordRead k.result) at rv
  have kv : wordRead k.result=(paidSourceUnit (R:=NativeProbeRing.Base p) a₀ t.val p).1 :=
    kr.1.trans src.symm
  have pay := measured_outside_exact F reg t.val (paidSourceUnit (R:=NativeProbeRing.Base p) a₀ t.val p).1 σ P
  have J := valid.1
  change originalOppositeSlot F reg P d t i hv 0 0 hf σ=
    embedBase p f (measuredOutsideValue F reg t.val (paidSourceUnit (R:=NativeProbeRing.Base p) a₀ t.val p).1 σ P).value at J
  rw [rv,kv,original_outside_code_value F reg t.val σ P,←pay]
  exact J

#print axioms literal_native_bit_receipt
end
end J4R43LiteralOutside

