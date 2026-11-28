import J4R43LiteralOutsideWordSearch
import J4R43LiteralOutsideMeterReceive
import J4R43LiteralOutsideHammingRun

/-! On the actual positive slot no two legal integer candidates alias
at the original printed precision. The same p-bit search therefore
recovers the actual Hamming statistic, not only its residue. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R10Repack J6ActiveRun J6R12Blueprint J6R9Recursive
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N7LiteralSupport
open V8NativeMessage.N7HighBound A1R10 A1R12 AOracleMachineTime
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 7700000
set_option maxRecDepth 2200
set_option Elab.async false

theorem embed_base_retract (p : ℕ) (hp : 0<p)
    (f : ℤ[X]) (hf : f.Monic) (hd : 0<f.natDegree) (x : NativeProbeRing.Base p) :
    J6R15SignedRead.boxProject p f 1 hf (by decide) (embedBase p f x)=x := by
  exact J6R15SignedRead.boxProject_base p f 1 hf hp hd (by decide) x

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀ v,GraphCutMoments.degree F v=3)
variable {f : ℤ[X]}
local notation "S" => printedParams (f:=f) (ell:=1) (oldRowSize F)
local notation "a₀" => J6ActiveRun.Shape.levelBits S 0
local notation "root" => oldColumnRoot F reg f (fun _=>false)

theorem actual_positive_word_decodes_count (P : ColumnPacking F reg (f:=f)) {h : ℕ}
    (G : BandCertificate P h) (d : ColumnReady F reg (f:=f))
    (t : ColumnCenter F reg (f:=f)) (i : Fin a₀) (hv : padicValInt 2 t.val=i.val)
    (out : t.val=(((2^a₀:ℕ):ℤ)-1)) (hf : f.Monic) (hd : 0<f.natDegree) (σ : W→Bool)
    (seen init base : Word (registerPrecision S root t))
    (seenValue : originalOppositeSlot F reg P d t i hv 0 0 hf σ=
      embedBase (registerPrecision S root t) f (wordRead seen))
    (initValue : wordRead init=
      ((graphFactor F reg P t.val (J9FactorBounds.kernel (2^a₀)):ℤ):NativeProbeRing.Base (registerPrecision S root t)))
    (baseValue : wordRead base=
      ((1-J9FactorBounds.kernel (2^a₀):ℤ):NativeProbeRing.Base (registerPrecision S root t))) :
    let n := (hitPins F reg P t.val).card
    let run := nativeHammingWord seen base init (n+1)
    run.result=hitWeight F reg P t.val σ ∧
    run.steps≤(n+1)*(wordOpCap (registerPrecision S root t)+registerPrecision S root t+4) := by
  let p := registerPrecision S root t
  let n := (hitPins F reg P t.val).card
  let C := J9FactorBounds.kernel (2^a₀)
  let A := graphFactor F reg P t.val C
  let B : ℤ := 1-C
  let k := hitWeight F reg P t.val σ
  have hp : 0<p := register_positive d t
  have mk : 0<Fintype.card (DWire F) := (Nat.zero_le _).trans_lt d.active
  obtain ⟨Slot,_,pos,basePos⟩ := original_positive_extreme_is_integer F reg P G d t i hv out hf hd σ
  change originalOppositeSlot F reg P d t i hv 0 0 hf σ=(A*B^k:ℤ) at Slot
  have SV : wordRead seen=((A*B^k:ℤ):NativeProbeRing.Base p) := by
    have eq : embedBase p f (wordRead seen)=(A*B^k:ℤ) := seenValue.symm.trans Slot
    have q := congrArg (J6R15SignedRead.boxProject p f 1 hf (by decide)) eq
    rw [embed_base_retract p hp f hf hd,project_integer p hp f hf hd] at q
    exact q
  have bound (j : ℕ) (hj : j≤n) :
      |A*B^j|≤(2:ℤ)^(7*Fintype.card (DWire F)) := by
    have H : j≤(hitPins F reg P (((2^a₀:ℕ):ℤ)-1)).card := by
      change j≤(hitPins F reg P t.val).card at hj
      rwa [out] at hj
    have q := actual_positive_candidates_fit F reg P H
    change |graphFactor F reg P (((2^a₀:ℕ):ℤ)-1) C*(1-C)^j|≤_ at q
    simpa only [A,B,out] using q
  have hkn : k≤n := hamming_le_selected F reg P t.val σ
  refine ⟨native_hamming_word_correct seen base init (Nat.lt_succ_of_le hkn) ?_,
    native_hamming_word_fee hp seen base init (n+1)⟩
  intro j hj
  change wordRead seen=wordRead init*(wordRead base)^j ↔ j=k
  rw [SV,initValue,baseValue,←Int.cast_pow,←Int.cast_mul]
  change ((A*B^k:ℤ):NativeProbeRing.Base p)=((A*B^j:ℤ):NativeProbeRing.Base p) ↔ j=k
  constructor
  · intro eq
    have h := congrArg (embedBase p f) eq
    have E : ((A*B^k:ℤ):Residue f 1 p)=((A*B^j:ℤ):Residue f 1 p) := by
      simpa only [map_intCast] using h
    have L := actual_extreme_integer_lift F reg t mk hf hd (A*B^k) (bound k hkn)
    have R := actual_extreme_integer_lift F reg t mk hf hd (A*B^j) (bound j (Nat.lt_succ_iff.mp hj))
    have uncast : A*B^j=A*B^k :=
      R.symm.trans ((congrArg (centeredBox p f hf) E.symm).trans L)
    exact hamming_comparison_unique A B pos basePos uncast
  · intro same
    rw [same]

#print axioms embed_base_retract
#print axioms actual_positive_word_decodes_count
end
end J4R43LiteralOutside

