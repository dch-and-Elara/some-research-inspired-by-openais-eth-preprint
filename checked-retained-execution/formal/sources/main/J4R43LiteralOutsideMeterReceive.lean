import J4R43LiteralOutsideMeterLoop
import J4R43LiteralOutsideUnitStrip
import J4R43LiteralOutsideReceipt

/-! The original zero-mode root of the four-clone binary file has
base-ring coefficients only. Running the old truth tables at width p
and then embedding as a constant gives literally the actual native
entry, not just its reduction mod 2 or its normalized global count. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators Polynomial
open Polynomial DenominatorBudget P1DyadicGrid P11FullPacking J6R10Repack
open J6ActiveRun J6R12Blueprint J6R9Recursive J6ActiveSchedule J6R9PacketCoeff
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N7LiteralSupport
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 7200000
set_option maxRecDepth 2600
set_option Elab.async false

def embedBase (p : ℕ) (f : ℤ[X]) : NativeProbeRing.Base p→+*Residue f 1 p :=
  (J6ActiveInterpolation.scalarIn p f 1).comp (AdjoinRoot.of (NativeProbeRing.liftPoly p f))

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀ v,GraphCutMoments.degree F v=3)
variable {f : ℤ[X]}
local notation "S" => printedParams (f:=f) (ell:=1) (oldRowSize F)
local notation "a₀" => J6ActiveRun.Shape.levelBits S 0
local notation "root" => oldColumnRoot F reg f (fun _=>false)
local notation "M" => Fintype.card (DWire F)
local notation "u₀" => J6ActiveRun.Shape.levelWidth S 0

def outsideBaseRun (P : ColumnPacking F reg (f:=f))
    (t : ColumnCenter F reg (f:=f)) (σ : W→Bool) :
    NativeMeter (NativeProbeRing.Base (registerPrecision S root t)) :=
  let p := registerPrecision S root t
  let c := paidSourceUnit (R:=NativeProbeRing.Base p) a₀ t.val p
  measuredOutsideValue F reg t.val c.1 σ P

theorem outside_at_native_width (P : ColumnPacking F reg (f:=f)) {h : ℕ}
    (G : BandCertificate P h) (d : ColumnReady F reg (f:=f))
    (t : ColumnCenter F reg (f:=f)) (i : Fin a₀) (hv : padicValInt 2 t.val=i.val)
    (wide : 2^a₀-h≤t.val.natAbs) (hf : f.Monic) (hd : 0<f.natDegree) (σ : W→Bool) :
    let p := registerPrecision S root t
    let out := outsideBaseRun F reg P t σ
    originalOppositeSlot F reg P d t i hv 0 0 hf σ=embedBase p f out.value ∧
      out.addressOps≤oldRowSize F*(24*M) ∧ out.tableOps≤8*oldRowSize F ∧
      out.ringOps+(paidSourceUnit (R:=NativeProbeRing.Base p) a₀ t.val p).2≤
        65*oldRowSize F+2*p+3 := by
  let p := registerPrecision S root t
  let E := embedBase p f
  let nil := J6R10Integral.box_two_nil p f 1
  let bnil := NativeProbeRing.base_nilpotent p
  let κ := paidSourceUnit (R:=NativeProbeRing.Base p) a₀ t.val p
  have mem : t.val∈grid a₀ := (active_grid a₀ M u₀ t.property).1
  have source := actual_paid_source_unit a₀ mem p bnil
  have srcMap : E.comp (J6ZeroTransport.reduceAt p bnil)=J6ZeroTransport.reduceAt p nil :=
    J6ZeroTransport.reduceAt_comp E p p bnil nil
  let out := measuredOutsideValue F reg t.val κ.1 σ P
  have arithmetic := measured_outside_bounds F reg t.val κ.1 σ P
  change originalOppositeSlot F reg P d t i hv 0 0 hf σ=E out.value ∧
    out.addressOps≤oldRowSize F*(24*M) ∧ out.tableOps≤8*oldRowSize F ∧
    out.ringOps+κ.2≤65*oldRowSize F+2*p+3
  refine ⟨?_,arithmetic.1,by simpa only [Nat.mul_comm] using arithmetic.2.1,?_⟩
  · have outVal := measured_outside_exact F reg t.val κ.1 σ P
    change out.value=factorizedValue F reg P t.val κ.1 σ at outVal
    have ck : κ.1=J6ZeroTransport.reduceAt p bnil (rho a₀ t.val) := source.1
    have factor := map_factorized_value F reg P (J6ZeroTransport.reduceAt p bnil)
      t.val (rho a₀ t.val) σ
    rw [literal_outside_value F reg P G d t i hv wide hf hd σ,←srcMap,
      RingHom.comp_apply,outVal,ck,factor]
  · have a := arithmetic.2.2
    have c : κ.2=2*p+3 := source.2
    change out.ringOps≤oldRowSize F*65 at a
    omega

#print axioms embedBase
#print axioms outside_at_native_width
end
end J4R43LiteralOutside

