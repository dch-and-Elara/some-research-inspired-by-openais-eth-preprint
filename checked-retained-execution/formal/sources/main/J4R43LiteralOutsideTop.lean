import J4R43LiteralOutsideSeating
import J4R43LiteralOutsideValue
import J4R43LiteralOutsideCost

/-! Same signed outside interval on one graph-only ordered packing.
The quota premise is an actual finite matched-edge supply in every
cell; it is not a per-node layout or an arbitrary group-value receipt. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators Polynomial
open Polynomial DenominatorBudget J6R9PacketCoeff P11FullPacking J6R10Repack J6R9PacketTiles
open J6ActiveRun J6R12Blueprint
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N7LiteralSupport
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

def reciprocal (degree : ℕ) : ℕ := 2^(2*degree-1)

def printedBand (a degree : ℕ) : ℕ := 2^a/(8*reciprocal degree)

theorem printed_band_legal (a degree : ℕ) (eventual : 8*reciprocal degree≤2^a) :
    0<printedBand a degree ∧ 2*printedBand a degree≤2^a := by
  let D := reciprocal degree
  have hD : 0<D := by unfold D reciprocal; positivity
  have h8 : 0<8*D := by positivity
  constructor
  · exact Nat.div_pos eventual h8
  · have h : (2^a/(8*D))*(8*D)≤2^a := Nat.div_mul_le_self _ _
    have g := Nat.mul_le_mul_left (2^a/(8*D)) (show 2≤8*D by omega)
    change 2*(2^a/(8*D))≤2^a
    rw [show 2*(2^a/(8*D))=(2^a/(8*D))*2 by omega]
    exact g.trans h

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀ v,GraphCutMoments.degree F v=3)
variable {f : ℤ[X]}
local notation "S" => printedParams (f:=f) (ell:=1) (oldRowSize F)
local notation "root" => oldColumnRoot F reg f (fun _=>false)
local notation "a₀" => J6ActiveRun.Shape.levelBits S 0

theorem same_layout_all_actual_outer_nodes
    (P : ColumnPacking F reg (f:=f)) (d : ColumnReady F reg (f:=f))
    (degree : ℕ) (enough : 8*reciprocal degree≤2^a₀)
    (pin : DWire F) (supply : BandSupply P (printedBand a₀ degree) pin)
    (hf : f.Monic) (hd : 0<f.natDegree) :
    ∃ Q : ColumnPacking F reg (f:=f),
      Q.rowLabel=P.rowLabel ∧ Q.colLabel=P.colLabel ∧ Q.copies=P.copies ∧
      Q.mask=J7SeatPacking.balancedMask a₀ Q.copies ∧
      BandCertificate Q (printedBand a₀ degree) ∧ (Q.seat pin).2.val+1=2^a₀ ∧
      ∀ (t : ColumnCenter F reg (f:=f)) (i : Fin a₀) (hv : padicValInt 2 t.val=i.val),
        (16*reciprocal degree)*(2^a₀-t.val.natAbs)≤2^a₀ →
        ∀ σ : W→Bool,
          originalOppositeSlot F reg Q d t i hv 0 0 hf σ =
            J6ZeroTransport.reduceAt (registerPrecision S root t)
              (J6R10Integral.box_two_nil (registerPrecision S root t) f 1)
              (factorizedValue F reg Q t.val (rho a₀ t.val) σ) := by
  have h := printed_band_legal a₀ degree enough
  obtain ⟨Q,r,c,b,m,band,last⟩ := realize_band_with_pin P (printedBand a₀ degree) h.1 h.2 pin supply
  refine ⟨Q,r,c,b,m,band,last,?_⟩
  intro t i hv interval σ
  have pos : 0<reciprocal degree := by unfold reciprocal; positivity
  have wide := printed_fraction_in_band (2^a₀) (reciprocal degree) t.val.natAbs pos interval
  exact literal_outside_value F reg Q band d t i hv wide hf hd σ

#print axioms printed_band_legal
#print axioms same_layout_all_actual_outer_nodes
end
end J4R43LiteralOutside

