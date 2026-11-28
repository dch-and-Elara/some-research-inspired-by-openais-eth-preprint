
import J6R23PaddingCensusRoot
import J6R23PaddingCensusExport

/-! Final concrete page-code specialization. The external inputs are
the occupied, assigned true seats and their actual completed U/V slots;
everything between them and the standalone ordinary CNF count is run
inside the charged arithmetic path. -/
namespace J6R23PaddingCensus
open scoped Polynomial BigOperators Classical
open Polynomial Std.Sat P11FullPacking J6Mesh J6OrientedHost J6RepairedCentered
open J7R10Plant J6R15SignedRead J6R12Repack J6R14ZeroMode J6R18ChildWrite J1PPrinted
open A1R10 A1R12 AOracleMachineTime J6R22RootReadout
set_option maxHeartbeats 25000000
set_option maxRecDepth 2400
set_option linter.unusedSectionVars false

def rootFromPositionedSeats {P B R ell : ℕ} (hp : 0<P) (hb : 0<B) (hr : 0<R)
    {fw : List (Word P)} (m q width : ℕ) (slots : J6Recovery.Addr m→UVBlock fw ell)
    (positions : List (PositionedPad (a m) (K m))) : Meter (Word R) :=
  let X := exportActualLayout width positions
  let out := rootFromLayout hp hb hr m q slots X.result
  ⟨out.result,out.steps+X.steps+8⟩

section Raw
variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
variable {f : ℤ[X]} {ell : ℕ} [Fact (Irreducible (NativeProbeRing.residuePoly f))]
local notation "ms" => J7R10Readout.mCNF
local notation "qs" => J7R10Readout.qCNF
local notation "inp" => J7R10Readout.H
local notation "pm" => J6SourcePrecision.printed

theorem exact_native_count_from_positioned_seats
    (F : CNF V) (p l native B R width : ℕ)
    (w : Fin (a (ms F))→Fin 64) (mask : MaskFamily (a (ms F)) (K (ms F)) (Fin 64))
    (hm : ms F≤K (ms F)) (hL : 2*l=L (ms F)) (hn : native≤ms F)
    (hfield : f.natDegree=4*Nat.clog 2 (physicalSize (ms F) native))
    (hsize : (2*epsDen)^30*(2:ℕ)^10≤Nat.clog 2 (physicalSize (ms F) native))
    (hdeg : ∀ v,(physicalPlant (inp F)).degree v≤sourceDelta (physicalSize (ms F) native))
    (hf : f.Monic) (hbase : 0<p) (hF : 0<f.natDegree) (hℓ : 0<ell)
    (menu : Prescribed f (literalDegree (ms F) native))
    (hp : 0<pm (ms F) p) (hb : 0<B) (hr : 0<R) {fw : List (Word (pm (ms F) p))}
    (hPoly : Modulus _ hp fw=NativeProbeRing.liftPoly (pm (ms F) p) f)
    (slots : J6Recovery.Addr (ms F)→UVBlock fw ell)
    (received : ∀ i, J6R18ChildWrite.castBox hPoly (uvRead hp fw ell (slots i)) =
        printedNativeFallback (f:=f) (ell:=ell) p (ms F) l (qs F) native (physicalPlant (inp F))
          w mask hm hL hn hfield hsize hdeg hf menu i)
    (order : List (Pad w (ms F) (K (ms F)) l)) (nodup : order.Nodup) (all : order.toFinset=Finset.univ)
    (positions : List (PositionedPad (a (ms F)) (K (ms F))))
    (chart : positionedLayout (ms F) l mask w hm hL positions order)
    (pageFit : K (ms F)≤2^width)
    (factorWidth : publicFactorWidth (ms F) (qs F) order.length+2≤B)
    (outerWidth : (baseTermWidth (ms F) (outerMeshWidth (ms F)) (pm (ms F) p)+1)*(ms F+1)+3≤R) :
    let m := ms F
    let Kp := width+13*a m
    let exec := rootFromPositionedSeats hp hb hr m (qs F) width slots positions
    bitsValue exec.result.val=PinnedCNF.modelCount F ∧
    exec.steps≤
      ((((∑ i : J6Recovery.Addr m,makeCoordinateFee (pm m p) B R ell fw.length m (J6Recovery.exp m i))+
      printedOuterFee R m+12*(m+1)*(R+1)+10)+
      (∑ i : J6Recovery.Addr m,(63*B+37+(2*m+1)*meshStateFee B+factorTapeFee B m (index m i) order.length))+
      (m+1)^2*(8*B+16)+4)+
      (m+1)*censusBudget Kp m order.length+(m+1)^2*(4*order.length+12)+4)+
      (4+order.length*exportFee (a m) width)+8 := by
  let m := ms F
  let q := qs F
  let X := exportActualLayout width positions
  obtain ⟨H,C⟩ := exported_actual_layout_chart m l width mask w hm hL positions order chart
  have receipt := exact_native_count_from_layout_tape F p l native B R (width+13*a m) w mask hm hL hn
    hfield hsize hdeg hf hbase hF hℓ menu hp hb hr hPoly slots received
    order nodup all (pageCode width) (page_code_injective width pageFit) X.result H factorWidth outerWidth
  refine ⟨receipt.1,?_⟩
  change (rootFromLayout hp hb hr m q slots X.result).steps+X.steps+8≤_
  exact Nat.add_le_add_right (Nat.add_le_add receipt.2 (le_of_eq C)) _
end Raw

#print axioms exact_native_count_from_positioned_seats
end J6R23PaddingCensus
