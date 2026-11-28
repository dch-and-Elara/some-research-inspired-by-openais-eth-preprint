
import J6R23PaddingCensusNative
import J6R23PaddingCensusPrepared

/-! Recover the literal CNF count from the same paid completed slots
and their actual oriented padding layout tape. Neither the per-column
load integers nor the divisor words are furnished by the caller. -/
namespace J6R23PaddingCensus
open scoped Polynomial BigOperators Classical
open Polynomial Std.Sat P11FullPacking J6Mesh J6OrientedHost J6RepairedCentered
open J7R10Plant J6R15SignedRead J6R12Repack J6R14ZeroMode J6R18ChildWrite J1PPrinted
open A1R10 A1R12 AOracleMachineTime J6R22RootReadout
set_option maxHeartbeats 25000000
set_option maxRecDepth 2300
set_option linter.unusedSectionVars false

def rootFromLayout {P B R ell Kp : ℕ} (hp : 0<P) (hb : 0<B) (hr : 0<R)
    {fw : List (Word P)} (m q : ℕ) (slots : J6Recovery.Addr m→UVBlock fw ell)
    (raw : List (PadColumnWord Kp (a m+1))) : Meter (Word R) :=
  let bank := List.ofFn (fun i=>censusAt m i raw)
  let loads (i : J6Recovery.Addr m) := (bank[i.val]'(by simpa only [bank,List.length_ofFn] using i.isLt)).result
  let run := preparedRootWords hp hb hr m q slots loads
  ⟨run.result,run.steps+(bank.map Meter.steps).sum+(m+1)^2*(4*raw.length+12)+4⟩

section Raw
variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
variable {f : ℤ[X]} {ell : ℕ} [Fact (Irreducible (NativeProbeRing.residuePoly f))]
local notation "ms" => J7R10Readout.mCNF
local notation "qs" => J7R10Readout.qCNF
local notation "inp" => J7R10Readout.H
local notation "pm" => J6SourcePrecision.printed

theorem exact_native_count_from_layout_tape
    (F : CNF V) (p l native B R Kp : ℕ)
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
    (encodePage : Page (a (ms F)) (K (ms F)) (Fin 64)→ℕ) (inj : Function.Injective encodePage)
    (raw : List (PadColumnWord Kp (a (ms F)+1)))
    (chart : realizesLayout (ms F) l mask w hm hL encodePage raw order)
    (factorWidth : publicFactorWidth (ms F) (qs F) order.length+2≤B)
    (width : (baseTermWidth (ms F) (outerMeshWidth (ms F)) (pm (ms F) p)+1)*(ms F+1)+3≤R) :
    let m := ms F
    let exec := rootFromLayout hp hb hr m (qs F) slots raw
    bitsValue exec.result.val=PinnedCNF.modelCount F ∧
    exec.steps≤
      (((∑ i : J6Recovery.Addr m,makeCoordinateFee (pm m p) B R ell fw.length m (J6Recovery.exp m i))+
      printedOuterFee R m+12*(m+1)*(R+1)+10)+
      (∑ i : J6Recovery.Addr m,(63*B+37+(2*m+1)*meshStateFee B+factorTapeFee B m (index m i) order.length))+
      (m+1)^2*(8*B+16)+4)+
      (m+1)*censusBudget Kp m order.length+(m+1)^2*(4*order.length+12)+4 := by
  let m := ms F
  let q := qs F
  let bank := List.ofFn (fun i=>censusAt m i raw)
  let loads (i : J6Recovery.Addr m) :=
    (bank[i.val]'(by simpa only [bank,List.length_ofFn] using i.isLt)).result
  have correct (i : J6Recovery.Addr m) := census_at_exact m l mask w hm hL encodePage inj raw order nodup all chart i
  have rc (i : J6Recovery.Addr m) :
      List.Forall₂ (fun k d=>k.val=J6PhysicalInteger.loads m l mask w hm hL i d) (loads i) order := by
    simpa only [loads,bank,List.getElem_ofFn] using (correct i).1
  have out := exact_native_raw_count_from_census F p l native B R w mask hm hL hn
    hfield hsize hdeg hf hbase hF hℓ menu hp hb hr hPoly slots received order nodup all loads rc factorWidth width
  refine ⟨out.1,?_⟩
  have bcost : (bank.map Meter.steps).sum≤(m+1)*censusBudget Kp m order.length := by
    unfold bank
    rw [List.map_ofFn,List.sum_ofFn]
    calc
      _ ≤ ∑ i : J6Recovery.Addr m,censusBudget Kp m order.length :=
        Finset.sum_le_sum fun i _=>(correct i).2
      _ = _ := by simp
  change (preparedRootWords hp hb hr m q slots loads).steps+(bank.map Meter.steps).sum+
    (m+1)^2*(4*raw.length+12)+4≤_
  have H : raw.length=order.length := (show List.Forall₂ _ raw order from chart).length_eq
  rw [H]
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add out.2 bcost) _) _
end Raw

#print axioms exact_native_count_from_layout_tape
end J6R23PaddingCensus
