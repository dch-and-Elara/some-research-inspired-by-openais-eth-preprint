
import J6R22RootReadoutTop
import J6R22RootReadoutFactorSource

/-! Combine public normalizer preparation with the signed native root
readout. The inputs are the actual already acquired U/V slots and the
ordered physical load census, not a table of precomputed normalizers. -/
namespace J6R22RootReadout
open scoped Polynomial BigOperators Classical
open Polynomial Std.Sat P11FullPacking J6Mesh J6OrientedHost J6RepairedCentered
open J7R10Plant J6R15SignedRead J6R12Repack J6R14ZeroMode J6R18ChildWrite J1PPrinted
open A1R10 A1R12 AOracleMachineTime
set_option maxHeartbeats 23000000
set_option maxRecDepth 2400
set_option linter.unusedSectionVars false

def preparedRootWords {P B R ell : ℕ} (hp : 0<P) (hb : 0<B) (hr : 0<R)
    {fw : List (Word P)} (m q : ℕ) (slots : J6Recovery.Addr m→UVBlock fw ell)
    (census : J6Recovery.Addr m→List (Fin 3)) : Meter (Word R) :=
  let bank := List.ofFn (fun i=>makePublicFactor hb m q i (census i))
  let inWords (i : J6Recovery.Addr m) := (bank[i.val]'(by simpa only [bank,List.length_ofFn] using i.isLt)).result
  let run := fullRootWords hp hr m slots inWords
  ⟨run.result,run.steps+(bank.map Meter.steps).sum+(m+1)^2*(8*B+16)+4⟩

section Raw
variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
variable {f : ℤ[X]} {ell : ℕ} [Fact (Irreducible (NativeProbeRing.residuePoly f))]
local notation "ms" => J7R10Readout.mCNF
local notation "qs" => J7R10Readout.qCNF
local notation "inp" => J7R10Readout.H
local notation "pm" => J6SourcePrecision.printed

theorem exact_native_raw_count_from_census
    (F : CNF V) (p l native B R : ℕ)
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
    (census : J6Recovery.Addr (ms F)→List (Fin 3))
    (aligned : ∀ i,List.Forall₂ (fun k v=>k.val=J6PhysicalInteger.loads (ms F) l mask w hm hL i v) (census i) order)
    (factorWidth : publicFactorWidth (ms F) (qs F) order.length+2≤B)
    (width : (baseTermWidth (ms F) (outerMeshWidth (ms F)) (pm (ms F) p)+1)*(ms F+1)+3≤R) :
    let m := ms F
    let out := preparedRootWords hp hb hr m (qs F) slots census
    bitsValue out.result.val=PinnedCNF.modelCount F ∧
    out.steps≤
      ((∑ i : J6Recovery.Addr m,makeCoordinateFee (pm m p) B R ell fw.length m (J6Recovery.exp m i))+
      printedOuterFee R m+12*(m+1)*(R+1)+10)+
      (∑ i : J6Recovery.Addr m,(63*B+37+(2*m+1)*meshStateFee B+factorTapeFee B m (index m i) order.length))+
      (m+1)^2*(8*B+16)+4 := by
  let m := ms F
  let q := qs F
  let bank := List.ofFn (fun i=>makePublicFactor hb m q i (census i))
  let ds (i : J6Recovery.Addr m) := (bank[i.val]'(by simpa only [bank,List.length_ofFn] using i.isLt)).result
  have factor (i : J6Recovery.Addr m) :=
    actual_public_factor_word hb m q l mask w hm hL i order nodup all (census i) (aligned i)
      (by rw [(aligned i).length_eq]; exact factorWidth)
  have dExact (i : J6Recovery.Addr m) : (bitsValue (ds i).val:ℤ)=rootPublicFactor m q l mask w hm hL i := by
    simpa only [ds,bank,List.getElem_ofFn] using (factor i).1
  have out := exact_native_raw_count_words F p l native B R w mask hm hL hn
    hfield hsize hdeg hf hbase hF hℓ menu hp hr hPoly slots ds received dExact width
  refine ⟨out.1,?_⟩
  have bcost :
      (bank.map Meter.steps).sum≤
        ∑ i : J6Recovery.Addr m,(63*B+37+(2*m+1)*meshStateFee B+factorTapeFee B m (index m i) order.length) := by
    unfold bank
    rw [List.map_ofFn,List.sum_ofFn]
    exact Finset.sum_le_sum fun i _=>by simpa only [(aligned i).length_eq] using (factor i).2
  change (fullRootWords hp hr m slots ds).steps+(bank.map Meter.steps).sum+(m+1)^2*(8*B+16)+4≤_
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add out.2 bcost) _) _
end Raw

#print axioms exact_native_raw_count_from_census
end J6R22RootReadout
