
import J6R25StableCensusFactor
import J6R25StableCensusSample
import J6R25StableCensusOuter
import J6R25StableCensusExport
import J6R22RootReadoutTop

/-! Compose the original metered census, factor, signed sample and
outer count bits on one legal chart. Confirmed U/V slot acquisition
is still a separate ledger. -/
namespace J6R25StableCensus
open scoped Polynomial BigOperators Classical
open Polynomial Std.Sat P11FullPacking J6Mesh J6OrientedHost J6OrientedHostEval
open J6R23PaddingCensus J6R24LegalLayout J6R15SignedRead J6R9Recursive
open J6R22RootReadout J6R18ChildWrite J6R10Integral J6NativeHeightMesh
open J7R10Plant J9R19CompiledBits A1R10 A1R12 AOracleMachineTime
set_option maxHeartbeats 4300000
set_option maxRecDepth 2500
set_option linter.unusedSectionVars false

def legalSitePrep {B Kp : ℕ} (hb : 0<B) (m q : ℕ) (i : J6Recovery.Addr m)
    (raw : List (PadColumnWord Kp (a m+1))) : Meter (Word B) :=
  let c := censusAt m i raw
  let n := makePublicFactor hb m q i c.result
  ⟨n.result,c.steps+n.steps+4⟩

def legalSiteFee (B Kp m n : ℕ) (i : J6Recovery.Addr m) :=
  censusBudget Kp m n+63*B+37+(2*m+1)*meshStateFee B+factorTapeFee B m (index m i) n+4

theorem legal_site_prep_exact {B Kp : ℕ} (hb : 0<B) (m l q : ℕ)
    (w : Fin (a m)→Fin 64) (hm : m≤K m) (hL : 2*l=L m)
    (C : LegalRootChart w hm hL) (code : Page (a m) (K m) (Fin 64)→ℕ)
    (inj : Function.Injective code) (i : J6Recovery.Addr m)
    (raw : List (PadColumnWord Kp (a m+1))) (order : List (NativePad m l w))
    (nd : order.Nodup) (all : order.toFinset=Finset.univ)
    (chart : realizesLegalLayout m l w hm hL C code raw order)
    (width : publicFactorWidth m q order.length+2≤B) :
    (bitsValue (legalSitePrep hb m q i raw).result.val:ℤ)=legalFactor m l q w hm hL C i ∧
      (legalSitePrep hb m q i raw).steps≤legalSiteFee B Kp m order.length i := by
  let c := censusAt m i raw
  let n := makePublicFactor hb m q i c.result
  obtain ⟨semantic,cs⟩ := legal_census_at_exact m l w hm hL C code inj raw order nd all chart i
  have len : c.result.length=order.length := semantic.length_eq
  have fit : publicFactorWidth m q c.result.length+2≤B := by rwa [len]
  obtain ⟨ex,cost⟩ := actual_legal_factor_word hb m q l w hm hL C i order nd all c.result semantic fit
  refine ⟨ex,?_⟩
  rw [len] at cost
  change c.steps+n.steps+4≤_
  have z : c.steps≤censusBudget Kp m order.length := cs
  have here : n.steps≤_ := cost
  unfold legalSiteFee
  omega

def legalRootWords {P B R ell Kp : ℕ} (hp : 0<P) (hb : 0<B) (hr : 0<R)
    {fw : List (Word P)} (m q : ℕ) (slots : J6Recovery.Addr m→UVBlock fw ell)
    (raw : List (PadColumnWord Kp (a m+1))) : Meter (Word R) :=
  let bank := List.ofFn (fun i=>legalSitePrep hb m q i raw)
  let ds (i : J6Recovery.Addr m) := (bank[i.val]'(by simpa only [bank,List.length_ofFn] using i.isLt)).result
  let count := fullRootWords hp hr m slots ds
  ⟨count.result,count.steps+(bank.map Meter.steps).sum+(m+1)^2*(8*B+16)+4⟩

def legalRootBudget (P B R ell d Kp m n : ℕ) :=
  ((∑ i : J6Recovery.Addr m,makeCoordinateFee P B R ell d m (J6Recovery.exp m i))+
    printedOuterFee R m+12*(m+1)*(R+1)+10)+
    (∑ i : J6Recovery.Addr m,legalSiteFee B Kp m n i)+(m+1)^2*(8*B+16)+4

theorem generic_legal_root_words {V : Type} [Fintype V]
    (m l q b B R Kp : ℕ) (T : Plant V m q) (w : Fin (a m)→Fin 64)
    (hm : m≤K m) (hL : 2*l=L m) (C : LegalRootChart w hm hL)
    (hz : coreA T (fun _=>false)=true) (answer : ℕ)
    (value : (outerAtOne m (sampleNum m) (sampleDen m) (rootOldNumerator m q T)).value-1=(answer:ℚ))
    (f : ℤ[X]) (ell : ℕ) (hf : f.Monic) (hF : 0<f.natDegree) (hℓ : 0<ell)
    (hp : 0<J6SourcePrecision.printed m b) (hb : 0<B) (hr : 0<R)
    {fw : List (Word (J6SourcePrecision.printed m b))}
    (hPoly : Modulus _ hp fw=NativeProbeRing.liftPoly (J6SourcePrecision.printed m b) f)
    (slots : J6Recovery.Addr m→UVBlock fw ell)
    (received : ∀ i,J6R18ChildWrite.castBox hPoly (uvRead hp fw ell (slots i)) =
      J6ZeroTransport.reduceAt (J6SourcePrecision.printed m b)
        (box_two_nil (J6SourcePrecision.printed m b) f ell)
        (chartScalar (V:=V) m l q T w hm hL C i))
    (code : Page (a m) (K m) (Fin 64)→ℕ) (inj : Function.Injective code)
    (raw : List (PadColumnWord Kp (a m+1))) (order : List (NativePad m l w))
    (nd : order.Nodup) (all : order.toFinset=Finset.univ)
    (chart : realizesLegalLayout m l w hm hL C code raw order)
    (factorFit : publicFactorWidth m q order.length+2≤B)
    (outerFit : (baseTermWidth m (outerMeshWidth m) (J6SourcePrecision.printed m b)+1)*(m+1)+3≤R) :
    bitsValue (legalRootWords hp hb hr m q slots raw).result.val=answer ∧
      (legalRootWords hp hb hr m q slots raw).steps≤
        legalRootBudget (J6SourcePrecision.printed m b) B R ell fw.length Kp m order.length := by
  let bank := List.ofFn (fun i=>legalSitePrep hb m q i raw)
  let ds (i : J6Recovery.Addr m) := (bank[i.val]'(by simpa only [bank,List.length_ofFn] using i.isLt)).result
  have D (i : J6Recovery.Addr m) := legal_site_prep_exact hb m l q w hm hL C code inj i raw order nd all chart factorFit
  have Dval (i : J6Recovery.Addr m) : (bitsValue (ds i).val:ℤ)=legalFactor m l q w hm hL C i := by
    simpa only [ds,bank,List.getElem_ofFn] using (D i).1
  have S (i : J6Recovery.Addr m) := legal_root_sample_words b m l q B T w hm hL C i hz
    f ell hf hF hℓ hp hPoly (slots i) (prepareMeshWords hp m i).result.2 (ds i)
      (received i) (prepare_mesh_exact hp m i).2.1 (Dval i)
  have fit : ∀ i,Fits (J6SourcePrecision.printed m b) (rootOldNumerator m q T i) :=
    fun i=>(legal_old_root_fits m l q b T w hm hL C i hz).le
  have out := full_root_words_receipt hp hr m slots ds (rootOldNumerator m q T) answer S fit value outerFit
  refine ⟨out.1,?_⟩
  have lab : (bank.map Meter.steps).sum≤∑ i : J6Recovery.Addr m,legalSiteFee B Kp m order.length i := by
    unfold bank
    rw [List.map_ofFn,List.sum_ofFn]
    exact Finset.sum_le_sum (fun i _=>(D i).2)
  change (fullRootWords hp hr m slots ds).steps+(bank.map Meter.steps).sum+(m+1)^2*(8*B+16)+4≤_
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add out.2 lab) _) _

#print axioms legal_site_prep_exact
#print axioms generic_legal_root_words
end J6R25StableCensus
