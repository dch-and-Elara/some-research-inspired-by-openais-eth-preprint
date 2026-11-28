
import J6R22RootReadoutOuterTape
import J6R22RootReadoutCount
import J6R22RootReadoutSample
import J6R22RootReadoutMeshPrep

/-! Compose both word widths and the native source receipt. The inputs
are the already acquired completed fallback U/V words and the public
positive-factor words, each on exactly the same actual odd address. -/
namespace J6R22RootReadout
open scoped Polynomial BigOperators Classical
open Polynomial Std.Sat J7R10Plant J6R9Recursive P11FullPacking J6Mesh
open J6NativeHeightMesh J6R15SignedRead J6R12Repack J6R14ZeroMode
open J6OrientedHost J6OrientedHostEval J1PPrinted J6R18ChildWrite
open A1R10 A1R12 AOracleMachineTime J9R19CompiledBits
set_option linter.unusedSectionVars false
set_option maxHeartbeats 20000000
set_option maxRecDepth 2500

def makeNativeCoordinate {P B R ell : ℕ} (hp : 0<P) (hr : 0<R)
    {fw : List (Word P)} (m : ℕ) (i : J6Recovery.Addr m)
    (slot : UVBlock fw ell) (D : Word B) : Meter (CoordinateWord R) :=
  let nm := prepareMeshWords hp m i
  let q := rootSampleFromUV hp slot nm.result.2 D (M m) (J6Recovery.exp m i)
  let out := prepareMeshWords hr m i
  let s := signedWord hr q.result.negative q.result.magnitude.val
  ⟨⟨out.result.1,out.result.2,s.result⟩,nm.steps+q.steps+out.steps+s.steps+10⟩

def makeCoordinateFee (P B R ell degree m e : ℕ) :=
  (28*P+24+(2*m+1)*meshStateFee P)+
  (6+ell*(degree*P+2)+degree*(P+2)+rootSampleFee P B (M m) e)+
  (28*R+24+(2*m+1)*meshStateFee R)+(19*R+6)+10

theorem make_native_coordinate_exact {P B R ell : ℕ} (hp : 0<P) (hr : 0<R)
    {fw : List (Word P)} (m : ℕ) (i : J6Recovery.Addr m)
    (slot : UVBlock fw ell) (D : Word B) (answer : ℤ)
    (origin :
      let den := (prepareMeshWords hp m i).result.2
      let sample := rootSampleFromUV hp slot den D (M m) (J6Recovery.exp m i)
      sample.result.value=answer ∧ sample.steps≤
        6+ell*(fw.length*P+2)+fw.length*(P+2)+rootSampleFee P B (M m) (J6Recovery.exp m i)) :
    (makeNativeCoordinate hp hr m i slot D).result.realizes (sampleNum m i) (sampleDen m i) answer ∧
    (makeNativeCoordinate hp hr m i slot D).steps≤
      makeCoordinateFee P B R ell fw.length m (J6Recovery.exp m i) := by
  let nm := prepareMeshWords hp m i
  let q := rootSampleFromUV hp slot nm.result.2 D (M m) (J6Recovery.exp m i)
  let out := prepareMeshWords hr m i
  let s := signedWord hr q.result.negative q.result.magnitude.val
  obtain ⟨n,d,hc⟩ := prepare_mesh_exact hr m i
  obtain ⟨_,_,hs⟩ := prepare_mesh_exact hp m i
  obtain ⟨v,c⟩ := signedWord_exact hr q.result.negative q.result.magnitude.val
  have V : wordRead s.result=(q.result.value:ZMod (2^R)) := v
  have ans : q.result.value=answer := origin.1
  constructor
  · exact ⟨n,d,V.trans (congrArg (fun x : ℤ => (x:ZMod (2^R))) ans)⟩
  · change nm.steps+q.steps+out.steps+s.steps+10≤_
    have hq : q.steps≤_ := origin.2
    exact Nat.add_le_add_right (Nat.add_le_add
      (Nat.add_le_add (Nat.add_le_add hs hq) hc) c) _

def fullRootWords {P B R ell : ℕ} (hp : 0<P) (hr : 0<R)
    {fw : List (Word P)} (m : ℕ) (slots : J6Recovery.Addr m→UVBlock fw ell)
    (divisors : J6Recovery.Addr m→Word B) : Meter (Word R) :=
  let C := List.ofFn (fun i=>makeNativeCoordinate hp hr m i (slots i) (divisors i))
  let out := outerWordCount hr m (C.map Meter.result)
  ⟨out.result,(C.map Meter.steps).sum+out.steps+12*(m+1)*(R+1)+10⟩

theorem full_root_words_receipt {P B R ell : ℕ} (hp : 0<P) (hr : 0<R)
    {fw : List (Word P)} (m : ℕ) (slots : J6Recovery.Addr m→UVBlock fw ell)
    (divisors : J6Recovery.Addr m→Word B) (A : J6Recovery.Addr m→ℤ) (answer : ℕ)
    (samples : ∀ i,
      let den := (prepareMeshWords hp m i).result.2
      let sample := rootSampleFromUV hp (slots i) den (divisors i) (M m) (J6Recovery.exp m i)
      sample.result.value=A i ∧ sample.steps≤
        6+ell*(fw.length*P+2)+fw.length*(P+2)+rootSampleFee P B (M m) (J6Recovery.exp m i))
    (fit : ∀ i, Fits P (A i)) 
    (truth : (outerAtOne m (sampleNum m) (sampleDen m) A).value-1=(answer:ℚ))
    (width : (baseTermWidth m (outerMeshWidth m) P+1)*(m+1)+3≤R) :
    bitsValue (fullRootWords hp hr m slots divisors).result.val=answer ∧
    (fullRootWords hp hr m slots divisors).steps≤
      (∑ i : J6Recovery.Addr m,makeCoordinateFee P B R ell fw.length m (J6Recovery.exp m i))+
      printedOuterFee R m+12*(m+1)*(R+1)+10 := by
  let C := List.ofFn (fun i=>makeNativeCoordinate hp hr m i (slots i) (divisors i))
  let xy := C.map Meter.result
  have hlen : xy.length=m+1 := by simp [xy,C]
  have cell (i : J6Recovery.Addr m) :=
    make_native_coordinate_exact hp hr m i (slots i) (divisors i) (A i) (samples i)
  have chart : ∀ j : Fin (m+1), xy[j.val]'(by rw [hlen]; exact j.isLt) |>.realizes
      (sampleNum m j) (sampleDen m j) (A j) := by
    intro j
    simpa only [xy,C,List.getElem_map,List.getElem_ofFn] using (cell j).1
  have out := native_odd_mesh_word_count hr xy hlen A chart fit answer truth width
  refine ⟨out.1,?_⟩
  have bills : (C.map Meter.steps).sum≤
      ∑ i : J6Recovery.Addr m,makeCoordinateFee P B R ell fw.length m (J6Recovery.exp m i) := by
    unfold C
    rw [List.map_ofFn,List.sum_ofFn]
    exact Finset.sum_le_sum fun i _=>(cell i).2
  change (C.map Meter.steps).sum+(outerWordCount hr m xy).steps+12*(m+1)*(R+1)+10≤_
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add bills out.2) _) _

section Raw
variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
variable {f : ℤ[X]} {ell : ℕ} [Fact (Irreducible (NativeProbeRing.residuePoly f))]
local notation "ms" => J7R10Readout.mCNF
local notation "qs" => J7R10Readout.qCNF
local notation "input" => J7R10Readout.H
local notation "pm" => J6SourcePrecision.printed

theorem exact_native_raw_count_words
    (F : CNF V) (p l native B R : ℕ)
    (w : Fin (a (ms F))→Fin 64) (mask : MaskFamily (a (ms F)) (K (ms F)) (Fin 64))
    (hm : ms F≤K (ms F)) (hL : 2*l=L (ms F)) (hn : native≤ms F)
    (hfield : f.natDegree=4*Nat.clog 2 (physicalSize (ms F) native))
    (hsize : (2*epsDen)^30*(2:ℕ)^10≤Nat.clog 2 (physicalSize (ms F) native))
    (hdeg : ∀ v,(physicalPlant (input F)).degree v≤sourceDelta (physicalSize (ms F) native))
    (hf : f.Monic) (hbase : 0<p) (hF : 0<f.natDegree) (hℓ : 0<ell)
    (menu : Prescribed f (literalDegree (ms F) native))
    (hp : 0<pm (ms F) p) (hr : 0<R) {fw : List (Word (pm (ms F) p))}
    (hPoly : Modulus _ hp fw=NativeProbeRing.liftPoly (pm (ms F) p) f)
    (slots : J6Recovery.Addr (ms F)→UVBlock fw ell)
    (divisors : J6Recovery.Addr (ms F)→Word B)
    (received : ∀ i, J6R18ChildWrite.castBox hPoly (uvRead hp fw ell (slots i)) =
        printedNativeFallback (f:=f) (ell:=ell) p (ms F) l (qs F) native (physicalPlant (input F))
          w mask hm hL hn hfield hsize hdeg hf menu i)
    (denoms : ∀ i,(bitsValue (divisors i).val:ℤ)=rootPublicFactor (ms F) (qs F) l mask w hm hL i)
    (width : (baseTermWidth (ms F) (outerMeshWidth (ms F)) (pm (ms F) p)+1)*(ms F+1)+3≤R) :
    let m := ms F
    let out := fullRootWords hp hr m slots divisors
    bitsValue out.result.val=PinnedCNF.modelCount F ∧
    out.steps≤
      (∑ i : J6Recovery.Addr m,makeCoordinateFee (pm m p) B R ell fw.length m (J6Recovery.exp m i))+
      printedOuterFee R m+12*(m+1)*(R+1)+10 := by
  let m := ms F
  let q := qs F
  let T := physicalPlant (input F)
  have s (i : J6Recovery.Addr m) := literal_root_sample_from_uv
    p m l q native B T w mask hm hL hn hfield hsize hdeg hf hbase hF hℓ menu i
    (planted_guard_zero F) hp hPoly (slots i) (prepareMeshWords hp m i).result.2 (divisors i)
    (received i) (prepare_mesh_exact hp m i).2.1 (denoms i)
  have fit : ∀ i,Fits (pm m p) (rootOldNumerator m q T i) :=
    fun i=>(source_odd_root_fits m q p l T mask w hm hL i (Fintype.card_fin 64) (planted_guard_zero F)).le
  have count := source_outer_exact F p l native w mask hm hL hn hfield hsize hdeg
    hf hbase hF hℓ menu
  exact full_root_words_receipt hp hr m slots divisors (rootOldNumerator m q T)
    (PinnedCNF.modelCount F) s fit count width
end Raw

#print axioms make_native_coordinate_exact
#print axioms full_root_words_receipt
#print axioms exact_native_raw_count_words
end J6R22RootReadout
