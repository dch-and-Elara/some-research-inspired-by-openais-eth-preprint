
import J6R22RootReadoutOddRoot
import J6R22RootReadoutExtract
import J6R22RootReadoutNativeFactor

/-! Complete native sample conversion after the physical fallback slot
has been acquired. The public denominator and positive factor word are
explicit inputs; no odd-root, division, or quotient-ring coefficient oracle
is called by the machine. -/
namespace J6R22RootReadout
open scoped Polynomial BigOperators Classical
open Polynomial P11FullPacking J6Mesh J6OrientedHost J6OrientedHostEval
open J6RepairedCentered J6NativeHeightMesh J6R15SignedRead
open J6R12Repack J6R14ZeroMode J6R18ChildWrite J6R19Retained J1PPrinted
open A1R10 A1R12 AOracleMachineTime AOracleCoordinates
set_option maxHeartbeats 16500000
set_option maxRecDepth 2048
set_option linter.unusedSectionVars false

def rootSampleFee (p b wires e : ℕ) : ℕ :=
  let width := p*e+1
  38*p+20+(wires+1)*wordMulFee p+signedDivisionFee p b+
    (8*width+10+p*rootProbeFee width e p)+2

def rootSample {p b : ℕ} (hp : 0<p) (den z : Word p)
    (D : Word b) (wires e : ℕ) : Meter (SignedMagnitude (p*e+1)) :=
  let q := clearThenDivide hp den z (List.replicate wires ()) D
  let y := signedRootWord (w:=p*e+1) (by omega) q.result (List.replicate e ()) (List.replicate p ())
  ⟨y.result,q.steps+y.steps+2⟩

theorem root_sample_exact {p b : ℕ} (hp : 0<p)
    (den z : Word p) (D : Word b) (wires e : ℕ) (x : ℤ)
    (hd : 0<bitsValue D.val) (odd : Odd e) (hx : x.natAbs<2^p)
    (clear : ((wordRead den)^wires*wordRead z).valMinAbs=(bitsValue D.val:ℤ)*x^e) :
    (rootSample hp den z D wires e).result.value=x ∧
      (rootSample hp den z D wires e).steps≤rootSampleFee p b wires e := by
  let q := clearThenDivide hp den z (List.replicate wires ()) D
  have hr := clear_then_divide_exact hp den z (List.replicate wires ()) D hd (x^e) (by simpa using clear)
  have ep : 0<e := by obtain ⟨j,hj⟩ := odd; omega
  have hW : p≤p*e+1 := (Nat.le_mul_of_pos_right _ ep).trans (Nat.le_succ _)
  have hY := signed_root_word_exact (w:=p*e+1) (by omega) hW q.result
    (List.replicate e ()) (List.replicate p ()) (by simp) (by simp)
    x (by simpa using odd) (by simpa using hr.1) hx
  refine ⟨hY.1,?_⟩
  change q.steps+(signedRootWord (w:=p*e+1) _ q.result (List.replicate e ()) (List.replicate p ())).steps+2≤_
  have hs := hr.2
  simp only [List.length_replicate] at hs
  change q.steps≤_ at hs
  have hy := hY.2
  simp only [List.length_replicate] at hy
  exact Nat.add_le_add_right (Nat.add_le_add hs hy) 2

def rootSampleFromUV {p b ell : ℕ} (hp : 0<p) {fw : List (Word p)} (uv : UVBlock fw ell)
    (den : Word p) (D : Word b) (wires e : ℕ) : Meter (SignedMagnitude (p*e+1)) :=
  let read := extractBaseWord hp uv
  let s := rootSample hp den read.result D wires e
  ⟨s.result,read.steps+s.steps+2⟩

theorem root_sample_uv_exact {p b ell : ℕ} (hp : 0<p) (hℓ : 0<ell)
    {fw : List (Word p)} {f : ℤ[X]} (hf : f.Monic)
    (hPoly : Modulus p hp fw=NativeProbeRing.liftPoly p f)
    (uv : UVBlock fw ell) (den : Word p) (D : Word b) (wires e : ℕ) (x : ℤ)
    (hd : 0<bitsValue D.val) (odd : Odd e) (hx : x.natAbs<2^p)
    (clear : ((wordRead den)^wires*boxProject p f ell hf hℓ
      (castBox hPoly (uvRead hp fw ell uv))).valMinAbs=(bitsValue D.val:ℤ)*x^e) :
    (rootSampleFromUV hp uv den D wires e).result.value=x ∧
      (rootSampleFromUV hp uv den D wires e).steps≤
        6+ell*(fw.length*p+2)+fw.length*(p+2)+rootSampleFee p b wires e := by
  have h := base_word_extract_exact hp hℓ hf hPoly uv
  have t := root_sample_exact hp den (extractBaseWord hp uv).result D wires e x hd odd hx (by rwa [h.1])
  refine ⟨t.1,?_⟩
  change (extractBaseWord hp uv).steps+
    (rootSample hp den (extractBaseWord hp uv).result D wires e).steps+2≤_
  exact (Nat.add_le_add_right (Nat.add_le_add (le_of_eq h.2) t.2) 2).trans (by omega)

section Source
open J6R9Recursive

variable {V : Type} [Fintype V] {f : ℤ[X]} {ell : ℕ} [Fact (Irreducible (NativeProbeRing.residuePoly f))]

/-- Input UV is the actual signed fallback receiver already paid for elsewhere.
The only remaining public-table inputs here are its prepared denominator
and positive factor words, not claims about the hidden numerator. -/
theorem literal_root_sample_from_uv
    (p m l q native b : ℕ) (T : Plant V m q)
    (w : Fin (a m)→Fin 64) (mask : MaskFamily (a m) (K m) (Fin 64))
    (hm : m≤K m) (hL : 2*l=L m) (hn : native≤m)
    (hfield : f.natDegree=4*Nat.clog 2 (physicalSize m native))
    (hsize : (2*epsDen)^30*(2:ℕ)^10≤Nat.clog 2 (physicalSize m native))
    (hdeg : ∀ v,T.degree v≤sourceDelta (physicalSize m native))
    (hf : f.Monic) (hbase : 0<p) (hF : 0<f.natDegree) (hℓ : 0<ell)
    (menu : Prescribed f (literalDegree m native)) (i : J6Recovery.Addr m)
    (hz : coreA T (fun _=>false)=true)
    (hp : 0<J6SourcePrecision.printed m p) {fw : List (Word (J6SourcePrecision.printed m p))}
    (hPoly : Modulus _ hp fw=NativeProbeRing.liftPoly (J6SourcePrecision.printed m p) f)
    (uv : UVBlock fw ell) (den : Word (J6SourcePrecision.printed m p)) (D : Word b)
    (hUV : J6R18ChildWrite.castBox hPoly (uvRead hp fw ell uv) =
        printedNativeFallback (f:=f) (ell:=ell) p m l q native T w mask hm hL hn hfield hsize hdeg hf menu i)
    (hden : wordRead den=(sampleDen m i:ZMod (2^(J6SourcePrecision.printed m p))))
    (hD : (bitsValue D.val:ℤ)=rootPublicFactor m q l mask w hm hL i) :
    let P := J6SourcePrecision.printed m p
    (rootSampleFromUV hp uv den D (M m) (J6Recovery.exp m i)).result.value=rootOldNumerator m q T i ∧
      (rootSampleFromUV hp uv den D (M m) (J6Recovery.exp m i)).steps≤
      6+ell*(fw.length*P+2)+fw.length*(P+2)+rootSampleFee P b (M m) (J6Recovery.exp m i) := by
  dsimp only
  have visible := printedNativeFallback_cleared p m l q native T w mask hm hL hn hfield hsize hdeg
    hf hbase hF hℓ menu i
  have hh : 0<bitsValue D.val := by
    exact_mod_cast (show (0:ℤ)<bitsValue D.val by rw [hD]; exact root_public_factor_pos m q l mask w hm hL i)
  apply root_sample_uv_exact hp hℓ hf hPoly uv den D (M m) (J6Recovery.exp m i)
    (rootOldNumerator m q T i) hh (J6Recovery.odd_exp m i)
    (source_odd_root_fits m q p l T mask w hm hL i (Fintype.card_fin 64) hz)
  rw [hden,hUV]
  rw [visible,source_actual_factor m q l T mask w hm hL i hz,hD]

end Source
#print axioms root_sample_exact
#print axioms root_sample_uv_exact
#print axioms literal_root_sample_from_uv
end J6R22RootReadout
