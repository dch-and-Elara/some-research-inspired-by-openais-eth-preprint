
import J6R25StableCensusNumerator
import J6R22RootReadoutSample

/-! Use the already implemented physical U/V, centering, restoring
division and greedy odd-root machine, but prove its *new chart* input
identity from the appropriate undeformed register and factor. -/
namespace J6R25StableCensus
open scoped Polynomial BigOperators Classical
open Polynomial P11FullPacking J6Mesh J6OrientedHost J6OrientedHostEval J6R9Recursive
open J6R23PaddingCensus J6R24LegalLayout J6R22RootReadout J6R15SignedRead
open J6R18ChildWrite J6R10Integral J6NativeHeightMesh
open A1R10 A1R12 AOracleMachineTime
set_option maxHeartbeats 21000000
set_option maxRecDepth 2200
set_option linter.unusedSectionVars false

theorem legal_root_sample_words {V : Type} [Fintype V]
    (b m l q B : ℕ) (T : Plant V m q) (w : Fin (a m)→Fin 64)
    (hm : m≤K m) (hL : 2*l=L m) (C : LegalRootChart w hm hL)
    (i : J6Recovery.Addr m) (hz : coreA T (fun _=>false)=true)
    (f : ℤ[X]) (ell : ℕ) (hf : f.Monic) (hF : 0<f.natDegree) (hℓ : 0<ell)
    (hp : 0<J6SourcePrecision.printed m b) {fw : List (Word (J6SourcePrecision.printed m b))}
    (hPoly : Modulus _ hp fw=NativeProbeRing.liftPoly (J6SourcePrecision.printed m b) f)
    (uv : UVBlock fw ell) (den : Word (J6SourcePrecision.printed m b)) (D : Word B)
    (received : J6R18ChildWrite.castBox hPoly (uvRead hp fw ell uv) =
      J6ZeroTransport.reduceAt (J6SourcePrecision.printed m b)
        (box_two_nil (J6SourcePrecision.printed m b) f ell) (chartScalar (V:=V) m l q T w hm hL C i))
    (hden : wordRead den=(sampleDen m i:ZMod (2^J6SourcePrecision.printed m b)))
    (hD : (bitsValue D.val:ℤ)=legalFactor m l q w hm hL C i) :
    let p := J6SourcePrecision.printed m b
    let s := rootSampleFromUV hp uv den D (M m) (J6Recovery.exp m i)
    s.result.value=rootOldNumerator m q T i ∧
      s.steps≤6+ell*(fw.length*p+2)+fw.length*(p+2)+rootSampleFee p B (M m) (J6Recovery.exp m i) := by
  dsimp only
  have hd : 0<bitsValue D.val := by
    exact_mod_cast (show (0:ℤ)<bitsValue D.val by rw [hD];exact legal_factor_positive m l q w hm hL C i)
  apply root_sample_uv_exact hp hℓ hf hPoly uv den D (M m) (J6Recovery.exp m i)
    (rootOldNumerator m q T i) hd (J6Recovery.odd_exp m i)
    (legal_old_root_fits m l q b T w hm hL C i hz)
  rw [hden,centered_legal_raw_exact f ell b m l q T w hm hL C hf hF hℓ i _ received,hD]
  exact legal_numerator_factorization m l q T w hm hL C i hz

#print axioms legal_root_sample_words
end J6R25StableCensus
