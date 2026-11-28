import J6R22RootReadoutSample

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4200000
set_option maxRecDepth 1600

/-! A concrete polynomial cap on the already implemented J6 signed
sample decoder. It includes U/V projection, modular denominator
clearing, the paid division, and the paid exact odd-root search. -/
namespace J6R49Cost
open scoped Polynomial
open Polynomial A1R10 A1R11 A1R12 AOracleMachineTime AOracleCoordinates
open J6R22RootReadout J6R15SignedRead J6R18ChildWrite

def sampleWordTariff (degree ell p b wires exp : ℕ) : ℕ :=
  6+ell*(degree*p+2)+degree*(p+2)+rootSampleFee p b wires exp

theorem sample_word_tariff_mono {degree ell p b wires exp s : ℕ}
    (hd : degree≤s) (hv : ell≤s) (hp : p≤s) (hb : b≤s) (hw : wires≤s) (he : exp≤s) :
    sampleWordTariff degree ell p b wires exp≤sampleWordTariff s s s s s s := by
  unfold sampleWordTariff rootSampleFee rootProbeFee signedDivisionFee wordMulFee
  dsimp only
  gcongr

theorem sample_word_diagonal_poly (s : ℕ) :
    sampleWordTariff s s s s s s≤1000*(s+1)^6 := by
  have exactPoly :
      1000*(s+1)^6=sampleWordTariff s s s s s s+
        (909+5541*s+14676*s^2+19789*s^3+14870*s^4+5968*s^5+968*s^6) := by
    unfold sampleWordTariff rootSampleFee rootProbeFee signedDivisionFee wordMulFee
    dsimp only
    ring
  rw [exactPoly]
  exact Nat.le_add_right _ _

theorem sample_word_tariff_poly {degree ell p b wires exp s : ℕ}
    (hd : degree≤s) (hv : ell≤s) (hp : p≤s) (hb : b≤s) (hw : wires≤s) (he : exp≤s) :
    sampleWordTariff degree ell p b wires exp≤1000*(s+1)^6 :=
  (sample_word_tariff_mono hd hv hp hb hw he).trans (sample_word_diagonal_poly s)

theorem same_sample_decoder_word_and_budget
    {p b ell : ℕ} (hp : 0<p) (hℓ : 0<ell) {fw : List (Word p)}
    {f : ℤ[X]} (hf : f.Monic) (hPoly : Modulus p hp fw=NativeProbeRing.liftPoly p f)
    (uv : UVBlock fw ell) (den : Word p) (D : Word b) (wires exp : ℕ) (x : ℤ)
    (hd : 0<bitsValue D.val) (odd : Odd exp) (hx : x.natAbs<2^p)
    (clear : ((wordRead den)^wires*boxProject p f ell hf hℓ
      (castBox hPoly (uvRead hp fw ell uv))).valMinAbs=(bitsValue D.val:ℤ)*x^exp)
    (s : ℕ) (he : fw.length≤s) (hv : ell≤s) (hP : p≤s) (hB : b≤s)
    (hw : wires≤s) (hExp : exp≤s) :
    (rootSampleFromUV hp uv den D wires exp).result.value=x ∧
      (rootSampleFromUV hp uv den D wires exp).steps≤1000*(s+1)^6 := by
  obtain ⟨v,c⟩ := root_sample_uv_exact hp hℓ hf hPoly uv den D wires exp x hd odd hx clear
  exact ⟨v,c.trans (sample_word_tariff_poly he hv hP hB hw hExp)⟩

#print axioms sample_word_tariff_mono
#print axioms sample_word_diagonal_poly
#print axioms sample_word_tariff_poly
#print axioms same_sample_decoder_word_and_budget
end J6R49Cost

