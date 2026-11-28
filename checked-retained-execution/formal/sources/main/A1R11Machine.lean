import A1R11Factors
import A1R11Verifier

/-! The full per-guess A1 UV verifier on assignment-independent packed
recipes. All row factors are generated inside the metered execution;
the native coefficient and original local tensor tapes are static inputs. -/

namespace A1R11
open A1R10 AOracleCoordinates AOracleWitness AOracleSuccinct AOracleThreshold
open AOracleMachineTime

def runPackedUV {p r c m delta b bc ell : ℕ} (q : ℕ) (hp : 0<p)
    {f : List (A1R10.Word p)} (he : 0<f.length) (hv : 0<ell)
    (P : Packed r c m delta bc f ell) (br : ℕ) (beta : Fin m →₀ ℕ)
    (i j : ℕ) (z : Code r c b × AOracleThreshold.Word p) : Meter Bool :=
  let g := runGate q P.target beta z.1
  if g.result then
    let t := runFactors hp he hv P br z.1
    let v := uvProductAccept hp he hv t.result i j (thresholdBits z.2)
    ⟨v.result,g.steps+t.steps+v.steps+2⟩
  else ⟨false,g.steps+2⟩

theorem runPackedUV_same {p r c m delta b bc ell : ℕ} (q : ℕ) (hp : 0<p)
    {f : List (A1R10.Word p)} (he : 0<f.length) (hv : 0<ell)
    (P : Packed r c m delta bc f ell) (br : ℕ) (beta : Fin m →₀ ℕ)
    (i j : ℕ) (z : Code r c b × AOracleThreshold.Word p) :
    (runPackedUV q hp he hv P br beta i j z).result =
      (runSuppliedUV q hp he hv P.target beta (runFactors hp he hv P br z.1).result i j z).result := by
  unfold runPackedUV runSuppliedUV
  dsimp only
  split <;> rfl

theorem runPackedUV_cost {p r c m delta b bc ell : ℕ} (q : ℕ) (hp : 0<p)
    {f : List (A1R10.Word p)} (he : 0<f.length) (hv : 0<ell)
    (hf : (Modulus p hp f).Monic) (hd : (Modulus p hp f).natDegree=f.length)
    (P : Packed r c m delta bc f ell) (br : ℕ) (beta : Fin m →₀ ℕ)
    (hq : 0<q) (fr : r≤2^br) (fc : c≤2^bc) (fit : m+1≤2^b) (hr : r<2^q)
    (hb : ∀ k,beta k<2^q) (s : ℕ) (hl : ∀ j,(P.localRecipe j).length≤s)
    (hm : ∀ k,(P.moment k).length≤s) (i : Fin f.length) (j : Fin ell)
    (z : Code r c b × AOracleThreshold.Word p) :
    (runPackedUV q hp he hv P br beta i.val j.val z).steps≤
      gateBudget r m b q+factorBudget r c m b br bc delta s P.rows.length P.cols.length f.length ell p hp+
      productAcceptBudget (r+2) f.length ell p+2 := by
  let g := runGate q P.target beta z.1
  let t := runFactors hp he hv P br z.1
  let v := uvProductAccept hp he hv t.result i.val j.val (thresholdBits z.2)
  obtain ⟨hg,hgc⟩ := runGate_exact (rootTerms (P.denote hp)) q hq beta fit hr hb z.1
  change g.result=_ at hg
  change g.steps≤_ at hgc
  change (if g.result then ⟨v.result,g.steps+t.steps+v.steps+2⟩ else ⟨false,g.steps+2⟩ : Meter Bool).steps≤_
  cases ha : g.result with
  | false =>
    change g.steps+2≤_
    omega
  | true =>
    have hwt : ∃ w : Witness r c m, parse z.1=some w := by
      cases hz : parse z.1 with
      | none => rw [ha,hz] at hg; cases hg
      | some w => exact ⟨w,rfl⟩
    obtain ⟨w,hw⟩ := hwt
    have hcode := (parse_exact fit z.1 w).mp hw
    have ht := runFactors_exact hp he hv P br fr fc fit w s hl hm
    have hlen : t.result.length=r+2 := by
      change (runFactors hp he hv P br z.1).result.length=_
      rw [hcode]
      exact ht.1
    have htc : t.steps≤factorBudget r c m b br bc delta s P.rows.length P.cols.length f.length ell p hp := by
      change (runFactors hp he hv P br z.1).steps≤_
      rw [hcode]
      exact ht.2.2
    have hc := (uvProductAccept_exact hp he hv t.result i j (thresholdBits z.2) hf hd).2
    change v.steps≤productAcceptBudget t.result.length f.length ell p at hc
    rw [hlen] at hc
    change g.steps+t.steps+v.steps+2≤_
    omega

theorem runPackedUV_count {p r c m delta b bc ell : ℕ} (q : ℕ) (hp : 0<p)
    {f : List (A1R10.Word p)} (he : 0<f.length) (hv : 0<ell)
    (hf : (Modulus p hp f).Monic) (hd : (Modulus p hp f).natDegree=f.length)
    (P : Packed r c m delta bc f ell) (br : ℕ) (beta : Fin m →₀ ℕ)
    (hq : 0<q) (fr : r≤2^br) (fc : c≤2^bc) (fit : m+1≤2^b) (hr : r<2^q)
    (hb : ∀ k,beta k<2^q) (s : ℕ) (hl : ∀ j,(P.localRecipe j).length≤s)
    (hm : ∀ k,(P.moment k).length≤s) (i : Fin f.length) (j : Fin ell) :
    let coord := doubleCoord (Modulus p hp f) hf ell
      (⟨f.length-1-i.val,by have := i.isLt; omega⟩,⟨ell-1-j.val,by have := j.isLt; omega⟩)
    (countVerify (fun z : Code r c b × AOracleThreshold.Word p =>
      (runPackedUV q hp he hv P br beta i.val j.val z).result) : ZMod (2^p)) =
       coord (MvPolynomial.coeff beta (rootPolynomial (rootTerms (P.denote hp)))) := by
  let t := fun z : Code r c b => (runFactors hp he hv P br z).result
  have h : (fun z : Code r c b × AOracleThreshold.Word p =>
      (runPackedUV q hp he hv P br beta i.val j.val z).result) =
      fun z => (runSuppliedUV q hp he hv P.target beta (t z.1) i.val j.val z).result := by
    funext z
    exact runPackedUV_same q hp he hv P br beta i.val j.val z
  rw [h]
  exact runSuppliedUV_count q hp he hv hf hd (P.denote hp) beta hq fit hr hb t
    (fun w => (runFactors_exact hp he hv P br fr fc fit w s hl hm).2.1) i j

#print axioms runPackedUV_same
#print axioms runPackedUV_cost
#print axioms runPackedUV_count
end A1R11

