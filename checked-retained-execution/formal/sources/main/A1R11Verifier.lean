import A1R11Gate
import A1R10Count

/-! Combining literal A1 legality gates with the R10 unsigned UV
threshold. Here the row-factor tape for one raw code is still supplied.
The next row-compiler track removes this witness-dependent tape oracle. -/

open scoped BigOperators
namespace A1R11
open AOracleMachineTime AOracleMachineTimeTape AOracleCoordinates
open AOracleSuccinct AOracleWitness AOracleThreshold A1R10

def productAcceptBudget (r e ell p : ℕ) : ℕ :=
  ell*(e*p+1)+4+r*(3432*((ell+1)^2*(e+1)^2*(p+1)^2)+4)+
  ell*(e*p+2)+e*(p+2)+10*p+6

/-- No typed witness parse is called, even on a malformed field. -/
def runSuppliedUV {r c m b p : ℕ} (q : ℕ) (hp : 0<p)
    {f : List (A1R10.Word p)} {ell : ℕ} (he : 0<f.length) (hv : 0<ell)
    (target : Fin r → Fin m → Bool) (beta : Fin m →₀ ℕ)
    (tape : List (UVBlock f ell)) (i j : ℕ) (z : Code r c b × AOracleThreshold.Word p) :
    Meter Bool :=
  let g := runGate q target beta z.1
  if g.result then
    let v := uvProductAccept hp he hv tape i j (thresholdBits z.2)
    ⟨v.result,g.steps+v.steps+2⟩
  else ⟨false,g.steps+2⟩

theorem runSuppliedUV_exact {r c m b p : ℕ} (q : ℕ) (hp : 0<p)
    {f : List (A1R10.Word p)} {ell : ℕ} (he : 0<f.length) (hv : 0<ell)
    (hf : (Modulus p hp f).Monic) (hd : (Modulus p hp f).natDegree=f.length)
    (S : RootTerms r c m (Truncated (Modulus p hp f) ell)) (beta : Fin m →₀ ℕ)
    (hq : 0<q) (fit : m+1≤2^b) (hr : r<2^q) (hb : ∀ k,beta k<2^q)
    (t : Code r c b → List (UVBlock f ell))
    (hw : ∀ w, (List.map (uvRead hp f ell) (t (encode fit w))).prod=weight S w)
    (i : Fin f.length) (j : Fin ell) (z : Code r c b × AOracleThreshold.Word p) :
    let coord := doubleCoord (Modulus p hp f) hf ell
      (⟨f.length-1-i.val,by have := i.isLt; omega⟩,⟨ell-1-j.val,by have := j.isLt; omega⟩)
    (runSuppliedUV q hp he hv S.isTarget beta (t z.1) i.val j.val z).result =
      verifier parse (valid S beta) (fun w => coord (weight S w)) z ∧
    (runSuppliedUV q hp he hv S.isTarget beta (t z.1) i.val j.val z).steps≤
      gateBudget r m b q+productAcceptBudget (t z.1).length f.length ell p+2 := by
  let g := runGate q S.isTarget beta z.1
  obtain ⟨hg,hc⟩ := runGate_exact S q hq beta fit hr hb z.1
  change g.result=_ at hg
  change g.steps≤_ at hc
  let v := uvProductAccept hp he hv (t z.1) i.val j.val (thresholdBits z.2)
  obtain ⟨hread,hvc⟩ := uvProductAccept_exact hp he hv (t z.1) i j (thresholdBits z.2) hf hd
  change v.steps≤productAcceptBudget (t z.1).length f.length ell p at hvc
  unfold runSuppliedUV verifier
  dsimp only
  change (if g.result then ⟨v.result,g.steps+v.steps+2⟩ else ⟨false,g.steps+2⟩ : Meter Bool).result=_
    ∧ (if g.result then ⟨v.result,g.steps+v.steps+2⟩ else ⟨false,g.steps+2⟩ : Meter Bool).steps≤_
  rw [hg]
  cases hz : parse z.1 with
  | none =>
    simp only [Option.elim_none,Bool.false_eq_true,if_false,true_and]
    omega
  | some w =>
    have hc' : z.1=encode fit w := (parse_exact fit z.1 w).mp hz
    have hwt : (List.map (uvRead hp f ell) (t z.1)).prod=weight S w := by
      rw [hc',hw]
    change (v.result=true ↔ bitsValue (encodeBits p z.2.val)<_) at hread
    rw [encodeBits_exact p _ z.2.isLt,hwt] at hread
    cases hv' : valid S beta w with
    | false =>
      simp only [Option.elim_some,hv',Bool.false_eq_true,if_false,Bool.false_and,true_and]
      omega
    | true =>
      simp only [Option.elim_some,hv',if_true,Bool.true_and]
      constructor
      · apply Bool.eq_iff_iff.mpr
        simpa only [decide_eq_true_eq] using hread
      · omega

theorem runSuppliedUV_count {r c m b p : ℕ} (q : ℕ) (hp : 0<p)
    {f : List (A1R10.Word p)} {ell : ℕ} (he : 0<f.length) (hv : 0<ell)
    (hf : (Modulus p hp f).Monic) (hd : (Modulus p hp f).natDegree=f.length)
    (L : Recipes (Truncated (Modulus p hp f) ell) r c m delta) (beta : Fin m →₀ ℕ)
    (hq : 0<q) (fit : m+1≤2^b) (hr : r<2^q) (hb : ∀ k,beta k<2^q)
    (t : Code r c b → List (UVBlock f ell))
    (hw : ∀ w, (List.map (uvRead hp f ell) (t (encode fit w))).prod=weight (rootTerms L) w)
    (i : Fin f.length) (j : Fin ell) :
    let coord := doubleCoord (Modulus p hp f) hf ell
      (⟨f.length-1-i.val,by have := i.isLt; omega⟩,⟨ell-1-j.val,by have := j.isLt; omega⟩)
    (countVerify (fun z => (runSuppliedUV q hp he hv L.target beta (t z.1) i.val j.val z).result)
      : ZMod (2^p)) = coord (MvPolynomial.coeff beta (rootPolynomial (rootTerms L))) := by
  let coord := doubleCoord (Modulus p hp f) hf ell
    (⟨f.length-1-i.val,by have := i.isLt; omega⟩,⟨ell-1-j.val,by have := j.isLt; omega⟩)
  have h : (fun z => (runSuppliedUV q hp he hv L.target beta (t z.1) i.val j.val z).result) =
      verifier parse (valid (rootTerms L) beta) (fun w => coord (weight (rootTerms L) w)) := by
    funext z
    exact (runSuppliedUV_exact q hp he hv hf hd (rootTerms L) beta hq fit hr hb t hw i j z).1
  rw [h]
  exact requested_coordinate_from_count (rootTerms L) beta fit (fun _ : Unit => coord) ()

#print axioms runSuppliedUV_exact
#print axioms runSuppliedUV_count
end A1R11
