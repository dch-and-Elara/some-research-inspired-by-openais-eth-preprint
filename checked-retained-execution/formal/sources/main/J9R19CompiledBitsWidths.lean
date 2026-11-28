
import J9R19CompiledBitsStencil

/-! Explicit integer width and operation bound for the complete Lagrange
read of one recovered port. Every written scalar is covered, including
the subtractions forming coordinate differences and the shared
common-denominator products. -/
namespace J9R19CompiledBits
open scoped BigOperators
set_option linter.unusedSectionVars false

theorem Fits.listGet {b : ℕ} (xs : List ℤ) (j : ℕ)
    (h : ∀ z∈xs, Fits b z) : Fits b (xs[j]?.getD 0) := by
  induction xs generalizing j with
  | nil => simpa using Fits.zero b
  | cons x xs ih =>
    cases j with
    | zero =>
      simpa using h x (List.mem_cons_self)
    | succ j =>
      simpa using ih j (fun z hz => h z (List.mem_cons_of_mem _ hz))

theorem evaluateStencil_word_width {n a b : ℕ} (coord : Fin n→ℤ) (v : Fin n→Fraction)
    (i : Fin n) (cf : ∀ j, Fits a (coord j)) (vf : ∀ j, (v j).fits b) :
    let W := (a+1)*n
    let B := W+b
    let E := B+(B+1)*n
    let q := evaluateStencil coord v i
    q.result.fits (E+W) ∧ (∀ z∈q.words, Fits (E+W) z) := by
  dsimp only
  let W := (a+1)*n
  let B := W+b
  let E := B+(B+1)*n
  change (evaluateStencil coord v i).result.fits (E+W) ∧
    (∀ z∈(evaluateStencil coord v i).words, Fits (E+W) z)
  let xs := (otherSites i).map coord
  let c := siteNumerator coord i
  let dif := siteDifferences coord i
  let den := siteDenominator coord i
  let terms := termFractions coord v i
  let s := clearRun terms
  have hl : xs.length≤n := by simpa [xs] using otherSites_length i
  have hld : dif.length≤n := by simpa [dif,siteDifferences] using otherSites_length i
  have ht : terms.length=n := by simp [terms,termFractions,coefficientTerms]
  have hc0 := factorRun_fits xs (fun x hx => by
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hx
    exact cf j)
  have hc1 (x : ℤ) (hx : x∈c.coeffs) : Fits W x :=
    (hc0.1 x hx).mono (Nat.mul_le_mul_left _ hl)
  have hc2 (x : ℤ) (hx : x∈c.words) : Fits W x :=
    (hc0.2 x hx).mono (Nat.mul_le_mul_left _ hl)
  have hd (x : ℤ) (hx : x∈dif) : Fits (a+1) x := by
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hx
    exact (cf i).sub (cf j)
  have hda : Fits W den.whole := by
    change Fits W (suffixRun dif).whole
    rw [(suffixRun_exact dif).1]
    exact (product_fits dif hd).mono (Nat.mul_le_mul_left _ hld)
  have hdb (x : ℤ) (hx : x∈den.after) : Fits W x := by
    change x∈(suffixRun dif).after at hx
    rw [(suffixRun_exact dif).2.1] at hx
    exact (tailProducts_fits dif hd x hx).mono (Nat.mul_le_mul_left _ hld)
  have htf (p : Fraction) (hp : p∈terms) : p.fits B := by
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hp
    refine ⟨(Fits.listGet c.coeffs j.val hc1).mul (vf j).1,(vf j).2.mono ?_⟩
    dsimp [B]
    omega
  have hsf : s.result.fits E := by
    simpa only [s,E,ht] using clearRun_result_fits terms htf
  have hsw (z : ℤ) (hz : z∈s.words) : Fits E z := by
    simpa only [E,ht] using clearRun_fits terms htf z hz
  have hout : Fits (E+W) (s.result.den*den.whole) := hsf.2.mul hda
  have leW : W≤E+W := by omega
  have leB : B≤E+W := by dsimp [E]; omega
  have leE : E≤E+W := by omega
  constructor
  · exact ⟨hsf.1.mono leE,hout⟩
  · intro z hz
    change z∈c.words++(dif++((den.whole::den.after)++((terms.map Fraction.num)++
      ((terms.map Fraction.den)++(s.words++[s.result.den*den.whole]))))) at hz
    rcases List.mem_append.mp hz with h0|hz
    · exact (hc2 z h0).mono leW
    rcases List.mem_append.mp hz with h0|hz
    · have iff : a+1≤W := by
        have h0n : 1≤n := by have hi := i.isLt; omega
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left (a+1) h0n
      exact (hd z h0).mono (iff.trans leW)
    rcases List.mem_append.mp hz with h0|hz
    · rcases List.mem_cons.mp h0 with rfl|h0
      · exact hda.mono leW
      · exact (hdb z h0).mono leW
    rcases List.mem_append.mp hz with h0|hz
    · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp h0
      exact (htf p hp).1.mono leB
    rcases List.mem_append.mp hz with h0|hz
    · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp h0
      exact (htf p hp).2.mono leB
    rcases List.mem_append.mp hz with h0|hz
    · exact (hsw z h0).mono leE
    · simp only [List.mem_singleton] at hz
      simpa only [hz] using hout

structure NormalizeRun where
  result : Fraction
  words : List ℤ
  work : ℕ

/-- Cost six scalar operations: two crossed products, two numerator
products plus one subtraction, and one denominator product. -/
def normalizeRun (obs scale background : Fraction) : NormalizeRun :=
  let u := obs.crossDivide scale
  let p := u.num*background.den
  let q := background.num*u.den
  let z : Fraction := ⟨p-q,u.den*background.den⟩
  ⟨z,[u.num,u.den,p,q,z.num,z.den],6⟩

theorem normalizeRun_exact (obs scale background : Fraction)
    (ho : obs.good) (hs : scale.num≠0) (hb : background.good) :
    (normalizeRun obs scale background).result.value =
      obs.value/scale.value - background.value := by
  change ((obs.crossDivide scale).subtract background).value = _
  rw [Fraction.subtract_exact _ _ (Fraction.crossDivide_good _ _ ho hs) hb,
    Fraction.crossDivide_exact]

theorem normalizeRun_good (obs scale background : Fraction)
    (ho : obs.good) (hs : scale.num≠0) (hb : background.good) :
    (normalizeRun obs scale background).result.good :=
  Fraction.subtract_good _ _ (Fraction.crossDivide_good _ _ ho hs) hb

theorem normalizeRun_total_work (obs scale background : Fraction) :
    (normalizeRun obs scale background).work=6 := rfl

theorem normalizeRun_fits {b : ℕ} (obs scale background : Fraction)
    (ho : obs.fits b) (hs : scale.fits b) (hb : background.fits b) :
    (normalizeRun obs scale background).result.fits (3*b+1) ∧
      (∀ z∈(normalizeRun obs scale background).words, Fits (3*b+1) z) := by
  let u := obs.crossDivide scale
  let z := u.subtract background
  have hu := Fraction.crossDivide_fits ho hs
  have hz := Fraction.subtract_fits hu hb
  have eq : b+b+b+1=3*b+1 := by omega
  rw [← eq]
  refine ⟨hz,?_⟩
  intro n hn
  change n∈[u.num,u.den,u.num*background.den,background.num*u.den,z.num,z.den] at hn
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
  rcases hn with rfl|rfl|rfl|rfl|rfl|rfl
  · exact hu.1.mono (by omega)
  · exact hu.2.mono (by omega)
  · exact (hu.1.mul hb.2).mono (by omega)
  · exact (hb.1.mul hu.2).mono (by omega)
  · exact hz.1
  · exact hz.2

#print axioms Fits.listGet
#print axioms evaluateStencil_word_width
#print axioms normalizeRun_exact
#print axioms normalizeRun_good
#print axioms normalizeRun_total_work
#print axioms normalizeRun_fits
end J9R19CompiledBits
