
import J9R19CompiledBitsLinear
import J9R19CompiledBitsFractions
import J9R18CompiledStencil

/-! The explicit integer Lagrange stencil implements the actual R18
inverse at integer seat coordinates. The only comparison in the final
Boolean read is numerator = denominator. -/
namespace J9R19CompiledBits
open scoped BigOperators Polynomial
open Polynomial
set_option linter.unusedSectionVars false

theorem coeff_ofCoefficients (xs : List ℤ) (i : ℕ) :
    (ofCoefficients xs).coeff i = xs[i]?.getD 0 := by
  induction xs generalizing i with
  | nil => simp [ofCoefficients]
  | cons x xs ih =>
    cases i with
    | zero => simp [ofCoefficients]
    | succ i =>
      change (C x + X*ofCoefficients xs).coeff (i+1)=_
      rw [coeff_add,coeff_X_mul,coeff_C,if_neg (Nat.succ_ne_zero i),zero_add,ih]
      rfl

def otherSites {n : ℕ} (i : Fin n) : List (Fin n) :=
  (List.finRange n).filter (fun j => j≠i)

theorem otherSites_toFinset {n : ℕ} (i : Fin n) :
    (otherSites i).toFinset = Finset.univ.erase i := by
  ext j
  simp [otherSites,Finset.mem_erase]

theorem otherSites_nodup {n : ℕ} (i : Fin n) : (otherSites i).Nodup :=
  (List.nodup_finRange n).filter _

theorem otherSites_length {n : ℕ} (i : Fin n) : (otherSites i).length≤n := by
  simpa [otherSites] using
    (List.length_filter_le (p:=fun j : Fin n => decide (j≠i)) (l:=List.finRange n))

def siteNumerator {n : ℕ} (coord : Fin n→ℤ) (i : Fin n) : LinearRun :=
  factorRun ((otherSites i).map coord)

def siteDifferences {n : ℕ} (coord : Fin n→ℤ) (i : Fin n) : List ℤ :=
  (otherSites i).map (fun j => coord i-coord j)

def siteDenominator {n : ℕ} (coord : Fin n→ℤ) (i : Fin n) : SuffixRun :=
  suffixRun (siteDifferences coord i)

theorem siteDenominator_nonzero {n : ℕ} (coord : Fin n→ℤ) (i : Fin n)
    (distinct : Function.Injective coord) : (siteDenominator coord i).whole≠0 := by
  unfold siteDenominator siteDifferences
  rw [(suffixRun_exact _).1,← List.prod_toFinset _ (otherSites_nodup i),otherSites_toFinset]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hj).1 ((distinct h).symm))

set_option maxHeartbeats 1800000 in
theorem siteNumerator_exact {n : ℕ} (coord : Fin n→ℤ) (i : Fin n)
    (distinct : Function.Injective coord) :
    (ofCoefficients (siteNumerator coord i).coeffs).map (Int.castRingHom ℚ) =
      C ((siteDenominator coord i).whole : ℚ) * J9R18Compiled.stencil (fun j => (coord j:ℚ)) i := by
  unfold siteNumerator siteDenominator siteDifferences J9R18Compiled.stencil Lagrange.basis
  rw [factorRun_exact,(suffixRun_exact _).1,List.map_map]
  rw [← List.prod_toFinset _ (otherSites_nodup i),otherSites_toFinset,
      ← List.prod_toFinset _ (otherSites_nodup i),otherSites_toFinset]
  simp only [Function.comp_apply,Polynomial.map_prod,Polynomial.map_sub,Polynomial.map_X,
    Polynomial.map_C,Int.coe_castRingHom,Int.cast_prod,Int.cast_sub,map_prod,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  have h : ((coord i:ℚ)-(coord j:ℚ))≠0 := by
    apply sub_ne_zero.mpr
    intro he
    have hij : coord i=coord j := by exact_mod_cast he
    exact (Finset.mem_erase.mp hj).1 ((distinct hij).symm)
  unfold Lagrange.basisDivisor
  rw [← mul_assoc,← map_mul,mul_inv_cancel₀ h,map_one,one_mul]

theorem siteCoefficient_exact {n : ℕ} (coord : Fin n→ℤ) (i j : Fin n)
    (distinct : Function.Injective coord) :
    ((((siteNumerator coord i).coeffs[j.val]?).getD 0 : ℤ) : ℚ) =
      ((siteDenominator coord i).whole : ℚ) *
        (J9R18Compiled.stencil (fun k => (coord k:ℚ)) i).coeff j := by
  have h := congrArg (fun p : ℚ[X] => p.coeff j) (siteNumerator_exact coord i distinct)
  simpa only [coeff_map,Int.coe_castRingHom,coeff_ofCoefficients,coeff_C_mul] using h

def coefficientTerms {n : ℕ} (c : List ℤ) (v : Fin n→Fraction) : List Fraction :=
  List.ofFn (fun j : Fin n => (v j).byInteger (c[j.val]?.getD 0))

def termFractions {n : ℕ} (coord : Fin n→ℤ) (v : Fin n→Fraction) (i : Fin n) :
    List Fraction := coefficientTerms (siteNumerator coord i).coeffs v

structure StencilRun where
  result : Fraction
  words : List ℤ
  work : ℕ

def evaluateStencil {n : ℕ} (coord : Fin n→ℤ) (v : Fin n→Fraction) (i : Fin n) : StencilRun :=
  let c := siteNumerator coord i
  let diff := siteDifferences coord i
  let den := suffixRun diff
  let t := coefficientTerms c.coeffs v
  let s := clearRun t
  let outDen := s.result.den*den.whole
  ⟨⟨s.result.num,outDen⟩,
    c.words++(diff++((den.whole::den.after)++((t.map Fraction.num)++
      ((t.map Fraction.den)++(s.words++[outDen]))))),
    c.work+diff.length+den.work+t.length+s.work+1⟩

theorem termFractions_nonzero {n : ℕ} (coord : Fin n→ℤ) (v : Fin n→Fraction) (i : Fin n)
    (good : ∀ j, (v j).good) :
    ∀ t∈termFractions coord v i, t.good := by
  intro t ht
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ht
  exact good j

theorem clearRun_good (ps : List Fraction) (good : ∀ a∈ps, a.good) :
    (clearRun ps).result.good := by
  change (exclusionRun (dens ps)).1.whole≠0
  rw [(exclusionRun_exact _).1]
  induction ps with
  | nil => simp [dens]
  | cons p ps ih =>
    exact mul_ne_zero (good p (by simp)) (ih (fun v hv => good v (by simp [hv])))

theorem clearRun_result_fits {b : ℕ} (ps : List Fraction) (fit : ∀ p∈ps, p.fits b) :
    (clearRun ps).result.fits (b+(b+1)*ps.length) := by
  have h := clearRun_fits ps fit
  constructor
  · apply h
    apply List.mem_append.mpr
    right
    apply List.mem_append.mpr
    right
    let ts := weightedTerms ps (exclusionRun (dens ps)).2.excluded
    change (sumRun ts).value∈(sumRun ts).intermediates
    cases ts with
    | nil => simp [sumRun]
    | cons x xs => simp [sumRun]
  · apply h
    exact List.mem_append.mpr (Or.inl (by simp [clearRun]))

theorem evaluateStencil_exact {n : ℕ} (coord : Fin n→ℤ) (v : Fin n→Fraction) (i : Fin n)
    (distinct : Function.Injective coord) (good : ∀ j, (v j).good) :
    (evaluateStencil coord v i).result.value =
      J9R18Compiled.stencilInverse (fun j => (coord j:ℚ)) (fun j => (v j).value) i := by
  let t := termFractions coord v i
  let den := (siteDenominator coord i).whole
  have hd : (den : ℚ)≠0 := by exact_mod_cast siteDenominator_nonzero coord i distinct
  change ((clearRun t).result.num : ℚ) / (((clearRun t).result.den*den : ℤ):ℚ) = _
  rw [Int.cast_mul,← div_div,← Fraction.value,clearRun_exact t (termFractions_nonzero coord v i good)]
  change ((t.map Fraction.value).sum / (den:ℚ)) = _
  dsimp only [t,termFractions,coefficientTerms]
  rw [List.map_ofFn,List.sum_ofFn]
  simp only [Function.comp_apply,Fraction.byInteger_exact,siteCoefficient_exact coord i _ distinct,mul_assoc]
  change (∑ j : Fin n, (den:ℚ) *
    ((J9R18Compiled.stencil (fun k => (coord k:ℚ)) i).coeff j * (v j).value)) / (den:ℚ) = _
  rw [← Finset.mul_sum,mul_div_cancel_left₀ _ hd]
  rfl

theorem evaluateStencil_good {n : ℕ} (coord : Fin n→ℤ) (v : Fin n→Fraction) (i : Fin n)
    (distinct : Function.Injective coord) (good : ∀ j, (v j).good) :
    (evaluateStencil coord v i).result.good :=
  mul_ne_zero (clearRun_good _ (termFractions_nonzero coord v i good))
    (siteDenominator_nonzero coord i distinct)

theorem evaluateStencil_work {n : ℕ} (coord : Fin n→ℤ) (v : Fin n→Fraction) (i : Fin n) :
    (evaluateStencil coord v i).work ≤ n*(n+1)+8*n+1 := by
  have hc := (factorRun_count ((otherSites i).map coord)).2
  have hd := (suffixRun_exact (siteDifferences coord i)).2.2
  have ht := clearRun_work (termFractions coord v i)
  have l : (siteDifferences coord i).length=(otherSites i).length := by simp [siteDifferences]
  have m : (termFractions coord v i).length=n := by simp [termFractions,coefficientTerms]
  have h := otherSites_length i
  have q : (otherSites i).length*((otherSites i).length+1)≤n*(n+1) :=
    Nat.mul_le_mul h (Nat.add_le_add_right h _)
  dsimp only [evaluateStencil]
  change (siteNumerator coord i).work + (siteDifferences coord i).length +
    (siteDenominator coord i).work + (termFractions coord v i).length +
    (clearRun (termFractions coord v i)).work + 1 ≤ _
  unfold siteNumerator siteDenominator
  rw [hc,hd,List.length_map,l,m]
  omega

#print axioms coeff_ofCoefficients
#print axioms siteDenominator_nonzero
#print axioms siteNumerator_exact
#print axioms siteCoefficient_exact
#print axioms clearRun_good
#print axioms clearRun_result_fits
#print axioms evaluateStencil_exact
#print axioms evaluateStencil_good
#print axioms evaluateStencil_work
end J9R19CompiledBits
