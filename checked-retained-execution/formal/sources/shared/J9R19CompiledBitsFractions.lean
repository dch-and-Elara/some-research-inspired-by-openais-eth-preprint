
import J9R19CompiledBitsPrefixes

/-! Exact unnormalised integer pairs. Fractions are never reduced and
division is implemented by crossing numerator and denominator, not
by a free rational inverse. A linear sum uses a common denominator
and the shared prefix/suffix products. -/
namespace J9R19CompiledBits
open scoped BigOperators
set_option linter.unusedSectionVars false

structure Fraction where
  num : ℤ
  den : ℤ
  deriving Repr, DecidableEq

def Fraction.value (p : Fraction) : ℚ := (p.num : ℚ) / (p.den : ℚ)

def Fraction.good (p : Fraction) : Prop := p.den ≠ 0

def Fraction.fits (b : ℕ) (p : Fraction) : Prop := Fits b p.num ∧ Fits b p.den

def Fraction.times (p q : Fraction) : Fraction := ⟨p.num*q.num,p.den*q.den⟩

def Fraction.byInteger (k : ℤ) (p : Fraction) : Fraction := ⟨k*p.num,p.den⟩

def Fraction.crossDivide (p q : Fraction) : Fraction := ⟨p.num*q.den,p.den*q.num⟩

def Fraction.subtract (p q : Fraction) : Fraction :=
  ⟨p.num*q.den-q.num*p.den,p.den*q.den⟩

theorem Fraction.times_exact (p q : Fraction) :
    (p.times q).value=p.value*q.value := by
  unfold Fraction.times Fraction.value
  push_cast
  rw [mul_div_mul_comm]

theorem Fraction.byInteger_exact (k : ℤ) (p : Fraction) :
    (p.byInteger k).value=k*p.value := by
  unfold Fraction.byInteger Fraction.value
  push_cast
  rw [mul_div_assoc]

theorem Fraction.crossDivide_exact (p q : Fraction) :
    (p.crossDivide q).value=p.value/q.value := by
  unfold Fraction.crossDivide Fraction.value
  push_cast
  simp [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc]

theorem Fraction.subtract_exact (p q : Fraction) (hp : p.good) (hq : q.good) :
    (p.subtract q).value=p.value-q.value := by
  have hp' : (p.den : ℚ) ≠ 0 := by exact_mod_cast hp
  have hq' : (q.den : ℚ) ≠ 0 := by exact_mod_cast hq
  unfold Fraction.subtract Fraction.value
  push_cast
  field_simp

theorem Fraction.crossDivide_good (p q : Fraction) (hp : p.good) (hq : q.num≠0) :
    (p.crossDivide q).good := mul_ne_zero hp hq

theorem Fraction.subtract_good (p q : Fraction) (hp : p.good) (hq : q.good) :
    (p.subtract q).good := mul_ne_zero hp hq

theorem Fraction.crossDivide_fits {b c : ℕ} {p q : Fraction} (hp : p.fits b) (hq : q.fits c) :
    (p.crossDivide q).fits (b+c) := ⟨hp.1.mul hq.2,hp.2.mul hq.1⟩

theorem Fraction.subtract_fits {b c : ℕ} {p q : Fraction} (hp : p.fits b) (hq : q.fits c) :
    (p.subtract q).fits (b+c+1) := by
  refine ⟨(hp.1.mul hq.2).sub ?_,(hp.2.mul hq.2).mono (by omega)⟩
  simpa only [Nat.add_comm] using hq.1.mul hp.2

theorem Fraction.testOne_exact (p : Fraction) (hp : p.good) :
    (p.num=p.den) ↔ p.value=1 := by
  have h : (p.den : ℚ) ≠ 0 := by exact_mod_cast hp
  rw [Fraction.value,div_eq_iff h,one_mul]
  norm_cast

structure SumRun where
  value : ℤ
  intermediates : List ℤ
  work : ℕ

def sumRun : List ℤ → SumRun
  | [] => ⟨0,[0],0⟩
  | x::xs =>
    let s := sumRun xs
    let z := x+s.value
    ⟨z,z::s.intermediates,s.work+1⟩

theorem sumRun_exact (xs : List ℤ) :
    (sumRun xs).value=xs.sum ∧ (sumRun xs).work=xs.length := by
  induction xs with
  | nil => simp [sumRun]
  | cons x xs ih => simp [sumRun,ih.1,ih.2]

theorem sumRun_fits {b : ℕ} (xs : List ℤ) (h : ∀ x∈xs, Fits b x) :
    ∀ z∈(sumRun xs).intermediates, Fits (b+xs.length) z := by
  induction xs with
  | nil => simp [sumRun,Fits]
  | cons x xs ih =>
    intro z hz
    simp only [sumRun,List.mem_cons] at hz
    rcases hz with rfl | hz
    · rw [(sumRun_exact xs).1,← List.sum_cons]
      exact sum_fits (x::xs) h
    · exact (ih (fun a ha => h a (by simp [ha])) z hz).mono (by simp)

def dens (ps : List Fraction) : List ℤ := ps.map Fraction.den

def clearedSpec : List Fraction → ℤ
  | [] => 0
  | p::ps => p.num * (dens ps).prod + p.den * clearedSpec ps

theorem clearedSpec_exact (ps : List Fraction) (h : ∀ p∈ps, p.good) :
    (Fraction.mk (clearedSpec ps) (dens ps).prod).value =
      (ps.map Fraction.value).sum := by
  have den_nonzero (xs : List Fraction) (hh : ∀ p∈xs, p.good) : (dens xs).prod ≠ 0 := by
    induction xs with
    | nil => simp [dens]
    | cons p xs ih =>
      exact mul_ne_zero (hh p (by simp)) (ih (fun a ha => hh a (by simp [ha])))
  induction ps with
  | nil => simp [clearedSpec,dens,Fraction.value]
  | cons p ps ih =>
    have htail : ∀ p∈ps, p.good := fun q hq => h q (by simp [hq])
    have hp : (p.den : ℚ) ≠ 0 := by
      exact_mod_cast (h p (by simp))
    have hd : ((dens ps).prod : ℚ) ≠ 0 := by exact_mod_cast den_nonzero _ htail
    rw [List.map_cons,List.sum_cons,← ih htail]
    change ((p.num * (dens ps).prod + p.den * clearedSpec ps : ℤ) : ℚ) /
      ((p.den * (dens ps).prod : ℤ) : ℚ) =
        (p.num : ℚ)/(p.den : ℚ) + (clearedSpec ps : ℚ)/((dens ps).prod : ℤ)
    push_cast at hd ⊢
    field_simp

def weightedTerms (ps : List Fraction) (omits : List ℤ) : List ℤ :=
  ps.zipWith (fun p o => p.num*o) omits

theorem weightedTerms_exact (ps : List Fraction) (p : ℤ) :
    (weightedTerms ps (omitProduct p (dens ps))).sum = p * clearedSpec ps := by
  induction ps generalizing p with
  | nil => simp [weightedTerms,omitProduct,dens,clearedSpec]
  | cons q ps ih =>
    unfold weightedTerms dens
    simp only [List.map_cons,omitProduct,List.zipWith_cons_cons,List.sum_cons,clearedSpec]
    change q.num * (p*(dens ps).prod) +
      (weightedTerms ps (omitProduct (p*q.den) (dens ps))).sum = _
    rw [ih]
    ring

structure ClearRun where
  result : Fraction
  words : List ℤ
  work : ℕ

/-- Renders every intermediate integer operand explicit. Its only
integer arithmetic is suffix/prefix multiplication, one multiplication
per numerator term, and an exact integer sum. -/
def clearRun (ps : List Fraction) : ClearRun :=
  let p := exclusionRun (dens ps)
  let t := weightedTerms ps p.2.excluded
  let s := sumRun t
  ⟨⟨s.value,p.1.whole⟩,(p.1.whole::(p.1.after++p.2.prefixCells++p.2.excluded))++(t++s.intermediates),
    p.1.work+p.2.work+t.length+s.work⟩

theorem clearRun_exact (ps : List Fraction) (h : ∀ p∈ps, p.good) :
    (clearRun ps).result.value=(ps.map Fraction.value).sum := by
  dsimp only [clearRun]
  rw [(sumRun_exact _).1,(exclusionRun_exact (dens ps)).1,
    (exclusionRun_exact (dens ps)).2.1,weightedTerms_exact,one_mul]
  exact clearedSpec_exact ps h

theorem clearRun_work (ps : List Fraction) : (clearRun ps).work ≤ 5*ps.length := by
  unfold clearRun
  dsimp only
  rw [(sumRun_exact _).2,(exclusionRun_exact (dens ps)).2.2]
  have ht (ss : List ℤ) : (weightedTerms ps ss).length≤ps.length := by
    unfold weightedTerms
    rw [List.length_zipWith]
    exact Nat.min_le_left _ _
  have h := ht (exclusionRun (dens ps)).2.excluded
  simp only [dens,List.length_map] at h ⊢
  omega

theorem weightedTerms_fits {b c : ℕ} (ps : List Fraction) (ss : List ℤ)
    (hp : ∀ p∈ps, p.fits b) (hs : ∀ x∈ss, Fits c x) :
    ∀ z∈weightedTerms ps ss, Fits (b+c) z := by
  induction ps generalizing ss with
  | nil => simp [weightedTerms]
  | cons p ps ih =>
    cases ss with
    | nil => simp [weightedTerms]
    | cons x ss =>
      intro z h
      simp only [weightedTerms,List.zipWith_cons_cons,List.mem_cons] at h
      rcases h with rfl | h
      · exact (hp p (by simp)).1.mul (hs x (by simp))
      · exact ih ss (fun p hp' => hp p (by simp [hp']))
          (fun x hx => hs x (by simp [hx])) z h

theorem clearRun_fits {b : ℕ} (ps : List Fraction) (h : ∀ p∈ps, p.fits b) :
    ∀ z∈(clearRun ps).words, Fits (b+(b+1)*ps.length) z := by
  let products := exclusionRun (dens ps)
  let terms := weightedTerms ps products.2.excluded
  have hd : ∀ x∈dens ps, Fits b x := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hx
    exact (h p hp).2
  have ph : ∀ z∈products.1.whole::(products.1.after++products.2.prefixCells++products.2.excluded),
      Fits (b*ps.length) z := by
    simpa only [products,dens,List.length_map] using exclusionRun_fits (b:=b) (dens ps) hd
  have ht : ∀ z∈terms, Fits (b+b*ps.length) z := by
    apply weightedTerms_fits ps _ h
    intro x hx
    apply ph x
    simp only [List.mem_cons,List.mem_append]
    tauto
  have hl : terms.length≤ps.length := by
    simp [terms,weightedTerms,List.length_zipWith]
  have hnum (x : ℤ) (hx : x∈(sumRun terms).intermediates) :
      Fits (b+(b+1)*ps.length) x := by
    apply (sumRun_fits terms ht x hx).mono
    rw [Nat.add_mul,one_mul]
    omega
  intro z hz
  change z∈(products.1.whole::(products.1.after++products.2.prefixCells++products.2.excluded))++
    (terms++(sumRun terms).intermediates) at hz
  rcases List.mem_append.mp hz with hz | hz
  · exact (ph z hz).mono (by rw [Nat.add_mul,one_mul]; omega)
  · rcases List.mem_append.mp hz with hz | hz
    · exact (ht z hz).mono (by rw [Nat.add_mul,one_mul]; omega)
    · exact hnum z hz

#print axioms Fraction.crossDivide_exact
#print axioms Fraction.subtract_exact
#print axioms Fraction.crossDivide_fits
#print axioms Fraction.subtract_fits
#print axioms Fraction.testOne_exact
#print axioms clearedSpec_exact
#print axioms clearRun_exact
#print axioms clearRun_work
#print axioms clearRun_fits
end J9R19CompiledBits
