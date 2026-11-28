
import J6R15SignedReadNative
import J9R19CompiledBitsFractions
import J9R19CompiledBitsPrimitives

/-! The final raw-CNF readout needs only the value at one. On the
actual odd sample mesh, evaluate the Lagrange factors over unreduced
integer pairs and never call a rational inverse in this program. -/
namespace J6R22RootReadout
open scoped BigOperators Polynomial Classical
open Polynomial J9R19CompiledBits
set_option linter.unusedSectionVars false
set_option maxHeartbeats 9500000

def lagFactor (ni di nj dj : ℤ) : Fraction :=
  ⟨(dj-nj)*di,ni*dj-nj*di⟩

theorem lag_factor_nonzero (ni di nj dj : ℤ) (hd : di≠0) (hd' : dj≠0)
    (distinct : (ni:ℚ)/di≠(nj:ℚ)/dj) :
    (lagFactor ni di nj dj).good := by
  intro h
  apply distinct
  have n : ni*dj=nj*di := sub_eq_zero.mp h
  have u : (di:ℚ)≠0 := by exact_mod_cast hd
  have v : (dj:ℚ)≠0 := by exact_mod_cast hd'
  apply (div_eq_div_iff u v).mpr
  exact_mod_cast n

theorem lag_factor_value (ni di nj dj : ℤ) (hd : di≠0) (hd' : dj≠0)
    (distinct : (ni:ℚ)/di≠(nj:ℚ)/dj) :
    (lagFactor ni di nj dj).value=(1-(nj:ℚ)/dj)/((ni:ℚ)/di-(nj:ℚ)/dj) := by
  have n : (ni*dj-nj*di:ℤ)≠0 := lag_factor_nonzero ni di nj dj hd hd' distinct
  have qd : (di:ℚ)≠0 := by exact_mod_cast hd
  have qd' : (dj:ℚ)≠0 := by exact_mod_cast hd'
  have Q : (ni:ℚ)*dj-(nj:ℚ)*di≠0 := by exact_mod_cast n
  unfold Fraction.value lagFactor
  push_cast
  have edge : (ni:ℚ)/di-(nj:ℚ)/dj = ((ni:ℚ)*dj-(nj:ℚ)*di)/((di:ℚ)*dj) := by
    field_simp
  have tail : 1-(nj:ℚ)/dj=(dj-(nj:ℚ))/dj := by field_simp
  rw [edge,tail]
  field_simp

theorem lag_factor_fits (b : ℕ) (ni di nj dj : ℤ)
    (a : Fits b ni) (c : Fits b di) (v : Fits b nj) (z : Fits b dj) :
    (lagFactor ni di nj dj).fits (2*b+1) := by
  change Fits (2*b+1) ((dj-nj)*di) ∧ Fits (2*b+1) (ni*dj-nj*di)
  constructor
  · exact ((z.sub v).mul c).mono (by omega)
  · exact ((a.mul z).sub (v.mul c)).mono (by omega)

def unitFraction : Fraction := ⟨1,1⟩

def fractionProduct : List Fraction→Fraction
  | [] => unitFraction
  | q::qs => q.times (fractionProduct qs)

theorem fraction_product_value (L : List Fraction) :
    (fractionProduct L).value=(L.map Fraction.value).prod := by
  induction L with
  | nil => simp [fractionProduct,unitFraction,Fraction.value]
  | cons q qs ih => simp only [fractionProduct,Fraction.times_exact,ih,List.map_cons,List.prod_cons]

theorem fraction_product_good (L : List Fraction) (h : ∀ a∈L,a.good) :
    (fractionProduct L).good := by
  induction L with
  | nil => simp [fractionProduct,unitFraction,Fraction.good]
  | cons q qs ih =>
    exact mul_ne_zero (h q List.mem_cons_self) (ih (fun a ha=>h a (List.mem_cons_of_mem _ ha)))

theorem fraction_product_fits (b : ℕ) (L : List Fraction) (h : ∀ a∈L,a.fits b) :
    (fractionProduct L).fits (b*L.length) := by
  induction L with
  | nil => exact ⟨Fits.one _,Fits.one _⟩
  | cons q qs ih =>
    obtain ⟨hn,hd⟩ := h q List.mem_cons_self
    obtain ⟨n,d⟩ := ih (fun a ha=>h a (List.mem_cons_of_mem _ ha))
    change Fits (b*(qs.length+1)) (q.num*(fractionProduct qs).num) ∧
      Fits (b*(qs.length+1)) (q.den*(fractionProduct qs).den)
    rw [Nat.mul_add,mul_one,add_comm (b*qs.length) b]
    exact ⟨hn.mul n,hd.mul d⟩

def otherSites (m : ℕ) (i : Fin (m+1)) : List (Fin (m+1)) :=
  (List.finRange (m+1)).filter (fun j=>decide (j≠i))

theorem other_sites_chart (m : ℕ) (i : Fin (m+1)) :
    (otherSites m i).Nodup ∧
      (otherSites m i).toFinset=Finset.univ.erase i := by
  constructor
  · exact (List.nodup_finRange _).filter _
  · ext j
    simp [otherSites,Finset.mem_erase]

theorem other_sites_count (m : ℕ) (i : Fin (m+1)) : (otherSites m i).length=m := by
  obtain ⟨h,h'⟩ := other_sites_chart m i
  rw [← List.toFinset_card_of_nodup h,h',Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ,Fintype.card_fin]
  omega

def termAtOne (m : ℕ) (n d A : Fin (m+1)→ℤ) (i : Fin (m+1)) : Fraction :=
  let s : Fraction := ⟨A i,(powerRun (d i) m).value⟩
  s.times (fractionProduct ((otherSites m i).map (fun j=>lagFactor (n i) (d i) (n j) (d j))))

theorem term_at_one_value (m : ℕ) (n d A : Fin (m+1)→ℤ) (i : Fin (m+1))
    (hd : ∀ j,d j≠0) (inj : Function.Injective (fun j => (n j:ℚ)/d j)) :
    (termAtOne m n d A i).value=((A i:ℚ)/(d i:ℚ)^m)*
      (Lagrange.basis Finset.univ (fun j=>(n j:ℚ)/d j) i).eval 1 := by
  unfold termAtOne
  rw [Fraction.times_exact,fraction_product_value,(powerRun_exact _ _).1]
  change ((A i:ℚ)/((d i)^m:ℤ))*_ = _
  rw [Int.cast_pow,List.map_map]
  congr 1
  unfold Lagrange.basis
  simp only [Polynomial.eval_prod,Lagrange.basisDivisor,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_sub,Polynomial.eval_X]
  rw [← (other_sites_chart m i).2,← List.prod_toFinset (Fraction.value ∘ fun j=>lagFactor (n i) (d i) (n j) (d j))
    (other_sites_chart m i).1]
  refine Finset.prod_congr rfl (fun j hj=>?_ )
  have ne : j≠i := by simpa [otherSites] using hj
  have diff : (n i:ℚ)/d i≠(n j:ℚ)/d j := fun h=>ne (inj h).symm
  rw [Function.comp_apply,lag_factor_value _ _ _ _ (hd _) (hd _) diff,div_eq_mul_inv,mul_comm]

theorem term_at_one_good (m : ℕ) (n d A : Fin (m+1)→ℤ) (i : Fin (m+1))
    (hd : ∀ j,d j≠0) (inj : Function.Injective (fun j => (n j:ℚ)/d j)) :
    (termAtOne m n d A i).good := by
  apply mul_ne_zero
  · rw [(powerRun_exact _ _).1]; exact pow_ne_zero _ (hd _)
  · apply fraction_product_good
    intro z hz
    obtain ⟨j,jm,rfl⟩ := List.mem_map.mp hz
    have ne : j≠i := by simpa [otherSites] using jm
    exact lag_factor_nonzero _ _ _ _ (hd _) (hd _) (fun h=>ne (inj h).symm)

def baseTermWidth (m b p : ℕ) := p+b*m+(2*b+1)*m

theorem term_at_one_fits (m b p : ℕ) (n d A : Fin (m+1)→ℤ) (i : Fin (m+1))
    (hn : ∀ j,Fits b (n j)) (hd : ∀ j,Fits b (d j)) (hA : ∀ j,Fits p (A j)) :
    (termAtOne m n d A i).fits (baseTermWidth m b p) := by
  have e := fraction_product_fits (2*b+1)
    ((otherSites m i).map (fun j=>lagFactor (n i) (d i) (n j) (d j))) (by
      intro z hz
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp hz
      exact lag_factor_fits b _ _ _ _ (hn i) (hd i) (hn j) (hd j))
  rw [List.length_map,other_sites_count] at e
  have hd' : Fits (b*m) ((powerRun (d i) m).value) := by
    rw [(powerRun_exact _ _).1]; exact (hd i).pow m
  constructor
  · exact ((hA i).mul e.1).mono (by unfold baseTermWidth; omega)
  · exact (hd'.mul e.2).mono (by unfold baseTermWidth; omega)

def outerTermTape (m : ℕ) (n d A : Fin (m+1)→ℤ) : List Fraction :=
  List.ofFn (termAtOne m n d A)

def outerAtOne (m : ℕ) (n d A : Fin (m+1)→ℤ) : Fraction :=
  (clearRun (outerTermTape m n d A)).result

theorem outer_at_one_exact (m : ℕ) (n d A : Fin (m+1)→ℤ)
    (hd : ∀ j,d j≠0) (inj : Function.Injective (fun j => (n j:ℚ)/d j)) :
    (outerAtOne m n d A).value =
      (Lagrange.interpolate Finset.univ (fun j => (n j:ℚ)/d j)
        (fun i=> (A i:ℚ)/(d i:ℚ)^m)).eval 1 := by
  have terms : ∀ p∈outerTermTape m n d A,p.good := by
    intro p hp
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    exact term_at_one_good m n d A i hd inj
  unfold outerAtOne
  rw [clearRun_exact _ terms]
  unfold outerTermTape
  rw [List.map_ofFn,List.sum_ofFn]
  unfold Lagrange.interpolate
  simp only [LinearMap.coe_mk,AddHom.coe_mk,Polynomial.eval_finset_sum,Polynomial.eval_mul,Polynomial.eval_C]
  exact Finset.sum_congr rfl fun i _=>term_at_one_value m n d A i hd inj

theorem outer_clear_words_fit (m b p : ℕ) (n d A : Fin (m+1)→ℤ)
    (hn : ∀ j,Fits b (n j)) (hd : ∀ j,Fits b (d j)) (hA : ∀ j,Fits p (A j)) :
    let B := baseTermWidth m b p
    let s := clearRun (outerTermTape m n d A)
    (∀ w∈s.words,Fits (B+(B+1)*(m+1)) w) ∧ s.work≤5*(m+1) := by
  have fs : ∀ x∈outerTermTape m n d A,x.fits (baseTermWidth m b p) := by
    intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact term_at_one_fits m b p n d A i hn hd hA
  constructor
  · simpa only [outerTermTape,List.length_ofFn] using clearRun_fits _ fs
  · simpa only [outerTermTape,List.length_ofFn] using clearRun_work (outerTermTape m n d A)

#print axioms lag_factor_nonzero
#print axioms lag_factor_value
#print axioms lag_factor_fits
#print axioms other_sites_count
#print axioms term_at_one_value
#print axioms term_at_one_good
#print axioms term_at_one_fits
#print axioms outer_at_one_exact
#print axioms outer_clear_words_fit
end J6R22RootReadout
