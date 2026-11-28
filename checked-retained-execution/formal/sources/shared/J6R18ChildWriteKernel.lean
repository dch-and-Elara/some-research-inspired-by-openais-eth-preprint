import AOracleSuccinctPhysical
import J6R9PacketLocal
import J6R9PacketReceive

/-! Agreement of the priced A1 unit-only kernel with the finite
receiving ring used by J6. All comparisons start in the odd-local
coefficient ring; there is no reduction homomorphism from ℚ. -/
namespace J6R18ChildWrite
open scoped BigOperators Polynomial
open Polynomial DenominatorBudget P1DyadicGrid P1DyadicGridBridge
open AOracleSuccinctNative AOracleSuccinctKernel AOracleSuccinctPhysical
open J6R9PacketCoeff J6R9PacketLocal

variable {R : Type*} [CommRing R]

theorem inverse_unique {d y v : R} (h₁ : d*y=1) (h₂ : d*v=1) : y=v := by
  calc
    y=(d*v)*y := by rw [h₂,one_mul]
    _=v*(d*y) := by ring
    _=v := by rw [h₁,mul_one]

theorem odd_reciprocal_same (p : ℕ) (hnil : (2:R)^p=0) (d : ℤ) (hd : Odd d) :
    J6ZeroTransport.oddReciprocal R p d=oddInverse p (d:R) := by
  have hOdd : ¬ (2:ℤ) ∣ d := fun v => (Int.not_even_iff_odd.mpr hd) (even_iff_two_dvd.mpr v)
  exact inverse_unique (J6ZeroTransport.oddReciprocal_valid p hnil d hOdd)
    (inverse_int p hnil d hd)

theorem reduction_rho (p : ℕ) (hnil : (2:R)^p=0) {a : ℕ} {t : ℤ} (ht : t∈grid a) :
    J6ZeroTransport.reduceAt p hnil (rho a t)=
      (oddPartsAt a t:R)*oddInverse p (oddDerivative a:R) := by
  have hOdd := oddDerivative_odd a
  have hb : ¬ (2:ℤ) ∣ oddDerivative a := fun v =>
    (Int.not_even_iff_odd.mpr hOdd) (even_iff_two_dvd.mpr v)
  rw [J6ZeroTransport.reduce_fraction p hnil (rho a t) (oddPartsAt a t) (oddDerivative a)
    hb ((rho_rat ht).trans (normalized_derivative_ratio (F:=ℚ) ht)),odd_reciprocal_same p hnil _ hOdd]

theorem reduction_slope (p : ℕ) (hnil : (2:R)^p=0) {a : ℕ} {t q : ℤ}
    (ht : t∈grid a) (hq : q∈grid a) (hne : t≠q) :
    J6ZeroTransport.reduceAt p hnil (J6ActiveLocalFactor.slope a t q)=
      (2:R)^(a+1-padicValInt 2 (t-q))*oddInverse p (oddWord (t-q):R) := by
  let v := padicValInt 2 (t-q)
  let d := oddWord (t-q)
  have hv : v≤a+1 := (grid_difference_valuation_le ht hq hne).trans (Nat.le_succ _)
  obtain ⟨ho,he⟩ := oddWord_factor (sub_ne_zero.mpr hne)
  have hd : Odd d := ho
  have hOdd : ¬ (2:ℤ) ∣ d := fun v => (Int.not_even_iff_odd.mpr hd) (even_iff_two_dvd.mpr v)
  have hvR : (t:ℚ)-(q:ℚ)=(2:ℚ)^v*(d:ℚ) := by
    simpa only [Int.cast_sub,Int.cast_mul,cast_pow₂] using congrArg (fun n : ℤ=>(n:ℚ)) he
  have hvQ : (2:ℚ)^(a+1)=(2:ℚ)^v*(2:ℚ)^(a+1-v) := by
    rw [← pow_add,Nat.add_sub_of_le hv]
  have hRat :
      twoLocalRat (J6ActiveLocalFactor.slope a t q)=(((2:ℤ)^(a+1-v):ℤ):ℚ)/(d:ℚ) := by
    rw [slope_rat ht hq hne,hvQ,hvR,mul_div_mul_left _ _ (pow_ne_zero _ (by decide))]
    simp
  rw [J6ZeroTransport.reduce_fraction p hnil _ _ _ hOdd hRat,odd_reciprocal_same p hnil _ hd]
  push_cast
  rfl

def ratioFactor (p a : ℕ) (t q : ℤ) (z : R) : R :=
  1+(2:R)^(a+1-padicValInt 2 (t-q))*z*oddInverse p (oddWord (t-q):R)

theorem factor_read (p : ℕ) (hnil : (2:R)^p=0) {a : ℕ} {t : ℤ} (ht : t∈grid a)
    (s : Finset ℤ) (hs : s⊆(grid a).erase t) (z : R) :
    (factors a t s).eval₂ (J6ZeroTransport.reduceAt p hnil) z=
      ∏ q ∈ s,ratioFactor p a t q z := by
  let E := eval₂RingHom (J6ZeroTransport.reduceAt p hnil) z
  change E (factors a t s)=_
  unfold factors
  rw [map_prod]
  refine Finset.prod_congr rfl (fun q hq=>?_)
  obtain ⟨he,hg⟩ := Finset.mem_erase.mp (hs hq)
  simp only [map_add,map_one,map_mul]
  change 1+(C (J6ActiveLocalFactor.slope a t q)).eval₂ (J6ZeroTransport.reduceAt p hnil) z *
    (X : TwoLocal[X]).eval₂ (J6ZeroTransport.reduceAt p hnil) z=_
  rw [eval₂_C,eval₂_X,reduction_slope p hnil ht hg (Ne.symm he),ratioFactor]
  ring

theorem cHat_read (p : ℕ) (hnil : (2:R)^p=0) {a : ℕ} {t : ℤ} (ht : t∈grid a) (z : R) :
    (cHat a t).eval₂ (J6ZeroTransport.reduceAt p hnil) z=
      ((oddPartsAt a t:R)*oddInverse p (oddDerivative a:R))*
        ∏ q ∈ (grid a).erase t,ratioFactor p a t q z := by
  change (C (rho a t)*factors a t ((grid a).erase t)).eval₂ (J6ZeroTransport.reduceAt p hnil) z=_
  rw [eval₂_mul,eval₂_C,reduction_rho p hnil ht,factor_read p hnil ht _ (fun _ h=>h) z]

theorem ratioFactor_cleared (p : ℕ) (hnil : (2:R)^p=0) (a : ℕ) {t q : ℤ} (h : t≠q) (z : R) :
    (oddWord (t-q):R)*ratioFactor p a t q z=normFactor a t q z := by
  have hinv := inverse_int p hnil _ (oddWord_factor (sub_ne_zero.mpr h)).1
  unfold ratioFactor normFactor shiftWord
  calc
    _=(oddWord (t-q):R)+(2:R)^(a+1-padicValInt 2 (t-q))*z*
        ((oddWord (t-q):R)*oddInverse p (oddWord (t-q):R)) := by ring
    _=_ := by rw [hinv,mul_one]

theorem normProd_cleared (p : ℕ) (hnil : (2:R)^p=0) (a : ℕ) (t : ℤ)
    (s : Finset ℤ) (hne : ∀ q∈s,t≠q) (z : R) :
    (∏ q ∈ s, (oddWord (t-q):R))*(∏ q ∈ s,ratioFactor p a t q z)=
      ∏ q ∈ s,normFactor a t q z := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun q hq=>ratioFactor_cleared p hnil a (hne q hq) z)

theorem W_is_modular (p : ℕ) (hnil : (2:R)^p=0) {a : ℕ} {t k : ℤ}
    (ht : t∈grid a) (hk : k∈grid a) (z : R) :
    (W a t k).eval₂ (J6ZeroTransport.reduceAt p hnil) z=modular p a t k z := by
  classical
  by_cases he : k=t
  · subst k
    rw [W,if_pos rfl,cHat_read p hnil ht,modular,if_pos rfl,oddPartsAt,Int.cast_prod]
    let s := (grid a).erase t
    have H := normProd_cleared p hnil a t s
      (fun q hq=>(Finset.ne_of_mem_erase hq).symm) z
    calc
      _=(∏ q ∈ s, (oddWord (t-q):R))*(∏ q ∈ s,ratioFactor p a t q z)*
          oddInverse p (oddDerivative a:R) := by unfold s; ring
      _=_ := by rw [H]
  · rw [W,if_neg he,eval₂_mul,eval₂_mul,eval₂_mul,eval₂_C,eval₂_C,eval₂_X,
      reduction_rho p hnil ht,reduction_slope p hnil ht hk (Ne.symm he),factor_read p hnil ht _
      (Finset.erase_subset _ _) z,modular,if_neg he]
    let s := ((grid a).erase t).erase k
    let d := (oddWord (t-k):R)
    let inv := oddInverse p (oddDerivative a:R)
    let x := (2:R)^(a+1-padicValInt 2 (t-k))
    let M := ∏ q ∈ s,(oddWord (t-q):R)
    let L := ∏ q ∈ s,ratioFactor p a t q z
    have hd : (oddPartsAt a t:R)=d*M := by
      rw [oddPartsAt,Int.cast_prod]
      exact (Finset.mul_prod_erase _ (fun q => (oddWord (t-q):R)) (Finset.mem_erase.mpr ⟨he,hk⟩)).symm
    have hinv : d*oddInverse p d=1 :=
      inverse_int p hnil _ (oddWord_factor (sub_ne_zero.mpr (Ne.symm he))).1
    have hN := normProd_cleared p hnil a t s
      (fun q hq=>(Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hq)).symm) z
    change ((oddPartsAt a t:R)*inv)*(x*oddInverse p d)*z*L= x*z*(∏ q∈s,normFactor a t q z)*inv
    rw [hd]
    calc
      _=(d*oddInverse p d)*x*z*(M*L)*inv := by ring
      _=_ := by rw [hinv,one_mul,hN]

#print axioms inverse_unique
#print axioms reduction_rho
#print axioms reduction_slope
#print axioms cHat_read
#print axioms W_is_modular
end J6R18ChildWrite

