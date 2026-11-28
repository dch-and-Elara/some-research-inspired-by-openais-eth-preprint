import V8NativeMessageN7LiteralSupportSigned
import J6NativeHeightDerivative

/-! At any real signed centre, the reduced denominator and numerator
come from the same finite grid derivative, including the negative side.
There is no arbitrary rational coefficient table. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped BigOperators Polynomial
open Polynomial P1DyadicGrid P1DyadicGridBridge J6R9PacketCoeff DenominatorBudget
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4500000

def plusProducts (L k : ℕ) : ℕ := ∏ j∈Finset.range k,(L+(j+1))
def minusProducts (L k : ℕ) : ℕ := ∏ j∈Finset.range k,(L-(j+1))

theorem difference_products_finite_bound {L k : ℕ} (hk : k<L) :
    0<plusProducts L k ∧ 0<minusProducts L k ∧
      plusProducts L k≤(2*L)^k ∧ minusProducts L k≤(2*L)^k := by
  unfold plusProducts minusProducts
  have aux := fun j (hj : j∈Finset.range k)=> Finset.mem_range.mp hj
  refine ⟨Finset.prod_pos (fun j hj=>by have := aux j hj; omega),
    Finset.prod_pos (fun j hj=>by have := aux j hj; omega),?_,?_⟩
  · calc
      _ ≤ ∏ _j∈Finset.range k,(2*L) := Finset.prod_le_prod' (fun j hj=>by have := aux j hj; omega)
      _ = _ := by simp
  · calc
      _ ≤ ∏ _j∈Finset.range k,(2*L) := Finset.prod_le_prod' (fun j hj=>by have := aux j hj; omega)
      _ = _ := by simp

theorem grid_ratio_is_real_products {L k : ℕ} (hk : k<L) :
    LayerRecovery.gridRatio L k=((plusProducts L k:ℚ)/(minusProducts L k:ℚ)) := by
  unfold LayerRecovery.gridRatio plusProducts minusProducts
  rw [Finset.prod_div_distrib,Nat.cast_prod,Nat.cast_prod]
  apply congrArg₂ (·/·)
  · refine Finset.prod_congr rfl fun j _=>?_
    push_cast
    rfl
  · refine Finset.prod_congr rfl fun j hj=>?_
    have t : j+1≤L := by have := Finset.mem_range.mp hj; omega
    rw [Nat.cast_sub t]
    push_cast
    rfl

private theorem native_nonnegative_ratio_fraction {a k : ℕ} (h : k<2^a) :
    (derivRatio a (k:ℤ):ℚ) =
      Rat.divInt ((-1:ℤ)^k * (plusProducts (2^a) k:ℤ)) (minusProducts (2^a) k:ℤ) := by
  rw [J6NativeHeightDerivative.ratio_eq_grid a k h,grid_ratio_is_real_products h,
    ←Rat.intCast_div_eq_divInt]
  push_cast
  ring

theorem signed_ratio_has_bounded_fraction {a : ℕ} {t : ℤ} (h : t∈grid a) :
    ∃ (n : ℤ) (d : ℕ),0<n.natAbs ∧ 0<d ∧ (derivRatio a t:ℚ)=Rat.divInt n (d:ℤ) ∧
      n.natAbs≤(2*2^a)^(t.natAbs+1) ∧ d≤(2*2^a)^(t.natAbs+1) := by
  have Lpos : 0<(2:ℕ)^a := pow_pos (by decide) _
  have Bpos : 0<2*(2:ℕ)^a := by omega
  have general (k : ℕ) (hk : k<2^a) (size : k≤t.natAbs+1)
      (posneg : (derivRatio a t:ℚ)=(derivRatio a (k:ℤ):ℚ) ∨
        (derivRatio a t:ℚ)=-(derivRatio a (k:ℤ):ℚ)) :
      ∃ (n : ℤ) (d : ℕ),0<n.natAbs ∧ 0<d ∧ (derivRatio a t:ℚ)=Rat.divInt n (d:ℤ) ∧
        n.natAbs≤(2*2^a)^(t.natAbs+1) ∧ d≤(2*2^a)^(t.natAbs+1) := by
    obtain ⟨pA,pD,hA,hD⟩ := difference_products_finite_bound hk
    let n : ℤ := (-1)^k * (plusProducts (2^a) k:ℤ)
    let d := minusProducts (2^a) k
    have hn : n.natAbs=plusProducts (2^a) k := by simp [n,Int.natAbs_mul,Int.natAbs_pow]
    have q : (derivRatio a (k:ℤ):ℚ)=Rat.divInt n (d:ℤ) :=
      native_nonnegative_ratio_fraction hk
    have b : (2*2^a)^k≤(2*2^a)^(t.natAbs+1) := Nat.pow_le_pow_right Bpos size
    rcases posneg with hEq | hEq
    · exact ⟨n,d,by rw [hn]; exact pA,pD,hEq.trans q,by rw [hn]; exact hA.trans b,hD.trans b⟩
    · refine ⟨-n,d,by simpa [hn] using pA,pD,?_,by simpa [hn] using hA.trans b,hD.trans b⟩
      simp only [hEq,q,←Rat.intCast_div_eq_divInt,Int.cast_neg,neg_div]
  by_cases s : 0≤t
  · let k := t.toNat
    have eq : (k:ℤ)=t := Int.toNat_of_nonneg s
    have lt : t<(2:ℤ)^a := (mem_grid.mp h).2
    have hk : k<2^a := by
      have q : (k:ℤ)<(2:ℤ)^a := by rw [eq]; exact lt
      exact_mod_cast q
    have size : k≤t.natAbs+1 := by dsimp [k]; omega
    exact general k hk size (Or.inl (congrArg (derivRatio a : ℤ→ℚ) eq.symm))
  · let k := (-1-t).toNat
    have eq : (k:ℤ)=-1-t := Int.toNat_of_nonneg (by omega)
    have lt : -1-t<(2:ℤ)^a := (mem_grid.mp (reflected_grid h)).2
    have hk : k<2^a := by
      have q : (k:ℤ)<(2:ℤ)^a := by rw [eq]; exact lt
      exact_mod_cast q
    have size : k≤t.natAbs+1 := by dsimp [k]; omega
    have sign := derivative_ratio_reflected h
    rw [←eq] at sign
    exact general k hk size (Or.inr (by linarith))

private theorem int_abs_dvd_of_dvd {x y : ℤ} (h : x∣y) : x.natAbs∣y.natAbs := by
  obtain ⟨k,res⟩ := h
  exact ⟨k.natAbs,by simpa only [Int.natAbs_mul] using congrArg Int.natAbs res⟩

theorem real_grid_reduced_height {a : ℕ} {t : ℤ} (h : t∈grid a) :
    let real := (derivRatio a t:ℚ)
    Odd (real.den:ℤ) ∧
      max real.num.natAbs real.den≤(2*2^a)^(t.natAbs+1) := by
  let real := (derivRatio a t:ℚ)
  have inRing : real∈twoLocalSubalgebra := by
    change (derivRatio a t:ℚ)∈twoLocalSubalgebra
    rw [←rho_rat h]
    exact (rho a t).property
  obtain ⟨r,s,odd,repr⟩ := (mem_twoLocal_iff _).mp inRing
  have dd : (real.den:ℤ)∣s := by
    rw [repr,Rat.intCast_div_eq_divInt]
    exact Rat.den_dvd r s
  have oddD : Odd (real.den:ℤ) := by
    by_contra bad
    have even := Int.not_odd_iff_even.mp bad
    have div : (2:ℤ)∣s := (even_iff_two_dvd.mp even).trans dd
    exact odd div
  obtain ⟨n,d,hn,hd,eq,hnb,hdb⟩ := signed_ratio_has_bounded_fraction h
  have er : real=Rat.divInt n (d:ℤ) := eq
  have dn : (real.den:ℤ)∣(d:ℤ) := by
    rw [er]
    exact Rat.den_dvd n d
  have nn : real.num∣n := by
    rw [er]
    exact Rat.num_dvd n (by exact_mod_cast hd.ne')
  have dlen : real.den≤d := by
    have bound := int_abs_dvd_of_dvd dn
    simp only [Int.natAbs_natCast] at bound
    exact Nat.le_of_dvd hd bound
  exact ⟨oddD,max_le (Nat.le_of_dvd hn (int_abs_dvd_of_dvd nn)|>.trans hnb)
    (dlen.trans hdb)⟩

end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.difference_products_finite_bound
#print axioms V8NativeMessage.N7LiteralSupport.grid_ratio_is_real_products
#print axioms V8NativeMessage.N7LiteralSupport.signed_ratio_has_bounded_fraction
#print axioms V8NativeMessage.N7LiteralSupport.real_grid_reduced_height
