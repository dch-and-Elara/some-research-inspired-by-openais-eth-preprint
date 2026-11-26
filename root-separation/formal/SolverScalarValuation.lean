import S11NativeKernel
import Mathlib.Data.Rat.Lemmas

noncomputable section
namespace RootSeparation.Solver

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Unlike padicValRat, the source valuation assigns infinity to zero. -/
def scalarOrder (q : ℚ) : WithTop ℤ :=
  if q = 0 then ⊤ else (↑(padicValRat 2 q) : WithTop ℤ)

theorem scalarOrder_add (x y : ℚ) :
    min (scalarOrder x) (scalarOrder y) ≤ scalarOrder (x+y) := by
  by_cases hx : x = 0
  · simp [hx,scalarOrder]
  by_cases hy : y = 0
  · simp [hy,scalarOrder]
  by_cases hxy : x+y = 0
  · simp [scalarOrder,hxy]
  rw [scalarOrder,if_neg hx,scalarOrder,if_neg hy,scalarOrder,if_neg hxy, ← WithTop.coe_min,
    WithTop.coe_le_coe]
  exact padicValRat.min_le_padicValRat_add hxy

theorem scalarOrder_mul (x y : ℚ) :
    scalarOrder (x*y) = scalarOrder x + scalarOrder y := by
  by_cases hx : x = 0
  · simp [hx,scalarOrder]
  by_cases hy : y = 0
  · simp [hy,scalarOrder]
  simp [scalarOrder,hx,hy,padicValRat.mul hx hy,WithTop.coe_add]

def scalarValuation : AddValuation ℚ (WithTop ℤ) :=
  AddValuation.of scalarOrder (by simp [scalarOrder]) (by simp [scalarOrder])
    scalarOrder_add scalarOrder_mul

theorem scalarOrder_two : scalarOrder 2 = 1 := by
  change (if (2:ℚ) = 0 then ⊤ else ↑(padicValRat 2 (2:ℚ))) = (1 : WithTop ℤ)
  rw [if_neg (by norm_num), show padicValRat 2 (2:ℚ) = 1 from padicValRat.self (by decide)]
  rfl

theorem scalarOrder_nonnegative_iff (q : ℚ) : 0 ≤ scalarOrder q ↔ Odd q.den := by
  by_cases hq : q = 0
  · simp [hq,scalarOrder]
  rw [scalarOrder,if_neg hq, ← WithTop.coe_zero, WithTop.coe_le_coe]
  by_cases hd : 2 ∣ q.den
  · have hval := one_le_padicValNat_of_dvd q.den_ne_zero hd
    have hn : ¬ (2 : ℤ) ∣ q.num := by
      intro hh
      have hh' : 2 ∣ q.num.natAbs := by exact Int.ofNat_dvd_left.1 hh
      have h := Nat.dvd_gcd hh' hd
      rw [q.reduced.gcd_eq_one] at h
      omega
    rw [padicValRat_def, padicValInt.eq_zero_of_not_dvd hn]
    have hnot : ¬Odd q.den := by rwa [Nat.not_odd_iff_even, even_iff_two_dvd]
    simp only [hnot,iff_false]
    omega
  · have hdd := padicValNat.eq_zero_of_not_dvd hd
    simp only [padicValRat_def,hdd,Nat.cast_zero,sub_zero,Int.natCast_nonneg,true_iff]
    rwa [← Nat.not_even_iff_odd,even_iff_two_dvd]

#print axioms scalarValuation
#print axioms scalarOrder_two
#print axioms scalarOrder_nonnegative_iff

end RootSeparation.Solver
