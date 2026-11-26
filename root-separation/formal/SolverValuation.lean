import SolverCoefficientOrder

noncomputable section
namespace RootSeparation.Solver
open Polynomial

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem scalarOrder_zpow_two (n : ℤ) : scalarOrder ((2 : ℚ)^n) = ↑n := by
  cases n with
  | ofNat n =>
    change scalarOrder ((2:ℚ)^(n:ℤ)) = ↑(n:ℤ)
    rw [zpow_natCast]
    have h := scalarValuation.map_pow (2:ℚ) n
    change scalarOrder ((2:ℚ)^n) = n • scalarOrder (2:ℚ) at h
    rw [h,scalarOrder_two]
    norm_cast
    simp
  | negSucc n =>
    rw [zpow_negSucc, scalarOrder,if_neg (inv_ne_zero (pow_ne_zero _ (by norm_num))),
      padicValRat.inv,padicValRat.pow (by norm_num)]
    have h : padicValRat 2 (2:ℚ) = 1 := padicValRat.self (by decide)
    rw [h]
    norm_cast
    omega

section Extension
variable {e : ℕ} (F : SourcePolynomial e)

abbrev orderInBasis := coordinateOrder F.monic F.degree

theorem orderInBasis_add (x y : RationalRing F.f) :
    min (orderInBasis F x) (orderInBasis F y) ≤ orderInBasis F (x+y) := by
  apply (le_coordinateOrder _ _ _ _).2
  intro i
  rw [map_add, Pi.add_apply]
  apply le_trans _ (scalarOrder_add _ _)
  exact min_le_min ((le_coordinateOrder _ _ _ _).1 le_rfl i)
    ((le_coordinateOrder _ _ _ _).1 le_rfl i)

theorem orderInBasis_top (x : RationalRing F.f) : orderInBasis F x = ⊤ ↔ x = 0 := by
  constructor
  · intro h
    apply (rationalCoords F.monic F.degree).injective
    rw [map_zero]
    funext i
    have hi := (le_coordinateOrder F.monic F.degree x ⊤).1 (ge_of_eq h) i
    change rationalCoords F.monic F.degree x i = 0
    by_contra hn
    simp [scalarOrder, hn] at hi
  · intro hx
    subst x
    apply top_le_iff.1
    apply (le_coordinateOrder _ _ _ _).2
    intro i
    simp [scalarOrder]

theorem orderInBasis_scale (q : ℚ) (hq : q ≠ 0) (x : RationalRing F.f) :
    orderInBasis F (AdjoinRoot.of _ q * x) = scalarOrder q + orderInBasis F x := by
  have hcoord (i : Fin e) : rationalCoords F.monic F.degree (AdjoinRoot.of _ q * x) i =
      q * rationalCoords F.monic F.degree x i := by
    let g := F.f.map (Int.castRingHom ℚ)
    let hg : g.Monic := F.monic.map _
    let hd : g.natDegree = e := (F.monic.natDegree_map _).trans F.degree
    change (AdjoinRoot.powerBasisAux' hg).equivFun (AdjoinRoot.of g q * x) (Fin.cast hd.symm i) =
      q * (AdjoinRoot.powerBasisAux' hg).equivFun x (Fin.cast hd.symm i)
    change (AdjoinRoot.powerBasisAux' hg).equivFun ((algebraMap ℚ (AdjoinRoot g)) q * x)
      (Fin.cast hd.symm i) = _
    rw [← Algebra.smul_def]
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
  unfold orderInBasis coordinateOrder
  simp_rw [hcoord,scalarOrder_mul]
  generalize (Finset.univ : Finset (Fin e)) = s
  induction s using Finset.induction_on with
  | empty =>
    simp [scalarOrder,hq]
  | insert i s hi ih =>
    rw [Finset.inf_insert, Finset.inf_insert,ih]
    change min _ _ = _ + min _ _
    by_cases h : scalarOrder (rationalCoords F.monic F.degree x i) ≤
        s.inf (fun j => scalarOrder (rationalCoords F.monic F.degree x j))
    · rw [min_eq_left h,min_eq_left (add_le_add_left h _)]
    · have hl := le_of_not_ge h
      rw [min_eq_right hl,min_eq_right (add_le_add_left hl _)]

private theorem wordOne_mul_ne_zero {x y : WordRing F.f 1} (hx : x ≠ 0) (hy : y ≠ 0) :
    x*y ≠ 0 := by
  let g := F.f.map (Int.castRingHom (ZMod 2))
  letI : Fact (Irreducible g) := ⟨F.irreducibleTwo⟩
  letI : Field (AdjoinRoot g) := AdjoinRoot.instField (f := g)
  have hx' : (x : AdjoinRoot g) ≠ 0 := hx
  have hy' : (y : AdjoinRoot g) ≠ 0 := hy
  have hxy : (x : AdjoinRoot g) * (y : AdjoinRoot g) ≠ 0 := mul_ne_zero (M₀ := AdjoinRoot g) hx' hy'
  exact hxy

private theorem wordOne_one_ne_zero : (1 : WordRing F.f 1) ≠ 0 := by
  let g := F.f.map (Int.castRingHom (ZMod 2))
  letI : Fact (Irreducible g) := ⟨F.irreducibleTwo⟩
  letI : Field (AdjoinRoot g) := AdjoinRoot.instField (f := g)
  exact (one_ne_zero : (1 : AdjoinRoot g) ≠ 0)

theorem orderInBasis_primitive (x : RationalRing F.f) :
    orderInBasis F x = 0 ↔
      ∃ y : IntegralRing F.f, integralRational F.f y = x ∧ integralWord F.f 1 y ≠ 0 := by
  constructor
  · intro h
    obtain ⟨y,hy⟩ := (coordinateOrder_nonnegative F.monic F.degree x).1 (le_of_eq h.symm)
    refine ⟨y,hy,?_⟩
    intro hz
    have h1 := (coordinateOrder_zero_iff F.monic F.degree 1 (by decide) y).1 hz
    change (1:WithTop ℤ) ≤ orderInBasis F (integralRational F.f y) at h1
    rw [hy, h] at h1
    exact (by decide : ¬ (1:WithTop ℤ) ≤ 0) h1
  · rintro ⟨y,rfl,hy⟩
    have h0 : 0 ≤ orderInBasis F (integralRational F.f y) :=
      (coordinateOrder_nonnegative F.monic F.degree (integralRational F.f y)).2 ⟨y,rfl⟩
    have h1 : ¬ (1:WithTop ℤ) ≤ orderInBasis F (integralRational F.f y) :=
      fun h => hy ((coordinateOrder_zero_iff F.monic F.degree 1 (by decide) y).2 h)
    generalize h : orderInBasis F (integralRational F.f y) = z at h0 h1 ⊢
    cases z with
    | top => exact (h1 le_top).elim
    | coe n =>
      change (0 : WithTop ℤ) ≤ ↑n at h0
      change ¬ (1 : WithTop ℤ) ≤ ↑n at h1
      norm_cast at h0 h1 ⊢
      omega

theorem orderInBasis_one : orderInBasis F 1 = 0 :=
  (orderInBasis_primitive F 1).2 ⟨1,map_one _, by
    rw [map_one]
    exact wordOne_one_ne_zero F⟩

theorem orderInBasis_two : orderInBasis F 2 = 1 := by
  have h := orderInBasis_scale F 2 (by norm_num) 1
  rw [map_ofNat,mul_one,orderInBasis_one,scalarOrder_two,add_zero] at h
  exact h

private theorem orderInBasis_prim_mul {x y : RationalRing F.f}
    (hx : orderInBasis F x = 0) (hy : orderInBasis F y = 0) :
    orderInBasis F (x*y) = 0 := by
  obtain ⟨a,ha,hra⟩ := (orderInBasis_primitive F x).1 hx
  obtain ⟨b,hb,hrb⟩ := (orderInBasis_primitive F y).1 hy
  refine (orderInBasis_primitive F _).2 ⟨a*b,by rw [map_mul,ha,hb],?_⟩
  rw [map_mul]
  exact wordOne_mul_ne_zero F hra hrb

theorem orderInBasis_mul (x y : RationalRing F.f) :
    orderInBasis F (x*y) = orderInBasis F x + orderInBasis F y := by
  by_cases hx : x = 0
  · simp [hx,(orderInBasis_top F 0).2 rfl]
  by_cases hy : y = 0
  · simp [hy,(orderInBasis_top F 0).2 rfl]
  have finite (z : RationalRing F.f) (hz : z ≠ 0) : ∃ n : ℤ, orderInBasis F z = ↑n := by
    cases h : orderInBasis F z with
    | top => exact (hz ((orderInBasis_top F z).1 h)).elim
    | coe n => exact ⟨n,rfl⟩
  obtain ⟨m,hm⟩ := finite x hx
  obtain ⟨n,hn⟩ := finite y hy
  let φ := AdjoinRoot.of (F.f.map (Int.castRingHom ℚ))
  have hscale (z : RationalRing F.f) (k : ℤ) :
      orderInBasis F (φ ((2:ℚ)^k) * z) = (↑k:WithTop ℤ) + orderInBasis F z := by
    rw [orderInBasis_scale F _ (zpow_ne_zero _ (by norm_num)) z,scalarOrder_zpow_two]
  have hX : orderInBasis F (φ ((2:ℚ)^(-m)) * x) = 0 := by
    rw [hscale,hm,← WithTop.coe_add,neg_add_cancel,WithTop.coe_zero]
  have hY : orderInBasis F (φ ((2:ℚ)^(-n)) * y) = 0 := by
    rw [hscale,hn,← WithTop.coe_add,neg_add_cancel,WithTop.coe_zero]
  have hP := orderInBasis_prim_mul F hX hY
  rw [mul_mul_mul_comm, ← map_mul, ← zpow_add₀ (show (2:ℚ) ≠ 0 by norm_num), hscale] at hP
  rw [hm,hn,← WithTop.coe_add]
  generalize h : orderInBasis F (x*y) = z at hP ⊢
  cases z with
  | top => simp at hP
  | coe k =>
    rw [← WithTop.coe_add,← WithTop.coe_zero,WithTop.coe_inj] at hP
    exact congrArg (fun a : ℤ => (↑a : WithTop ℤ)) (by omega : k = m+n)

def rationalValuation : AddValuation (RationalRing F.f) (WithTop ℤ) :=
  AddValuation.of (orderInBasis F) ((orderInBasis_top F 0).2 rfl)
    (orderInBasis_one F) (orderInBasis_add F) (orderInBasis_mul F)

theorem rationalValuation_two : rationalValuation F 2 = 1 := orderInBasis_two F

theorem rationalValuation_integer (x : IntegerRing F.f) :
    0 ≤ rationalValuation F (integerRational F.f x) := by
  change 0 ≤ orderInBasis F (integerRational F.f x)
  rw [coordinateOrder_nonnegative F.monic F.degree]
  exact ⟨integerIntegral F.f x, integralRational_integerIntegral _ _⟩

theorem binaryPoint_valuation_unit (a b : BitVec e) (h : a ≠ b) :
    rationalValuation F (integerRational F.f (binaryPoint F a) -
      integerRational F.f (binaryPoint F b)) = 0 := by
  change orderInBasis F _ = 0
  rw [orderInBasis_primitive]
  refine ⟨integerIntegral F.f (binaryPoint F a - binaryPoint F b), ?_, ?_⟩
  · rw [integralRational_integerIntegral, map_sub]
  · rw [integralWord_integerIntegral, map_sub, sub_ne_zero]
    exact fun he => h (binaryPoint_residue_injective F he)

theorem tryWord_congr (p : ℕ) (hp : 0 < p) (x y : RationalRing F.f)
    (hy : 0 ≤ rationalValuation F y)
    (hxy : (↑(p:ℤ) : WithTop ℤ) ≤ rationalValuation F (x-y)) :
    tryWord F.monic p x = tryWord F.monic p y := by
  have hp₀ : (0:WithTop ℤ) ≤ (↑(p:ℤ):WithTop ℤ) := by exact_mod_cast (Nat.zero_le p)
  have h0 : 0 ≤ rationalValuation F (x-y) := hp₀.trans hxy
  obtain ⟨y₀,hy₀⟩ := (coordinateOrder_nonnegative F.monic F.degree y).1 hy
  obtain ⟨z,hz⟩ := (coordinateOrder_nonnegative F.monic F.degree (x-y)).1 h0
  have ht : integralWord F.f p z = 0 := (coordinateOrder_zero_iff F.monic F.degree p hp z).2
    (by rw [hz]; exact hxy)
  have hsum : integralRational F.f (z+y₀) = x := by
    rw [map_add,hz,hy₀,sub_add_cancel]
  rw [← hsum,← hy₀,tryWord_integral,tryWord_integral,map_add,ht,zero_add]

end Extension

#print axioms orderInBasis_scale
#print axioms orderInBasis_primitive
#print axioms rationalValuation
#print axioms rationalValuation_two
#print axioms rationalValuation_integer
#print axioms binaryPoint_valuation_unit
#print axioms tryWord_congr

end RootSeparation.Solver
