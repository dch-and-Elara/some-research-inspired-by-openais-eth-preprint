import P5MainIteratorTaylorUpper

/-! Matching positive upper exponent for the literal full integer-box
scan in a separately balanced layout. Exactly the printed schedule's
degree, group-size and measurement dimension budgets are fed in. -/
namespace P5MainIterator
open scoped BigOperators Classical
open Real

set_option maxHeartbeats 6100000 in
theorem taylor_list_upper_at {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (x : ℝ) (hx : 0<x) (hx1 : x≤1) :
    ((TaylorList V q).card:ℝ)*x^q ≤ exp (2*x*(Fintype.card V:ℝ)) := by
  let n := Fintype.card V
  have hf (j : ℕ) : (2:ℝ)^j*(n.choose j:ℝ) * x^j =
      (2*x)^j*(n.choose j:ℝ) := by rw [mul_pow]; ring
  rw [card_taylorList,Nat.cast_sum,Finset.sum_mul]
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  calc
    _ ≤ ∑ j∈Finset.range (min q n+1),(2:ℝ)^j*(n.choose j:ℝ)*x^j := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_of_le_one hx.le hx1 (by have := Finset.mem_range.mp hj; omega)
    _ ≤ ∑ j∈Finset.range (n+1),(2:ℝ)^j*(n.choose j:ℝ)*x^j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun _ _ _ => by positivity)
    _ = ∑ j∈Finset.range (n+1),(2*x)^j*(n.choose j:ℝ) := Finset.sum_congr rfl (fun j _ => hf j)
    _ = (2*x+1)^n := by rw [add_pow]; simp
    _ ≤ (exp (2*x))^n := pow_le_pow_left₀ (by positivity) (add_one_le_exp (2*x)) _
    _ = _ := by rw [← exp_nat_mul,mul_comm]

theorem taylor_source_exponent {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (L l C : ℝ) (hL : 0<L) (hl : 1≤l) (heq : l=log L)
    (_hC : 0≤C) (hρ : l/sqrt L≤1)
    (hq : (q:ℝ)≤C*(Fintype.card V:ℝ)*(l/sqrt L)) :
    ((TaylorList V q).card:ℝ) ≤ exp ((2+C/2)*(Fintype.card V:ℝ)*(l^2/sqrt L)) := by
  let x := l/sqrt L
  let n := Fintype.card V
  have hl' : 0<l := by linarith only [hl]
  have hx : 0<x := by dsimp [x]; positivity
  have h := taylor_list_upper_at (V:=V) q x hx hρ
  have hdiv := (le_div_iff₀ (pow_pos hx q)).mpr h
  apply hdiv.trans
  have hlogx : -log x ≤ l/2 := by
    dsimp [x]
    rw [log_div hl'.ne' (by positivity),log_sqrt hL.le,←heq]
    linarith only [log_nonneg hl]
  have hqlog : (q:ℝ)*(-log x)≤(C*(n:ℝ)*x)*(l/2) :=
    (mul_le_mul_of_nonneg_left hlogx (by positivity)).trans
      (mul_le_mul_of_nonneg_right hq (by positivity))
  have hTex : exp (2*x*(n:ℝ))/(x^q) = exp (2*x*(n:ℝ)+(q:ℝ)*(-log x)) := by
    have hPow : x^q=exp ((q:ℝ)*log x) := by rw [exp_nat_mul,exp_log hx]
    rw [hPow,←exp_sub]
    congr 1
    ring
  rw [hTex]
  apply exp_le_exp.mpr
  calc
    _ ≤ 2*x*(n:ℝ)+(C*(n:ℝ)*x)*(l/2) := add_le_add_left hqlog _
    _ ≤ _ := by
      have hsq : l≤l^2 := by simpa only [mul_one,pow_two] using mul_le_mul_of_nonneg_left hl hl'.le
      have hcmp : x≤l^2/sqrt L := div_le_div_of_nonneg_right hsq (sqrt_nonneg _)
      have hlin : 2*x*(n:ℝ)≤2*(l^2/sqrt L)*(n:ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcmp (by norm_num)) (by positivity)
      have hterm : (C*(n:ℝ)*x)*(l/2)=(C/2)*(n:ℝ)*(l^2/sqrt L) := by dsimp [x]; ring
      rw [hterm]
      linarith only [hlin]

set_option maxHeartbeats 8400000 in
theorem scheduled_full_box_upper {V : Type*} [Fintype V] [DecidableEq V]
    (q Q r b h M : ℕ) (L l Cq Cd Cm Cg : ℝ)
    (hQ : 0<Q) (hr : 0<r) (hL : 0<L) (hl : 1≤l) (heq : l=log L)
    (hρ : l/sqrt L≤1)
    (hqC : 0≤Cq) (hCd : 0≤Cd) (hCm : 0≤Cm)
    (hq : (q:ℝ)≤Cq*(Fintype.card V:ℝ)*(l/sqrt L))
    (hLbudget : L≤(Fintype.card V:ℝ)*(l^2/sqrt L))
    (hQlog : log (Q:ℝ)≤L) (hrlog : log (r:ℝ)≤L)
    (hR : (1:ℝ)/(r:ℝ)≤Cg*(l^2/sqrt L))
    (hb : (b:ℝ)≤2*(Fintype.card V:ℝ)/(r:ℝ))
    (hcoord : (r:ℝ)*(h:ℝ)≤Cd*((Fintype.card V:ℝ)/((r:ℝ)*L)))
    (hm : log (2*(M:ℝ)+1)≤Cm*L) :
    ((Q*(TaylorList V q).card*(2*M+1)^(r*h)*r*2^b:ℕ):ℝ) ≤
      exp ((4+Cq/2+(Cd*Cm+2*log 2)*Cg)*(Fintype.card V:ℝ)*(l^2/sqrt L)) := by
  let a := l^2/sqrt L
  let n := Fintype.card V
  have hrr : 0<(r:ℝ) := by exact_mod_cast hr
  have hQr : 0<(Q:ℝ) := by exact_mod_cast hQ
  have h2 : 0≤ log 2 := log_nonneg (by norm_num)
  have hα : 0≤a := by dsimp [a]; positivity
  have hT := taylor_source_exponent (V:=V) q L l Cq hL hl heq hqC hρ hq
  have hLogMnonneg : 0≤log (2*(M:ℝ)+1) := by
    apply log_nonneg
    exact_mod_cast (by omega : 1≤2*M+1)
  have hc₁ : (r:ℝ)*(h:ℝ)*log (2*(M:ℝ)+1)≤Cd*Cm*((n:ℝ)/(r:ℝ)) := by
    calc
      _ ≤ (Cd*((n:ℝ)/((r:ℝ)*L)))*(Cm*L) :=
        mul_le_mul hcoord hm hLogMnonneg (by positivity)
      _ = _ := by field_simp
  have hc₂ : (b:ℝ)*log 2≤2*log 2*((n:ℝ)/(r:ℝ)) := by
    calc
      _ ≤ (2*(n:ℝ)/(r:ℝ))*log 2 := mul_le_mul_of_nonneg_right hb h2
      _ = _ := by ring
  have hc : (r:ℝ)*(h:ℝ)*log (2*(M:ℝ)+1)+(b:ℝ)*log 2 ≤
      ((Cd*Cm+2*log 2)*Cg)*(n:ℝ)*a := by
    calc
      _ ≤ (Cd*Cm+2*log 2)*((n:ℝ)/(r:ℝ)) := by linarith only [hc₁,hc₂]
      _ = ((Cd*Cm+2*log 2)*(n:ℝ))*(1/(r:ℝ)) := by ring
      _ ≤ ((Cd*Cm+2*log 2)*(n:ℝ))*(Cg*a) :=
        mul_le_mul_of_nonneg_left hR (by positivity)
      _ = _ := by ring
  have hTcast :
      ((Q*(TaylorList V q).card*(2*M+1)^(r*h)*r*2^b:ℕ):ℝ) =
      (Q:ℝ)*((TaylorList V q).card:ℝ)*(2*(M:ℝ)+1)^(r*h)*(r:ℝ)*(2:ℝ)^b := by push_cast; rfl
  rw [hTcast]
  have hh : 0<2*(M:ℝ)+1 := by positivity
  calc
    _ ≤ (Q:ℝ)*exp ((2+Cq/2)*(n:ℝ)*a)*(2*(M:ℝ)+1)^(r*h)*(r:ℝ)*(2:ℝ)^b := by
      gcongr
    _ = exp (log (Q:ℝ)+((2+Cq/2)*(n:ℝ)*a)+
          ((r:ℝ)*(h:ℝ)*log (2*(M:ℝ)+1))+log (r:ℝ)+(b:ℝ)*log 2) := by
      repeat' rw [exp_add]
      have hz₁ : exp ((r:ℝ)*(h:ℝ)*log (2*(M:ℝ)+1)) = (2*(M:ℝ)+1)^(r*h) := by
        rw [←Nat.cast_mul,exp_nat_mul,exp_log hh]
      have hz₂ : exp ((b:ℝ)*log 2) = (2:ℝ)^b := by rw [exp_nat_mul,exp_log (by norm_num : (0:ℝ)<2)]
      rw [exp_log hQr,exp_log hrr,hz₁,hz₂]
    _ ≤ _ := by apply exp_le_exp.mpr; linarith only [hc,hQlog,hrlog,hLbudget]

#print axioms taylor_list_upper_at
#print axioms taylor_source_exponent
#print axioms scheduled_full_box_upper
end P5MainIterator
