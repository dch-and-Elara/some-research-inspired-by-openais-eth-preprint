import J1PhysicalPrinted

/-! Finite MAIN guards for the printed floor/ceiling parameters
(main TeX lines 2753–2776). No independent r>0 premise. -/

namespace J1PPrinted

def ceilSqrt (lambda : ℕ) : ℕ :=
  lambda.sqrt + if lambda.sqrt^2=lambda then 0 else 1

def mainRadius (beta lambda : ℕ) : ℕ := (beta+3)*ceilSqrt lambda

def mainScaleIndex (lambda : ℕ) : ℕ := J1PhysicalPrinted.sourceNu lambda / 2 - 1

private theorem polynomial_margin_aux (n : ℕ) :
    16384*(32+n+1)^2 ≤ (2:ℕ)^(32+n) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hx : (32+n+1+1)^2 ≤ 2*(32+n+1)^2 := by
      nlinarith [show 2≤32+n by omega]
    calc
      _ = 16384*(32+n+1+1)^2 := by ring
      _ ≤ 16384*(2*(32+n+1)^2) := Nat.mul_le_mul_left _ hx
      _ = 2*(16384*(32+n+1)^2) := by ring
      _ ≤ 2*(2:ℕ)^(32+n) := Nat.mul_le_mul_left _ ih
      _ = _ := by rw [Nat.add_succ,pow_succ,Nat.mul_comm]

private theorem polynomial_margin (n : ℕ) (hn : 32≤n) :
    16384*(n+1)^2 ≤ (2:ℕ)^n := by
  have hh := polynomial_margin_aux (n-32)
  rwa [Nat.add_sub_of_le hn] at hh

theorem sqrt_ge_dyadic_main (lambda : ℕ) (hn : 32 ≤ mainScaleIndex lambda) :
    (2:ℕ)^mainScaleIndex lambda ≤ lambda.sqrt := by
  let nu := J1PhysicalPrinted.sourceNu lambda
  let n := mainScaleIndex lambda
  have hn' : 32 ≤ n := hn
  have he : n = nu/2-1 := rfl
  have hlt : nu-1 < Nat.clog 2 lambda := by
    change nu-1 < nu
    omega
  have hlo : (2:ℕ)^(nu-1) < lambda :=
    (Nat.lt_clog_iff_pow_lt (b:=2) (by decide)).1 hlt
  apply Nat.le_sqrt'.mpr
  calc
    _ = (2:ℕ)^(2*n) := by change ((2:ℕ)^n)^2 = _; rw [← pow_mul,Nat.mul_comm]
    _ ≤ (2:ℕ)^(nu-1) := Nat.pow_le_pow_right (by decide) (by omega)
    _ ≤ _ := hlo.le

/-- Actual r,Q,R roundings are simultaneously admissible under one
explicit finite size cutoff and the fixed-constant β applicability
test. The original manuscript only asserts eventual validity. -/
theorem main_shape_guards (beta lambda : ℕ)
    (hn : 32 ≤ mainScaleIndex lambda) (hbeta : beta+3 ≤ mainScaleIndex lambda+1) :
    2 ≤ J1PhysicalPrinted.sourceR lambda ∧
      32 ≤ mainRadius beta lambda ∧
      6*mainRadius beta lambda ≤ J1PhysicalPrinted.sourceQ lambda := by
  let n := mainScaleIndex lambda
  let nu := J1PhysicalPrinted.sourceNu lambda
  let x := lambda.sqrt
  let B := beta+3
  let c := ceilSqrt lambda
  have hnu : nu≤3*(n+1) := by
    have he : n=nu/2-1 := rfl
    omega
  have hnuPos : 0<nu := by
    have he : n=nu/2-1 := rfl
    omega
  have hb : B≤n+1 := hbeta
  have hpoly := (polynomial_margin n hn).trans (sqrt_ge_dyadic_main lambda hn)
  change 16384*(n+1)^2 ≤ x at hpoly
  have hx : 32 ≤ x := by nlinarith [sq_nonneg ((n:ℤ)+1)]
  have hcLow : x ≤ c := by unfold c ceilSqrt; omega
  have hcHigh : c ≤ 2*x := by
    have hc : c ≤ x+1 := by
      dsimp only [c,ceilSqrt,x]
      split <;> omega
    omega
  have hsq : nu^2 ≤ 9*(n+1)^2 := by
    calc
      _ ≤ (3*(n+1))^2 := Nat.pow_le_pow_left hnu _
      _ = _ := by ring
  have hR : 2≤J1PhysicalPrinted.sourceR lambda := by
    change 2≤x/nu^2
    apply (Nat.le_div_iff_mul_le (pow_pos hnuPos _)).2
    have h := Nat.mul_le_mul_left 2 hsq
    nlinarith
  have hB : 1≤B := by dsimp [B]; omega
  have hRad : 32≤mainRadius beta lambda :=
    (hx.trans hcLow).trans (by
      change c≤B*c
      simpa using Nat.mul_le_mul_right c hB)
  have hxBound : 1536*B*nu≤x := by
    calc
      _ ≤ 1536*(n+1)*(3*(n+1)) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hb) hnu
      _ = 4608*(n+1)^2 := by ring
      _ ≤ 16384*(n+1)^2 := Nat.mul_le_mul_right _ (by decide)
      _ ≤ _ := hpoly
  have hQ : 6*mainRadius beta lambda ≤ J1PhysicalPrinted.sourceQ lambda := by
    change 6*(B*c)≤lambda/(128*nu)
    apply (Nat.le_div_iff_mul_le (by positivity)).2
    calc
      _ = (768*B*nu)*c := by ring
      _ ≤ (768*B*nu)*(2*x) := Nat.mul_le_mul_left _ hcHigh
      _ = (1536*B*nu)*x := by ring
      _ ≤ x*x := Nat.mul_le_mul_right _ hxBound
      _ ≤ _ := by rw [← pow_two]; exact Nat.sqrt_le' lambda
  exact ⟨hR,hRad,hQ⟩

/-- The actual J1 family uses n=4N; r positivity and Q/R shape now
come from the printed definitions rather than separate hypotheses. -/
theorem actual_j1_guards (N beta : ℕ) (hN : 0<N)
    (hn : 32 ≤ mainScaleIndex (Nat.clog 2 (4*N)))
    (hbeta : beta+3 ≤ mainScaleIndex (Nat.clog 2 (4*N))+1) :
    let lambda := Nat.clog 2 (4*N)
    let r := J1PhysicalPrinted.sourceR lambda
    let Q := J1PhysicalPrinted.sourceQ lambda
    2 ≤ r ∧ 32 ≤ mainRadius beta lambda ∧ 6*mainRadius beta lambda ≤ Q ∧
      192*Q*r^2*r^Q+6 < N ∧
      10*(r^(2*Q))^2 ≤ 12*N ∧ 2*Q*r^2 ≤ 4*N := by
  let lambda := Nat.clog 2 (4*N)
  have hs := main_shape_guards beta lambda hn hbeta
  have hx := sqrt_ge_dyadic_main lambda hn
  have hn' : 32 ≤ mainScaleIndex lambda := hn
  have h128 : 16 ≤ lambda.sqrt := by
    change (2:ℕ)^4 ≤ lambda.sqrt
    exact (Nat.pow_le_pow_right (by decide) (show 4≤mainScaleIndex lambda by omega)).trans hx
  have hL : 256≤lambda := by
    have h := (Nat.pow_le_pow_left h128 2).trans (Nat.sqrt_le' lambda)
    norm_num at h
    exact h
  have hr : 0 < J1PhysicalPrinted.sourceR lambda := (by decide : 0 < (2:ℕ)).trans_le hs.1
  have h := J1PhysicalPrinted.source_guards N hN hL hr
  exact ⟨hs.1,hs.2.1,hs.2.2,h⟩

#print axioms sqrt_ge_dyadic_main
#print axioms main_shape_guards
#print axioms actual_j1_guards

end J1PPrinted

