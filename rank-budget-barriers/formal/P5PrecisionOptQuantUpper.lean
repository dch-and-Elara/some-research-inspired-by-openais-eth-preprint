import P5PrecisionOptFiniteUpper
import P5PrecisionOptQuantLower

/-! Explicit two-sided finite scale for the unrestricted retained-order
optimum of this fixed decoder. Fields/local coefficient rings are the
same as in the proved fixed criterion. The rounded exponent
2*u-floor(u/4) differs from 7*u/4 by less than one. -/
namespace Paper5.PrecisionOpt
open P1DyadicGrid HermiteLoss
open scoped BigOperators

theorem square_le_dyadic (u : ℕ) (hu : 4≤u) : u*u≤2^u := by
  induction u,hu using Nat.le_induction with
  | base => decide
  | succ u hu h =>
    have h' : (u+1)*(u+1)≤2*(u*u) := by
      have hh := Nat.mul_le_mul_right u hu
      nlinarith
    exact h'.trans ((Nat.mul_le_mul_left 2 h).trans_eq (by rw [pow_succ]; ring))

theorem polynomial_tail_le_dyadic (u : ℕ) (hu : 16≤u) :
    u*u*(24*u+16)≤2^(u+2) := by
  induction u,hu using Nat.le_induction with
  | base => decide
  | succ u hu h =>
    have hu2 := Nat.mul_le_mul_right u hu
    have hu3 := Nat.mul_le_mul_right (u*u) hu
    have h' : (u+1)*(u+1)*(24*(u+1)+16)≤2*(u*u*(24*u+16)) := by nlinarith
    calc
      _ ≤ 2*(u*u*(24*u+16)) := h'
      _ ≤ 2*2^(u+2) := Nat.mul_le_mul_left _ h
      _ = _ := by rw [show u+1+2=(u+2)+1 by omega,pow_succ]; ring

theorem allowance_quantitative {M u : ℕ} (hu : 16≤u) (hM : u*u≤M) :
    meanAllowance M u ≤ 12*(M:ℚ)/(u:ℚ)+5*(M:ℚ)/((u:ℚ)*(u:ℚ)) := by
  let x : ℚ := u
  let m : ℚ := M
  have hpos : 0<x := by dsimp [x]; exact_mod_cast (show 0<u by omega)
  have hx : 0<x*x := mul_pos hpos hpos
  have hm : 0≤m := by dsimp [m]; positivity
  have hM' : x*x≤m := by dsimp [x,m]; exact_mod_cast hM
  have hHnat : sourceH M u*u≤3*M+u := by
    unfold sourceH
    exact (Nat.div_mul_le_self _ _).trans (Nat.sub_le ..)
  have hHrat : (sourceH M u:ℚ)*x≤3*m+x := by dsimp [x,m]; exact_mod_cast hHnat
  have hH : 4*(sourceH M u:ℚ)≤12*m/x+4 := by
    apply (mul_le_mul_iff_left₀ hpos).mp
    have he : (12*m/x+4)*x=12*m+4*x := by field_simp
    rw [he]
    linarith
  have hp0 := polynomial_tail_le_dyadic u hu
  have hp1 : x*x*(24*x+16)≤(2:ℚ)^(u+2) := by dsimp [x]; exact_mod_cast hp0
  have htail : m*(24*x+16)/(2:ℚ)^(u+2)≤m/(x*x) := by
    apply (div_le_div_iff₀ (by positivity : 0<(2:ℚ)^(u+2)) hx).mpr
    have hi' := mul_le_mul_of_nonneg_right hp1 hm
    nlinarith
  have hM1 : 1≤m/(x*x) := (le_div_iff₀ hx).mpr (by linarith)
  have he : meanAllowance M u =
      4*(sourceH M u:ℚ)+m*(24*x+16)/(2:ℚ)^(u+2) := by
    unfold meanAllowance
    dsimp [x,m]
    push_cast
    ring
  change meanAllowance M u≤12*m/x+5*m/(x*x)
  have ht : (4:ℚ)≤4*(m/(x*x)) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hM1 (by norm_num : 0≤(4:ℚ))
  calc
    meanAllowance M u = 4*(sourceH M u:ℚ)+m*(24*x+16)/(2:ℚ)^(u+2) := he
    _ ≤ (12*m/x+4)+m/(x*x) := add_le_add hH htail
    _ = (12*m/x+m/(x*x))+4 := by ring
    _ ≤ (12*m/x+m/(x*x))+4*(m/(x*x)) := add_le_add_left ht _
    _ = _ := by ring

theorem actual_depth_lower {M u v : ℕ} (hu : 16≤u) (hM : u*u≤M)
    (h : (Paper5.P3.printedDegree u M:ℚ)/(2:ℚ)^(2*u) <
      meanAllowance M u/3*(2*(v:ℚ)+2)) :
    u≤4*(v+2) := by
  let x : ℚ := u
  let m : ℚ := M
  let L : ℚ := (2:ℚ)^(2*u)
  have hpos : 0<x := by dsimp [x]; exact_mod_cast (show 0<u by omega)
  have hx : 0<x*x := mul_pos hpos hpos
  have hm : 0≤m := by dsimp [m]; positivity
  have hL : 0<L := by dsimp [L]; positivity
  have hxu : x≤L := by
    have hh : u≤(2:ℕ)^(2*u) := by
      calc
        u ≤ u*u := by nlinarith
        _ ≤ 2^u := square_le_dyadic u (by omega)
        _ ≤ _ := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by omega)
    dsimp [x,L]
    exact_mod_cast hh
  have hl : m/L≤m/x := div_le_div_of_nonneg_left hm hpos hxu
  have he : (Paper5.P3.printedDegree u M:ℚ)/L=2*m-m/L := by
    unfold Paper5.P3.printedDegree
    have hwp : 1≤2*(2:ℕ)^(2*u) := Nat.succ_le_of_lt (by positivity)
    rw [Nat.cast_mul,Nat.cast_sub hwp]
    push_cast
    change m*(2*L-1)/L=_
    field_simp
  by_contra hn
  have hj0 : 4*(v+2) < u := Nat.lt_of_not_ge hn
  have hj : 2*(v:ℚ)+2≤x/2-2 := by
    have H : (4*(v+2:ℕ):ℚ)<x := by dsimp [x]; exact_mod_cast hj0
    push_cast at H
    linarith
  let B := 12*m/x+5*m/(x*x)
  have hB : 0≤B := by dsimp [B]; positivity
  have h0 : meanAllowance M u ≤ B := allowance_quantitative hu hM
  have hv : 0≤2*(v:ℚ)+2 := by positivity
  have H : meanAllowance M u / 3 * (2*(v:ℚ)+2) ≤ B/3*(x/2-2) :=
    (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right h0 (by norm_num)) hv).trans
      (mul_le_mul_of_nonneg_left hj (by positivity))
  have hAlg : B/3*(x/2-2) = 2*m - (43/6:ℚ)*(m/x) - (10/3:ℚ)*(m/(x*x)) := by
    unfold B
    field_simp
    ring
  have hA : 0≤m/x := div_nonneg hm hpos.le
  have hZ : 0≤m/(x*x) := div_nonneg hm hx.le
  rw [hAlg] at H
  change (Paper5.P3.printedDegree u M:ℚ)/L < _ at h
  rw [he] at h
  linarith

theorem scaled_deepest_upper {M u i b : ℕ} (hu : 16≤u) (hM : u*u≤M)
    (hi : i<u) (hdepth : u≤4*(i+3))
    (hb : b≤1+rootSlack M u i/(2*u+1-i)) :
    (u*u)*b ≤ 300*M*2^(2*u-u/4) := by
  let T := (2:ℕ)^(2*u-u/4)
  let h := sourceH M u
  let ell := 2*u+1-i
  let D := 2*u+1
  have hu0 : 0<u := by omega
  have hM0 : u≤M := (show u≤u*u by nlinarith).trans hM
  have hMpos : 1≤M := by omega
  have hhu : h*u≤4*M := h_upper M u hM0
  have hEll : u≤ell := by dsimp [ell]; omega
  have hD : D≤3*u := by dsimp [D]; omega
  have hT : u*u≤T := (square_le_dyadic u (by omega)).trans
    (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by omega))
  have hpow : (2:ℕ)^(2*u-i)≤8*T := by
    have hz : u/4 ≤ i+3 := by
      apply Nat.le_of_lt_succ
      apply (Nat.div_lt_iff_lt_mul (by decide : 0<4)).mpr
      omega
    have H := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (show 2*u-i≤2*u-u/4+3 by omega)
    rw [pow_add,show (2:ℕ)^3=8 by decide,mul_comm (2^(2*u-u/4)) 8] at H
    exact H
  by_cases hzero : b=0
  · simp [hzero]
  have hB : (b-1)*ell≤rootSlack M u i := by
    apply (Nat.le_div_iff_mul_le (hu0.trans_le hEll)).mp
    change b≤1+rootSlack M u i/ell at hb
    omega
  have hU : ((b-1)*u)*u≤rootSlack M u i*u :=
    Nat.mul_le_mul_right _ ((Nat.mul_le_mul_left _ hEll).trans hB)
  have hC : (u*u)*(b-1) ≤ 256*(M*T)+24*(M*(u*u)) := by
    calc
      _ = ((b-1)*u)*u := by ring
      _ ≤ rootSlack M u i*u := hU
      _ = 8*(h*u)*2^(2*u-i)+8*M*(D*u) := by dsimp [rootSlack,h,D]; ring
      _ ≤ 8*(4*M)*(8*T)+8*M*((3*u)*u) :=
        Nat.add_le_add
          (Nat.mul_le_mul (Nat.mul_le_mul_left 8 hhu) hpow)
          (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hD))
      _ = _ := by ring
  have h1 : 24*(M*(u*u))≤24*(M*T) :=
    Nat.mul_le_mul_left 24 (Nat.mul_le_mul_left M hT)
  have h2 : u*u≤M*T := hT.trans (by simpa using Nat.mul_le_mul_right T hMpos)
  have hde : (u*u)*b=(u*u)*(b-1)+(u*u) := by
    calc
      (u*u)*b = (u*u)*((b-1)+1) :=
        congrArg ((u*u)*·) (Nat.sub_add_cancel (show 1≤b by omega)).symm
      _ = _ := by rw [Nat.mul_add,Nat.mul_one]
  change (u*u)*b≤300*M*T
  rw [hde,show 300*M*T=300*(M*T) by ring]
  omega

theorem scaled_exact_optimum_upper {K : Type*} [Field K] [CharZero K] (O : Subring K)
    [IsLocalRing O] (hn2 : ¬IsUnit (2:O)) {M u : ℕ} (hu : 16≤u) (hM : u*u≤M) (p : ℕ) :
    (u*u)*exactRootOpt M u p ≤ 300*M*2^(2*u-u/4) := by
  let b := exactRootOpt M u p
  by_cases hp : 0<b
  · have hM0 : u≤M := (show u≤u*u by nlinarith).trans hM
    obtain ⟨q,hlegal,hcert⟩ := (finite_optimum_exact O hn2 M u p hp).2 (le_refl b)
    obtain ⟨t,_,_,hd,hb⟩ := actual_profile_finite_upper O hn2 M u p hM0 q hlegal b hcert
    have hi : level t.val < u := (Finset.mem_filter.mp t.property).2.2
    have hv := actual_depth_lower hu hM hd
    exact scaled_deepest_upper hu hM hi (by omega) hb
  · have hb : b=0 := by omega
    change (u*u)*b ≤ _
    rw [hb,mul_zero]
    exact Nat.zero_le _

/-- Explicit finite analogue of the manuscript's optimized Θ scale.
The source asymptotic regime eventually satisfies these guards. -/
theorem optimized_root_two_sided {K : Type*} [Field K] [CharZero K] (O : Subring K)
    [IsLocalRing O] (hn2 : ¬IsUnit (2:O)) {M u : ℕ} (hu : 16≤u) (hM : u*u≤M) (p : ℕ) :
    M*2^(2*u-u/4) ≤ 2*(u*u)*exactRootOpt M u p ∧
      (u*u)*exactRootOpt M u p≤300*M*2^(2*u-u/4) :=
  ⟨scaled_exact_optimum_lower O hn2 (by omega) hM p,scaled_exact_optimum_upper O hn2 hu hM p⟩

#print axioms polynomial_tail_le_dyadic
#print axioms allowance_quantitative
#print axioms actual_depth_lower
#print axioms scaled_deepest_upper
#print axioms scaled_exact_optimum_upper
#print axioms optimized_root_two_sided
end Paper5.PrecisionOpt
