import P5PrecisionOptSatWindow
import P5PrecisionOptChoices

/-! Quantitative optimized lower bound with a directly stated finite
regime, avoiding asymptotic constants hidden in the chosen taper. -/
namespace Paper5.PrecisionOpt
open P1DyadicGrid HermiteLoss
open scoped BigOperators

theorem positive_left_cancel {k x y : ℕ} (hk : 0<k) (h : k*x≤k*y) : x≤y := by
  by_contra hn
  have h' := Nat.mul_lt_mul_of_pos_left (Nat.lt_of_not_ge hn) hk
  omega

theorem adapted_depth_quarter {M u : ℕ} (hu : 8≤u) (hM : u*u≤M) :
    adaptedDepth M u≤u/4+4 := by
  have hp : 0<u := by omega
  have hM0 : u≤M := (show u≤u*u by nlinarith).trans hM
  let h := sourceH M u
  let H := adaptedHeight M u
  let k := u/4+2
  have Hpos : 0<H := (adapted_profile_parameters hu hM0).1
  have hh : 3*M≤h*u := h_cover M u hp
  have hhM : 3*(u*u)≤h*u := (Nat.mul_le_mul_left 3 hM).trans hh
  have huu : u≤h := by
    apply positive_left_cancel hp
    nlinarith
  have hHu : u≤H := huu.trans (adapted_height_arithmetic M u).1
  have hdiv : 4*h≤3*H+2 := by
    have hm := Nat.mod_lt (4*h) (by decide : 0<3)
    have hN := Nat.div_add_mod (4*h) 3
    change 3*H+(4*h)%3=4*h at hN
    omega
  have hm := Nat.mul_le_mul_right u hdiv
  have hmain : 4*M≤H*u+u := by nlinarith
  have hk : u+5≤4*k := by
    have hh := Nat.div_add_mod u 4
    have H := Nat.mod_lt u (by decide : 0<4)
    dsimp [k]
    omega
  have hb : M≤H*k := by
    apply positive_left_cancel (by decide : 0<4)
    calc
      4*M ≤ H*u+u := hmain
      _ ≤ H*(u+5) := by nlinarith
      _ ≤ H*(4*k) := Nat.mul_le_mul_left _ hk
      _ = _ := by ring
  have hfloor : (M+H-1)/H≤k := by
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul Hpos).2
    rw [Nat.succ_eq_add_one,add_mul,one_mul,Nat.mul_comm k H]
    omega
  change (M+H-1)/H+2 ≤ u/4+4
  dsimp [k] at hfloor
  omega

theorem scaled_adapted_window_lower {M u : ℕ} (hu : 8≤u) (hM : u*u≤M) :
    M*2^(2*u-u/4) ≤ 2*(u*u)*adaptedWindow M u := by
  have hM0 : u≤M := (show u≤u*u by nlinarith).trans hM
  let H := adaptedHeight M u
  let v := adaptedDepth M u
  let T := (2:ℕ)^(2*u-u/4)
  let Y := (2:ℕ)^(2*u-v)
  let L := (2:ℕ)^(2*u)
  let D := 2*u+1
  let W := 8*H*Y
  let s := orderMass u (adaptedProfile M u)-Paper5.P3.printedDegree u M
  let b := 4*M+W/D
  have hh : 3*M≤H*u := (h_cover M u (by omega)).trans
    (Nat.mul_le_mul_right u ((adapted_height_arithmetic M u).1))
  have hp : v≤u/4+4 := adapted_depth_quarter hu hM
  have hTY : T≤16*Y := by
    have h := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (show 2*u-u/4≤2*u-v+4 by omega)
    rw [pow_add,show (2:ℕ)^4=16 by decide,mul_comm (2^(2*u-v)) 16] at h
    exact h
  have hTL : T≤L := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (Nat.sub_le ..)
  have h1 : M*T≤2*(u*u)*s := by
    obtain ⟨_,_,hv,hcov,_⟩ := adapted_profile_parameters hu hM0
    have hs : 2*H*L+M≤s := taperProfile_degree_slack M u v H hv hcov
    have hU : u≤2*(u*u) := by nlinarith
    have hHL : H*L≤2*H*L+M := by
      rw [show 2*H*L=H*L+H*L by ring]
      omega
    calc
      M*T ≤ M*L := Nat.mul_le_mul_left _ hTL
      _ ≤ (H*u)*L := Nat.mul_le_mul_right _ (by omega)
      _ = u*(H*L) := by ring
      _ ≤ (2*(u*u))*s :=
        Nat.mul_le_mul hU (hHL.trans hs)
  have h2 : M*T≤2*(u*u)*b := by
    have hW : W≤b*D := by
      have hz := Nat.mod_lt W (show 0<D by dsimp [D]; omega)
      have hh := Nat.div_add_mod W D
      have hq : W/D+1≤b := by dsimp [b]; omega
      have h2 : W≤(W/D+1)*D := by
        rw [add_mul,one_mul,mul_comm (W/D) D]
        omega
      exact h2.trans (Nat.mul_le_mul_right D hq)
    have hD : D≤3*u := by dsimp [D]; omega
    have hp : 24*(M*T)≤16*u*W := by
      calc
        24*(M*T) = 8*(3*M)*T := by ring
        _ ≤ 8*(H*u)*T := Nat.mul_le_mul_right T (Nat.mul_le_mul_left _ hh)
        _ ≤ 8*(H*u)*(16*Y) := Nat.mul_le_mul_left _ hTY
        _ = _ := by dsimp [W]; ring
    have hi : 16*u*W≤24*(2*(u*u)*b) := by
      calc
        _ ≤ (16*u)*(b*D) := Nat.mul_le_mul_left _ hW
        _ ≤ (16*u)*(b*(3*u)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hD)
        _ = _ := by ring
    exact positive_left_cancel (by decide : 0<24) (hp.trans hi)
  change M*T≤2*(u*u)*min s b
  rw [←Nat.mul_min_mul_left]
  exact le_min h1 h2

theorem scaled_exact_optimum_lower {K : Type*} [Field K] [CharZero K] (O : Subring K)
    [IsLocalRing O] (hn2 : ¬IsUnit (2:O)) {M u : ℕ} (hu : 8≤u) (hM : u*u≤M) (p : ℕ) :
    M*2^(2*u-u/4) ≤ 2*(u*u)*exactRootOpt M u p := by
  have hM0 : u≤M := (show u≤u*u by nlinarith).trans hM
  have hL := scaled_adapted_window_lower hu hM
  have hO : adaptedWindow M u≤exactRootOpt M u p :=
    (finite_optimum_exact O hn2 M u p (adapted_window_pos hu hM0)).mp
      ⟨adaptedProfile M u,adapted_profile_admissible hu hM0,
        adapted_window_admissible hu hM0,adapted_window_actual O hn2 hu hM0 p⟩
  exact hL.trans (Nat.mul_le_mul_left _ hO)

#print axioms adapted_depth_quarter
#print axioms scaled_adapted_window_lower
#print axioms scaled_exact_optimum_lower
end Paper5.PrecisionOpt
