import P5MainIteratorChoose
import P5MainIteratorTail

/-! The nontrivial high-Q, small-R optimizer branch of F.A4.
All eventual scalar margins are explicit inputs to the finite theorem. -/
namespace P5MainIterator
open scoped BigOperators Classical
open Real

noncomputable def targetScale (L l : ℝ) : ℝ := l^2 / sqrt L

theorem tail_forces_width_ratio (n Q R : ℕ) (T L l : ℝ)
    (hn : 0<n) (hq : 0<Q) (hL : 0<L) (hl : 0<l)
    (hQ : (Q:ℝ)≤4*L/l)
    (htail : ((n:ℝ)/2)*(tailConstant * exp (-(64*(R:ℝ)^2/(Q:ℝ)))) ≤ T)
    (hbelow : T < (n:ℝ)*targetScale L l)
    (hthreshold : l/4 ≤ log tailConstant - log (2*targetScale L l)) :
    (l/sqrt L)/32 ≤ (R:ℝ)/(Q:ℝ) := by
  have hnr : 0<(n:ℝ) := by exact_mod_cast hn
  have hqr : 0<(Q:ℝ) := by exact_mod_cast hq
  have hα : 0<targetScale L l := by unfold targetScale; positivity
  let u := 64*(R:ℝ)^2/(Q:ℝ)
  have hsmall : exp (-u)<2*targetScale L l/tailConstant := by
    apply (lt_div_iff₀ tailConstant_pos).mpr
    apply (mul_lt_mul_iff_right₀ hnr).mp
    have h : ((n:ℝ)/2)*(tailConstant * exp (-u)) < (n:ℝ)*targetScale L l :=
      htail.trans_lt hbelow
    linarith only [h]
  have hlog := log_lt_log (exp_pos _) hsmall
  rw [log_exp,log_div (by positivity) tailConstant_pos.ne'] at hlog
  have hw : l ≤ 256*(R:ℝ)^2/(Q:ℝ) := by
    calc
      _ ≤ 4*u := by linarith only [hlog,hthreshold]
      _ = _ := by dsimp [u]; ring
  have h₁ : l*(Q:ℝ) ≤ 256*(R:ℝ)^2 := (le_div_iff₀ hqr).mp hw
  have h₂ : l*(Q:ℝ) ≤ 4*L := by rw [mul_comm]; exact (le_div_iff₀ hl).mp hQ
  have hsq : l^2 * (Q:ℝ)^2 ≤ (1024*L)*(R:ℝ)^2 := by
    calc
      _ = (l*(Q:ℝ))*(l*(Q:ℝ)) := by ring
      _ ≤ (4*L)*(256*(R:ℝ)^2) := mul_le_mul h₂ h₁ (by positivity) (by positivity)
      _ = _ := by ring
  have he : ((l/sqrt L)/32)^2 ≤ ((R:ℝ)/(Q:ℝ))^2 := by
    rw [show (l/sqrt L)/32=l/(sqrt L*32) by ring,div_pow,div_pow,mul_pow,sq_sqrt hL.le]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    norm_num
    nlinarith only [hsq]
  by_contra! hh
  have hf := pow_lt_pow_left₀ hh (by positivity : 0≤(R:ℝ)/(Q:ℝ)) (by decide : (2:ℕ)≠0)
  exact (not_lt_of_ge he) hf

set_option maxHeartbeats 4600000 in
theorem entropy_selected_width {V : Type*} [Fintype V] [DecidableEq V]
    (q T Q R : ℕ) (L l κ δ : ℝ)
    (hL : 0<L) (hl : 0<l) (hκ : 0<κ) (_hδ : 0<δ) (hδκ : δ≤κ/32) (hδ1 : δ≤1)
    (hscale : l/sqrt L ≤ exp (-l/4))
    (hsize : 2≤δ*(Fintype.card V:ℝ)*l/sqrt L)
    (hwidth : (l/sqrt L)/32 ≤ (R:ℝ)/(Q:ℝ))
    (horder : ⌊κ*(Fintype.card V:ℝ)*(R:ℝ)/(Q:ℝ)⌋₊≤q)
    (ht : (TaylorList V q).card≤T) :
    (δ/(8*log 2))*(Fintype.card V:ℝ)*targetScale L l ≤ logTwo T := by
  let n := Fintype.card V
  let x := δ*(n:ℝ)*l/sqrt L
  let j := ⌊x⌋₊
  have hx : 2≤x := hsize
  have hx0 : 0≤x := by linarith only [hx]
  have hlarge := Nat.lt_floor_add_one x
  have hjlo : x/2≤(j:ℝ) := by dsimp [j]; linarith only [hx,hlarge]
  have hjr : 0<(j:ℝ) := by linarith only [hjlo,hx]
  have hjp : 0<j := by exact_mod_cast hjr
  have hjup : (j:ℝ)≤x := Nat.floor_le hx0
  have hu : x≤κ*(n:ℝ)*(R:ℝ)/(Q:ℝ) := by
    calc
      _ = (δ*(n:ℝ))*(l/sqrt L) := by dsimp [x]; ring
      _ ≤ ((κ/32)*(n:ℝ))*(l/sqrt L) := by
        gcongr
      _ = (κ*(n:ℝ))*((l/sqrt L)/32) := by ring
      _ ≤ (κ*(n:ℝ))*((R:ℝ)/(Q:ℝ)) := mul_le_mul_of_nonneg_left hwidth (by positivity)
      _ = _ := by ring
  have hjq : j≤q := (Nat.floor_mono hu).trans horder
  have hbound : (j:ℝ)≤(n:ℝ)*exp (-l/4) := by
    apply hjup.trans
    calc
      x = (δ*(l/sqrt L))*(n:ℝ) := by dsimp [x]; ring
      _ ≤ (1*exp (-l/4))*(n:ℝ) := by
        gcongr
      _ = _ := by ring
  have hjn : j≤n := by
    have he : exp (-l/4)≤1 := by rw [←exp_zero]; apply exp_le_exp.mpr; linarith only [hl]
    have hB : (j:ℝ)≤(n:ℝ) := hbound.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left he (by positivity : 0≤(n:ℝ)))
    exact_mod_cast hB
  have hratio : exp (l/4) ≤ (n:ℝ)/(j:ℝ) := by
    apply (le_div_iff₀ hjr).mpr
    calc
      _ ≤ exp (l/4)*((n:ℝ)*exp (-l/4)) :=
        mul_le_mul_of_nonneg_left hbound (exp_nonneg _)
      _ = _ := by rw [mul_left_comm,←exp_add,show l/4 + -l/4 = 0 by ring,exp_zero,mul_one]
  have hlog := log_le_log (exp_pos _) hratio
  rw [log_exp] at hlog
  have hlog2 : 0<log 2 := log_pos (by norm_num)
  have hprec : (l/4)/log 2 ≤ logTwo ((n:ℝ)/(j:ℝ)) :=
    div_le_div_of_nonneg_right hlog hlog2.le
  have hcost := paid_taylor_entropy q j T hjp hjq hjn ht
  calc
    _ = (x/2)*((l/4)/log 2) := by unfold targetScale x; ring
    _ ≤ (j:ℝ)*logTwo ((n:ℝ)/(j:ℝ)) :=
      mul_le_mul hjlo hprec (by positivity) (by positivity)
    _ ≤ _ := hcost

#print axioms tail_forces_width_ratio
#print axioms entropy_selected_width
end P5MainIterator
