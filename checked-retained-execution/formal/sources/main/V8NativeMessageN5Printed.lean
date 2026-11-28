import V8NativeMessageN5Native
import P5HybridClosurePrintedMain

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3600000
set_option maxRecDepth 3500

/-! Evaluates N5 at the printed four-copy MAIN size. Group count is
r=floor(sqrt(lambda)/nu²), not the differently named deformation
degree R. The finite guard displays where polynomial-width delivery
and polynomial MAIN order are spent. -/
namespace V8NativeMessage.N5
open scoped Classical BigOperators Polynomial
open Paper5.D1Literal J6R9Recursive N4 Paper5.HybridClosure.Printed
noncomputable section

theorem printed_groups_plus_one (N : ℕ) (hr : 1≤mainR N) (hNu : 0<mainNu N) :
    (mainR N:ℝ)+1≤2*Real.sqrt (mainLambda N:ℝ)/(mainNu N:ℝ)^2 := by
  have hNu' : 0<(mainNu N:ℝ) := by exact_mod_cast hNu
  have h₁ : (1:ℝ)≤mainR N := by exact_mod_cast hr
  have h₂ : (mainR N:ℝ)≤Real.sqrt (mainLambda N:ℝ)/(mainNu N:ℝ)^2 := by
    rw [main_r_literal N hNu]
    exact Nat.floor_le (div_nonneg (Real.sqrt_nonneg _) (sq_nonneg _))
  rw [mul_div_assoc]
  linarith only [h₁,h₂]

theorem subtract_log_with_polynomial_width (a : ℝ) (N e width κ T r : ℕ)
    (hw : 0<width) (hp : width≤(N+1)^e)
    (h : (a-Real.logb 2 κ)/(r+1)-Real.logb 2 width≤Real.logb 2 T) :
    (a-Real.logb 2 κ)/(r+1)-(e:ℝ)*Real.logb 2 (N+1)≤Real.logb 2 T := by
  have h₁ : 0<(width:ℝ) := by exact_mod_cast hw
  have h₂ : (width:ℝ)≤((N:ℝ)+1)^e := by exact_mod_cast hp
  have h₃ := Real.logb_le_logb_of_le (b:=2) (by norm_num) h₁ h₂
  rw [Real.logb_pow] at h₃
  exact (sub_le_sub_left h₃ _).trans h

/-- Once the explicit half-budget is available, the two advertised
scales follow by inserting the applicable lower bound on 'a'. This
lemma is finite and does not assert that an unmetered oracle pays it. -/
theorem guarded_printed_scale (a : ℝ) (N e width κ T : ℕ)
    (hNu : 0<mainNu N) (hr : 1≤mainR N) (hLam : 0<mainLambda N) (hw : 0<width)
    (ha : 0≤a) (hp : width≤(N+1)^e)
    (half : 2*(Real.logb 2 κ+((mainR N:ℝ)+1)*(e*Real.logb 2 (N+1)))≤a)
    (h : (a-Real.logb 2 κ)/(mainR N+1)-Real.logb 2 width≤Real.logb 2 T) :
    a*(mainNu N:ℝ)^2/(4*Real.sqrt (mainLambda N:ℝ))≤Real.logb 2 T := by
  have hNu' : 0<(mainNu N:ℝ) := by exact_mod_cast hNu
  have hLam' : 0<(mainLambda N:ℝ) := by exact_mod_cast hLam
  let r : ℝ := (mainR N:ℝ)+1
  let v : ℝ := (mainNu N:ℝ)^2
  let s := Real.sqrt (mainLambda N:ℝ)
  let L := (e:ℝ)*Real.logb 2 (N+1)
  let K := Real.logb 2 κ
  have rp : 0<r := by dsimp [r]; positivity
  have vp : 0<v := by dsimp [v]; positivity
  have sp : 0<s := Real.sqrt_pos.2 hLam'
  have hh : (a-K)/r-L≤Real.logb 2 T :=
    subtract_log_with_polynomial_width a N e width κ T (mainR N) hw hp h
  have hb : 2*(K+r*L)≤a := half
  have hs : a/(2*r)≤(a-K)/r-L := by
    apply (le_sub_iff_add_le).2
    rw [show a/(2*r)=a/2/r by rw [div_div]]
    apply (le_div_iff₀ rp).2
    rw [add_mul,div_mul_cancel₀ _ rp.ne']
    nlinarith only [hb]
  have rg : r≤2*s/v := printed_groups_plus_one N hr hNu
  have br : (2*r)*v≤4*s := by
    have h' := (le_div_iff₀ vp).1 rg
    nlinarith only [h']
  have hcut : a*v/(4*s)≤a/(2*r) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    calc
      (a*v)*(2*r)=a*((2*r)*v) := by ring
      _ ≤ a*(4*s) := mul_le_mul_of_nonneg_left br ha
  exact hcut.trans (hs.trans hh)

variable {X : Type} {H L : Type*} [Fintype X] [DecidableEq X] [Fintype H]
  {F : Finset (X×X)} {reg : ∀ v,GraphCutMoments.degree F v=3} {f : ℤ[X]}
  {P : RootPacking F reg f} {d : LayoutReady F reg f} {i : rootKept F f}
  [Fact (Irreducible (ratPoly f))] [Fact (Irreducible (NativeProbeRing.residuePoly f))]
  {γ : ℝ} (C : FourCut P i γ) (Qs : H→OrdinaryQuery P d i) (hf : f.Monic)
  (σ : X→Bool) {width : ℕ} {t : Trace L (NativePayload f) width}

include C in
theorem original_printed_N5
    (actual : ExplicitReceipts Qs hf σ t) (correct : RightTerminal Qs hf)
    (hR : ∀ h,(Qs h).groups≤mainR (Fintype.card X)) :
    (γ*(Fintype.card X:ℝ)/68-Real.logb 2 ((12*Fintype.card X+1:ℕ):ℝ))/
      (mainR (Fintype.card X)+1)-Real.logb 2 width≤Real.logb 2 (time t) :=
  original_N5_log (C:=C) (Qs:=Qs) (hf:=hf) (σ:=σ) actual correct
    (κmax:=12*Fintype.card X+1) (rmax:=mainR (Fintype.card X)) (fun h=>true_order_bound (Qs h)) hR

#print axioms printed_groups_plus_one
#print axioms subtract_log_with_polynomial_width
#print axioms guarded_printed_scale
#print axioms original_printed_N5
end
end V8NativeMessage.N5