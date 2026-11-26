import P5PrecisionOptAverage
import P5PrecisionOptChoices

/-! Native P.9: the shell mean inequality follows for every legal
pointwise profile. Zero order gives zero weighted contribution and
requires no error inequality at that point. -/
namespace Paper5.PrecisionOpt
open P1DyadicGrid HermiteLoss
open scoped BigOperators

def RootInequalities (M u p : ℕ) (q : Profile u) (b : ℕ) : Prop :=
  ∀ t,0<q t →
    ((b:ℤ)+(q t:ℤ)-2)*Paper5.P3.nativeLoss (2*u) t.val ≤
      Paper5.P3.rootPrecision u M (Paper5.P3.printedHeight u M) p t.val-p+
        Paper5.P3.nativeCarrierVal Subtype.val q t

def rootSlack (M u i : ℕ) : ℕ :=
  8*sourceH M u*2^(2*u-i)+8*M*(2*u+1)

theorem rootSlack_eq (M u p : ℕ) (t : Paper5.P3.rootNodes u) :
    Paper5.P3.rootPrecision u M (Paper5.P3.printedHeight u M) p t.val-p =
      (rootSlack M u (level t.val):ℤ) := by
  unfold rootSlack Paper5.P3.rootPrecision
  change (p:ℤ)+8*(sourceH M u:ℤ)*(2:ℤ)^(2*u-level t.val)+8*(M:ℤ)*(2*(u:ℤ)+1)-(p:ℤ)=_
  push_cast
  ring

theorem weighted_node_shell_cap (M u p b : ℕ) (q : Profile u) (hb : 0<b)
    (h : RootInequalities M u p q b) (t : Paper5.P3.rootNodes u) :
    (q t:ℚ)*(sameShellCost u q t:ℚ) ≤
      (q t:ℚ)*((higherShellGain u q (level t.val):ℚ)+(rootSlack M u (level t.val):ℚ)) := by
  by_cases hq : 0<q t
  · have hn : 0≤((b:ℤ)+(q t:ℤ)-2)*Paper5.P3.nativeLoss (2*u) t.val :=
      Int.mul_nonneg (by omega) (Paper5.P3.native_loss_positive
        (Finset.mem_filter.mp t.property).1 (Finset.mem_filter.mp t.property).2.1).le
    have H := hn.trans (h t hq)
    rw [rootSlack_eq,arbitrary_profile_carrier] at H
    have H' : sameShellCost u q t ≤ (higherShellGain u q (level t.val))+(rootSlack M u (level t.val):ℤ) := by
      omega
    have HH : (sameShellCost u q t:ℚ) ≤
        (higherShellGain u q (level t.val):ℚ)+(rootSlack M u (level t.val):ℚ) := by exact_mod_cast H'
    exact mul_le_mul_of_nonneg_left HH (by positivity)
  · have hz : q t=0 := by omega
    simp [hz]

theorem shell_mean_product_ineq (M u p b : ℕ) (hM : u≤M) (q : Profile u)
    (hlegal : admissibleOrders M u q) (hb : 0<b) (h : RootInequalities M u p q b)
    (i : ℕ) :
    2*((2:ℚ)^(2*u-i)-1)*shellMean u q i ≤
      (higherShellGain u q i:ℚ)+(rootSlack M u i:ℚ)+4*(M:ℚ)*(2*u-i:ℕ) := by
  let w (t : NativeShell u i) : ℚ := q t.val
  let W : ℚ := ∑ t,w t
  let n := 2*u-i
  let D : ℚ := (2:ℚ)^n
  let G : ℚ := higherShellGain u q i
  let F : ℚ := rootSlack M u i
  let E : ℚ := ∑ t : NativeShell u i,w t*(sameShellCost u q t.val:ℚ)
  let Z : ℚ := ∑ t : NativeShell u i,w t^2
  have hD : 0<D := by dsimp [D]; positivity
  have hw0 (t : NativeShell u i) : 0≤w t := by dsimp [w]; positivity
  have hW : 0≤W := Finset.sum_nonneg fun t _ => hw0 t
  have hMass : W=(shellOrderMass u q i:ℚ) := by
    unfold shellOrderMass
    rw [Nat.cast_sum]
    exact native_shell_sum u i (fun t => (q t:ℚ))
  have hMean : shellMean u q i=W/D := by unfold shellMean; rw [←hMass]
  by_cases h0 : W=0
  · rw [hMean,h0,zero_div,mul_zero]
    have hgZ : 0≤higherShellGain u q i := by
      apply Finset.sum_nonneg
      intro t _
      positivity
    have hg : 0≤G := by
      change 0≤(higherShellGain u q i:ℚ)
      exact_mod_cast hgZ
    change 0≤G+(rootSlack M u i:ℚ)+4*(M:ℚ)*(n:ℚ)
    positivity
  have hE : E = (∑ t : NativeShell u i, ∑ s∈Finset.univ.erase t,w t*w s*(shellDistance t s:ℚ)) := by
    unfold E
    apply Finset.sum_congr rfl
    intro t _
    rw [shellCost_as_distance,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    change w t*(w s*(shellDistance t s:ℚ)) = _
    rw [mul_assoc]
  have hc : 2*(1-1/D)*W^2≤E+(n:ℚ)*Z := by
    rw [hE]
    exact actual_grid_p8 w
  have hZ : Z≤4*(M:ℚ)*W := by
    unfold Z W
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t _
    have H : w t≤4*(M:ℚ) := by
      dsimp [w]
      exact_mod_cast (hlegal t.val).trans (q_cap M u _ hM)
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right H (hw0 t)
  have hCap : E≤ W*(G+F) := by
    unfold E W
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro t _
    have H := weighted_node_shell_cap M u p b q hb h t.val
    rw [show level t.val.val=i from rawShell_level t] at H
    exact H
  have hu : 2*(1-1/D)*W^2 ≤ W*(G+F+4*(M:ℚ)*(n:ℚ)) := by
    calc
      _ ≤ E+(n:ℚ)*Z := hc
      _ ≤ W*(G+F)+(n:ℚ)*(4*(M:ℚ)*W) :=
        add_le_add hCap (mul_le_mul_of_nonneg_left hZ (by positivity))
      _ = _ := by ring
  change 2*(D-1)*shellMean u q i≤G+F+4*(M:ℚ)*(n:ℚ)
  rw [hMean]
  apply (mul_le_mul_iff_right₀ (lt_of_le_of_ne hW (Ne.symm h0))).mp
  calc
    W*(2*(D-1)*(W/D)) = 2*(1-1/D)*W^2 := by field_simp
    _ ≤ _ := hu

theorem arbitrary_native_p9 (M u p b : ℕ) (hM : u≤M) (q : Profile u)
    (hlegal : admissibleOrders M u q) (hb : 0<b) (hcert : RootInequalities M u p q b)
    (i : ℕ) (hi : i<u) :
    2*shellMean u q i -
        (∑ j∈Finset.range u,((j-i:ℕ):ℚ)/(2:ℚ)^(j-i)*shellMean u q j) ≤
      8*(sourceH M u:ℚ)+(M:ℚ)*(12*(2*u:ℕ)+16)/(2:ℚ)^(u+1) := by
  let n := 2*u-i
  let D : ℚ := (2:ℚ)^n
  let G : ℚ := higherShellGain u q i
  let m := shellMean u q i
  let C : ℚ := (M:ℚ)*(12*(2*u:ℕ)+16)
  have hD : 0<D := by dsimp [D]; positivity
  have hc : 0≤C := by dsimp [C]; positivity
  have hpow : (2:ℚ)^(u+1) ≤ D := by
    dsimp [D,n]
    exact pow_le_pow_right₀ (by norm_num : (1:ℚ)≤2) (by omega)
  have hm : m≤4*(M:ℚ) := shellMean_le_4M q hM hlegal i hi
  have hn : (n:ℚ)≤(2*u:ℕ) := by exact_mod_cast Nat.sub_le (2*u) i
  have hconst : 8*(M:ℚ)*((2*u:ℕ)+1)+4*(M:ℚ)*(n:ℚ)+2*m≤C := by
    have hN := mul_le_mul_of_nonneg_left hn (by positivity : 0≤4*(M:ℚ))
    dsimp [C]
    push_cast at *
    linarith
  have H := shell_mean_product_ineq M u p b hM q hlegal hb hcert i
  change 2*(D-1)*m≤G+(rootSlack M u i:ℚ)+4*(M:ℚ)*(n:ℚ) at H
  have he : (rootSlack M u i:ℚ)=8*(sourceH M u:ℚ)*D+8*(M:ℚ)*((2*u:ℕ)+1) := by
    unfold rootSlack
    push_cast
    rfl
  rw [he] at H
  have hA : 2*m-G/D ≤ 8*(sourceH M u:ℚ)+ C/D := by
    apply (mul_le_mul_iff_right₀ hD).mp
    have h1 : D*(2*m-G/D)=2*D*m-G := by field_simp
    have h2 : D*(8*(sourceH M u:ℚ)+C/D)=8*(sourceH M u:ℚ)*D+C := by field_simp
    rw [h1,h2]
    linarith
  have hB := div_le_div_of_nonneg_left hc (by positivity : 0<(2:ℚ)^(u+1)) hpow
  rw [←higher_gain_as_means]
  exact hA.trans (add_le_add_left hB _)

theorem actual_certificate_inequalities {K : Type*} [Field K] [CharZero K] (O : Subring K)
    [IsLocalRing O] (hn2 : ¬IsUnit (2:O)) (M u p : ℕ) (q : Profile u) (b : ℕ)
    (h : RootCertified O hn2 M u p q b) : RootInequalities M u p q b :=
  (Paper5.P3.printed_root_p1 O hn2 u M (Paper5.P3.printedHeight u M) p b h.1.1 q).mp h.2

#print axioms rootSlack_eq
#print axioms weighted_node_shell_cap
#print axioms shell_mean_product_ineq
#print axioms arbitrary_native_p9
#print axioms actual_certificate_inequalities
end Paper5.PrecisionOpt
