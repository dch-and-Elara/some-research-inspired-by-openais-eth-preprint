import P5FrontendG1TannerCertificate
import P5FrontendG1ExistenceCosh
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Exact finite counting form of the Rademacher/Hoeffding argument.
The uniform product sample space is exhibited by the literal shift
tuples and its exponential sum factors exactly. -/
namespace Paper5.FrontendG1.Tanner
open scoped BigOperators
open Real

noncomputable def signedReal (z : F₂) : ℝ := if z=0 then 1 else -1

noncomputable def realChar {ell : ℕ} (b u : Word ell) : ℝ :=
  signedReal (dotProduct b u)

noncomputable def realWalsh {ell d : ℕ} (s : Fin d→Word ell) (b : Word ell) : ℝ :=
  ∑ j, realChar b (s j)

theorem sourceWalsh_eq_real {ell d : ℕ} (s : Fin d→Word ell) (b : Word ell) :
    (sourceWalsh s b:ℝ)=realWalsh s b := by
  rw [sourceWalsh,realWalsh,Int.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : dotProduct b (s j)=0 <;> simp [realChar,signedReal,h]

theorem sourceAbsWalsh_eq_real {ell d : ℕ} (s : Fin d→Word ell) (b : Word ell) :
    ((sourceWalsh s b).natAbs:ℝ)=|realWalsh s b| := by
  rw [Nat.cast_natAbs,Int.cast_abs,sourceWalsh_eq_real]

private theorem add_one_sign (z : F₂) : signedReal (z+1) = -signedReal z := by
  rcases binary_cases z with hz|hz
  · simp [signedReal,hz]
  · rw [hz,show (1:F₂)+1=0 by decide]
    simp [signedReal]

theorem pivot_sign_flip {ell : ℕ} (b : Word ell) (j : Fin ell) (hj : b j=1)
    (u : Word ell) :
    realChar b (u+singlePort j) = -realChar b u := by
  have hk : dotProduct b (singlePort j)=1 := by
    simp [dotProduct,singlePort,mul_ite,hj]
  rw [realChar,dotProduct_add,hk,add_one_sign,realChar]

theorem word_exponential_sum {ell : ℕ} (b : Word ell) (hb : b≠0) (a : ℝ) :
    (∑ u : Word ell, exp (a*realChar b u)) = (Fintype.card (Word ell):ℝ)*cosh a := by
  classical
  have hNZ : ∃ j : Fin ell,b j≠0 := by
    by_contra! h
    apply hb
    funext j
    exact h j
  obtain ⟨j,hj₀⟩ := hNZ
  have hj : b j=1 := (binary_cases _).resolve_left hj₀
  have hS : (∑ u : Word ell,exp (-a*realChar b u))=∑ u : Word ell,exp (a*realChar b u) := by
    calc
      _ = ∑ u : Word ell,exp (a*realChar b ((Equiv.addRight (singlePort j)) u)) := by
        apply Finset.sum_congr rfl
        intro u _
        change exp (-a*realChar b u)=exp (a*realChar b (u+singlePort j))
        rw [pivot_sign_flip b j hj,mul_neg,neg_mul]
      _ = _ := Equiv.sum_comp (Equiv.addRight (singlePort j)) (fun (u : Word ell)=>exp (a*realChar b u))
  have hTwo : (∑ u : Word ell,exp (a*realChar b u))+
      (∑ u : Word ell,exp (a*realChar b u)) = (Fintype.card (Word ell):ℝ)*(2*cosh a) := by
    conv_lhs => arg 2; rw [←hS]
    rw [←Finset.sum_add_distrib]
    calc
      _ = ∑ _u : Word ell,2*cosh a := by
        apply Finset.sum_congr rfl
        intro u _
        by_cases hZ : dotProduct b u=0
        · simp [realChar,signedReal,hZ,Real.cosh_eq]
          ring
        · simp [realChar,signedReal,hZ,Real.cosh_eq]
          ring
      _ = _ := by simp [nsmul_eq_mul]
  linarith only [hTwo]

theorem tuple_exponential_sum {ell d : ℕ} (b : Word ell) (hb : b≠0) (a : ℝ) :
    (∑ s : Fin d→Word ell,exp (a*realWalsh s b)) =
      (((Fintype.card (Word ell)):ℝ)*cosh a)^d := by
  simp only [realWalsh,Finset.mul_sum,Real.exp_sum]
  calc
    _ = ∏ _j : Fin d,∑ u : Word ell,exp (a*realChar b u) :=
      (Fintype.prod_sum (fun (_j : Fin d) (u : Word ell)=>exp (a*realChar b u))).symm
    _ = _ := by simp [word_exponential_sum b hb a]

noncomputable def tiltedTail {ell : ℕ} (d : ℕ) (b : Word ell) (a : ℝ) :
    Finset (Fin d→Word ell) := by
  classical
  exact Finset.univ.filter fun s=>a^2*(d:ℝ)≤a*realWalsh s b

theorem tuple_card_real {ell d : ℕ} :
    (Fintype.card (Fin d→Word ell):ℝ)=((Fintype.card (Word ell)):ℝ)^d := by simp

theorem tilted_tail_bound {ell d : ℕ} (b : Word ell) (hb : b≠0) (a : ℝ) :
    ((tiltedTail d b a).card:ℝ) ≤
      (Fintype.card (Fin d→Word ell):ℝ)*exp (-(a^2*(d:ℝ)/2)) := by
  classical
  let S := tiltedTail d b a
  let n := (d:ℝ)
  let Q := (Fintype.card (Word ell):ℝ)
  have h1 : (S.card:ℝ)*exp (a^2*n) ≤ ∑ s∈S,exp (a*realWalsh s b) := by
    rw [←nsmul_eq_mul,←Finset.sum_const]
    apply Finset.sum_le_sum
    intro s hs
    exact Real.exp_le_exp.mpr (Finset.mem_filter.mp hs).2
  have h2 : (∑ s∈S,exp (a*realWalsh s b)) ≤
      ∑ s : Fin d→Word ell,exp (a*realWalsh s b) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)
  have h3 : (∑ s : Fin d→Word ell,exp (a*realWalsh s b)) ≤ Q^d*exp (a^2*n/2) := by
    rw [tuple_exponential_sum b hb a]
    calc
      _ ≤ (Q*exp (a^2/2))^d := by
        have hQ : 0≤Q := by dsimp [Q]; positivity
        exact pow_le_pow_left₀ (mul_nonneg hQ (Real.cosh_pos a).le)
          (mul_le_mul_of_nonneg_left (cosh_exponential_bound a) hQ) _
      _ = _ := by rw [mul_pow,←Real.exp_nat_mul]; congr 2; dsimp [n]; ring
  change (S.card:ℝ)≤(Fintype.card (Fin d→Word ell):ℝ)*exp (-(a^2*n/2))
  rw [tuple_card_real]
  calc
    _ ≤ Q^d*exp (a^2*n/2)/exp (a^2*n) :=
      (le_div_iff₀ (Real.exp_pos _)).mpr (h1.trans (h2.trans h3))
    _ = _ := by
      rw [mul_div_assoc,←Real.exp_sub]
      congr 2
      ring

noncomputable def badAbsTail {ell : ℕ} (d : ℕ) (b : Word ell) (ε : ℝ) :
    Finset (Fin d→Word ell) := by
  classical
  exact Finset.univ.filter fun s=>ε*(d:ℝ) < |realWalsh s b|

theorem bad_abs_tail_bound {ell d : ℕ} (b : Word ell) (hb : b≠0) (ε : ℝ) (hε : 0≤ε) :
    ((badAbsTail d b ε).card:ℝ) ≤
      2*(Fintype.card (Fin d→Word ell):ℝ)*exp (-(ε^2*(d:ℝ)/2)) := by
  classical
  have hsub : badAbsTail d b ε⊆tiltedTail d b ε∪tiltedTail d b (-ε) := by
    intro s hs
    have h := (Finset.mem_filter.mp hs).2
    by_cases hpos : 0≤realWalsh s b
    · rw [abs_of_nonneg hpos] at h
      apply Finset.mem_union.mpr
      apply Or.inl
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
      calc
        _ = ε*(ε*(d:ℝ)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h.le hε
    · rw [abs_of_neg (lt_of_not_ge hpos)] at h
      apply Finset.mem_union.mpr
      apply Or.inr
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
      calc
        _ = ε*(ε*(d:ℝ)) := by ring
        _ ≤ ε*(-realWalsh s b) := mul_le_mul_of_nonneg_left h.le hε
        _ = _ := by ring
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hcR :
      ((badAbsTail d b ε).card:ℝ) ≤ (tiltedTail d b ε).card + (tiltedTail d b (-ε)).card := by
    exact_mod_cast hc
  have h1 := tilted_tail_bound (d:=d) b hb ε
  have h2 := tilted_tail_bound (d:=d) b hb (-ε)
  rw [neg_sq] at h2
  linarith only [hcR,h1,h2]

#print axioms sourceWalsh_eq_real
#print axioms sourceAbsWalsh_eq_real
#print axioms pivot_sign_flip
#print axioms word_exponential_sum
#print axioms tuple_exponential_sum
#print axioms tuple_card_real
#print axioms tilted_tail_bound
#print axioms bad_abs_tail_bound
end Paper5.FrontendG1.Tanner