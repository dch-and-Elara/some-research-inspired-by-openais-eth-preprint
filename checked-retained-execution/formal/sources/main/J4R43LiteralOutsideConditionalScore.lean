import J4R43LiteralOutsideConditionalMoments

/-! Exact low-dimensional evaluation of the conditional squared-deviation
objective. This is the score used to choose a mark, not an exponential
sum over completions or a supplied optimal matching. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators
open IndependentThinning
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 6000000

variable {U C : Type*} [Fintype U] [DecidableEq U] [Fintype C] [DecidableEq C]

theorem expectation_sum (a : U→Option Bool) {J : Type*} (s : Finset J)
    (f : J→(U→Bool)→ℚ) :
    conditionalExpected a (fun w=>∑ j∈s,f j w) =
      ∑ j∈s,conditionalExpected a (f j) := by
  simp only [conditionalExpected,Finset.mul_sum]
  exact Finset.sum_comm

theorem expectation_scale (a : U→Option Bool) (c : ℚ) (f : (U→Bool)→ℚ) :
    conditionalExpected a (fun w=>c*f w)=c*conditionalExpected a f := by
  simp only [conditionalExpected,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun w _=>by ring)

theorem expectation_add (a : U→Option Bool) (f g : (U→Bool)→ℚ) :
    conditionalExpected a (fun w=>f w+g w)=conditionalExpected a f+conditionalExpected a g := by
  simp only [conditionalExpected,mul_add,Finset.sum_add_distrib]

theorem expectation_sub (a : U→Option Bool) (f g : (U→Bool)→ℚ) :
    conditionalExpected a (fun w=>f w-g w)=conditionalExpected a f-conditionalExpected a g := by
  simp only [conditionalExpected,mul_sub,Finset.sum_sub_distrib]

theorem expectation_const (a : U→Option Bool) (c : ℚ) :
    conditionalExpected a (fun _=>c)=c := by
  rw [conditionalExpected,←Finset.sum_mul,conditional_mass_total,one_mul]

def rawCount (B : U→Finset U) (label : U→C) (c : C) (w : U→Bool) : ℚ :=
  ∑ e,colourWeight label c e*rawIndicator B e w

def rawScore (B : U→Finset U) (label : U→C) (w : U→Bool) : ℚ :=
  ∑ c, (rawCount B label c w-meanAt B label c)^2

def conditionalCell (a : U→Option Bool) (B : U→Finset U) (label : U→C) (c : C) : ℚ :=
  (∑ e : U, ∑ e' : U, colourWeight label c e*colourWeight label c e'*twoMoment a B e e') -
    (2*meanAt B label c)*(∑ e : U,colourWeight label c e*oneMoment a B e) +
      (meanAt B label c)^2

def localScore (a : U→Option Bool) (B : U→Finset U) (label : U→C) : ℚ :=
  ∑ c, conditionalCell a B label c

theorem raw_count_square (B : U→Finset U) (label : U→C) (c : C) (w : U→Bool) :
    (rawCount B label c w)^2 =
      ∑ e : U,∑ e' : U,colourWeight label c e*colourWeight label c e'*
        (rawIndicator B e w*rawIndicator B e' w) := by
  rw [rawCount,pow_two,Finset.sum_mul]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun e _=>Finset.sum_congr rfl (fun e' _=>by ring))

theorem conditional_cell_exact (a : U→Option Bool) (B : U→Finset U) (label : U→C) (c : C) :
    conditionalExpected a (fun w=>(rawCount B label c w-meanAt B label c)^2) =
      conditionalCell a B label c := by
  have in1 : conditionalExpected a (rawCount B label c) =
      ∑ e,colourWeight label c e*oneMoment a B e := by
    unfold rawCount
    rw [expectation_sum]
    simp_rw [expectation_scale,one_moment_exact]
  have in2 : conditionalExpected a (fun w=>(rawCount B label c w)^2) =
      ∑ e : U,∑ e' : U,colourWeight label c e*colourWeight label c e'*twoMoment a B e e' := by
    simp_rw [raw_count_square,expectation_sum,expectation_scale,two_moment_exact]
  have poly (w : U→Bool) : (rawCount B label c w-meanAt B label c)^2 =
      (rawCount B label c w)^2-(2*meanAt B label c)*rawCount B label c w+
        (meanAt B label c)^2 := by ring
  unfold conditionalCell
  simp_rw [poly,expectation_add,expectation_sub,expectation_scale,expectation_const,in1,in2]

theorem local_score_exact (a : U→Option Bool) (B : U→Finset U) (label : U→C) :
    localScore a B label=conditionalExpected a (rawScore B label) := by
  symm
  unfold rawScore localScore
  rw [expectation_sum]
  exact Finset.sum_congr rfl (fun c _=>conditional_cell_exact a B label c)

def pairedCoin : (Outcome U) ≃ ((U→Bool)×(U→Bool)) where
  toFun ω := (fun e=>(ω e).1,fun e=>(ω e).2)
  invFun z := fun e=>(z.1 e,z.2 e)
  left_inv ω := by funext e; exact Prod.eta _
  right_inv _ := rfl

theorem upside_mass (w : U→Bool) :
    markProbability (fun e=>(w e,true))=conditionalMass (fun _=>none) w := by
  unfold markProbability prob conditionalMass
  exact Finset.prod_congr rfl (fun e _=>by norm_num [coinWeight,coinAt])

theorem initial_mark_score_eq (B : U→Finset U) (label : U→C) :
    conditionalExpected (fun _=>none) (rawScore B label) =
      ∑ w : Outcome U, markProbability w * markScore B label w := by
  change _ = ∑ w, (fun z : Outcome U=>markProbability z*markScore B label z) w
  rw [Fintype.sum_equiv pairedCoin _ (fun z=>markProbability (pairedCoin.symm z)*
    markScore B label (pairedCoin.symm z)) (fun x=>
      congrArg (fun y : Outcome U=>markProbability y*markScore B label y)
        ((pairedCoin (U:=U)).symm_apply_apply x).symm), Fintype.sum_prod_type]
  unfold conditionalExpected
  refine Finset.sum_congr rfl fun w _=>?_
  let T : U→Bool := fun _=>true
  rw [Finset.sum_eq_single T]
  · have p : 0<markProbability (fun e=>(w e,true)) := by
      unfold markProbability prob
      exact Finset.prod_pos (fun e _=>by norm_num [coinWeight])
    change _=markProbability (fun e=>(w e,true))*markScore B label (fun e=>(w e,true))
    rw [upside_mass]
    congr 1
    unfold rawScore markScore rawCount countAt
    apply Finset.sum_congr rfl
    intro c _
    congr 2
    refine Finset.sum_congr rfl (fun e _=>?_)
    rw [real_count_for_supported_marks B (fun e=>(w e,true)) p]
    by_cases h : ∀ f∈B e,w f=decide (f=e) <;> simp [rawIndicator,prescribe,required,h]
  · intro z _ ne
    have ex : ∃ e, z e≠true := by
      by_contra! h
      exact ne (funext h)
    obtain ⟨e,ez⟩ := ex
    have z0 : markProbability (pairedCoin.symm (w,z))=0 := by
      unfold markProbability prob
      apply Finset.prod_eq_zero (Finset.mem_univ e)
      change coinWeight 1 (w e,z e)=0
      simp [coinWeight,ez]
    rw [z0,zero_mul]
  · simp

theorem literal_initial_score_bound (B : U→Finset U) (label : U→C) (D : ℕ)
    (self : ∀ e,e∈B e) (symm : ∀ e f,f∈B e→e∈B f) (width : ∀ e,(B e).card≤D) :
    localScore (fun _=>none) B label≤4*(Fintype.card U:ℚ)*(D*D:ℕ) := by
  rw [local_score_exact,initial_mark_score_eq]
  exact score_variance_unified B label D self symm width

#print axioms expectation_sum
#print axioms expectation_scale
#print axioms expectation_const
#print axioms raw_count_square
#print axioms conditional_cell_exact
#print axioms local_score_exact
#print axioms pairedCoin
#print axioms initial_mark_score_eq
#print axioms literal_initial_score_bound
end
end J4R43LiteralOutside

