import J4R43LiteralOutsideVariance

/-! Exact conditional product law for the same fair edge marks.
There is no conditioning on a partition other than the actual
already written Boolean coordinates. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5000000

variable {U : Type*} [Fintype U] [DecidableEq U]

def coinAt (a : Option Bool) (b : Bool) : ℚ :=
  match a with
  | none => 1/2
  | some u => if b=u then 1 else 0

theorem coinAt_mass (a : Option Bool) : ∑ b : Bool,coinAt a b=1 := by
  cases a with
  | none => norm_num [Fintype.sum_bool,coinAt]
  | some b => cases b <;> norm_num [Fintype.sum_bool,coinAt]

def conditionalMass (a : U→Option Bool) (w : U→Bool) : ℚ :=
  ∏ i,coinAt (a i) (w i)

def conditionalExpected (a : U→Option Bool) (f : (U→Bool)→ℚ) : ℚ :=
  ∑ w : U→Bool,conditionalMass a w*f w

theorem conditional_mass_total (a : U→Option Bool) :
    (∑ w : U→Bool,conditionalMass a w)=1 := by
  unfold conditionalMass
  rw [←Fintype.prod_sum (fun i b=>coinAt (a i) b)]
  simp only [coinAt_mass,Finset.prod_const_one]

theorem conditional_expected_mult (a : U→Option Bool) (f : U→Bool→ℚ) :
    conditionalExpected a (fun w=>∏ i,f i (w i)) =
      ∏ i,∑ b : Bool,coinAt (a i) b*f i b := by
  unfold conditionalExpected conditionalMass
  simp only [←Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i b=>coinAt (a i) b*f i b)).symm

def prescribe (S : Finset U) (pattern w : U→Bool) : Prop :=
  ∀ i∈S,w i=pattern i

def localMass (a : U→Option Bool) (S : Finset U) (pattern : U→Bool) : ℚ :=
  ∏ i∈S,coinAt (a i) (pattern i)

theorem conditional_pattern_exact (a : U→Option Bool) (S : Finset U) (pattern : U→Bool) :
    conditionalExpected a (fun w=>if prescribe S pattern w then 1 else 0) =
      localMass a S pattern := by
  let f (i : U) (b : Bool) : ℚ := if i∈S then (if b=pattern i then 1 else 0) else 1
  have e (w : U→Bool) : (if prescribe S pattern w then (1:ℚ) else 0)=∏ i,f i (w i) := by
    by_cases h : prescribe S pattern w
    · rw [if_pos h]
      symm
      refine Finset.prod_eq_one fun i _=>?_
      by_cases hi : i∈S
      · simp [f,hi,h i hi]
      · simp [f,hi]
    · rw [if_neg h]
      simp only [prescribe, not_forall] at h
      obtain ⟨i,hS,hneq⟩ := h
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [f,hS,hneq])
  simp_rw [e]
  rw [conditional_expected_mult]
  unfold localMass
  trans (∏ i : U,if i∈S then coinAt (a i) (pattern i) else 1)
  swap
  · rw [←Finset.prod_filter,Finset.filter_univ_mem]
  refine Finset.prod_congr rfl fun i _=>?_
  by_cases hi : i∈S
  · rw [if_pos hi]
    simp only [f,if_pos hi]
    rw [Finset.sum_eq_single (pattern i)]
    · simp
    · intro j _ h
      simp [h]
    · simp
  · simp only [f,if_neg hi,mul_one,coinAt_mass]

theorem set_coordinate_mass (a : U→Option Bool) (i : U) (v : Bool) (w : U→Bool) :
    conditionalMass (Function.update a i (some v)) w =
      coinAt (some v) (w i)*(∏ j∈Finset.univ.erase i,coinAt (a j) (w j)) := by
  unfold conditionalMass
  rw [←Finset.mul_prod_erase (s:=Finset.univ) _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun j hj=>?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

theorem conditional_split (a : U→Option Bool) (i : U) (fresh : a i=none)
    (score : (U→Bool)→ℚ) :
    conditionalExpected a score =
      (conditionalExpected (Function.update a i (some false)) score+
        conditionalExpected (Function.update a i (some true)) score)/2 := by
  have h (w : U→Bool) : conditionalMass a w =
      (conditionalMass (Function.update a i (some false)) w+
        conditionalMass (Function.update a i (some true)) w)/2 := by
    rw [set_coordinate_mass,set_coordinate_mass]
    unfold conditionalMass
    rw [←Finset.mul_prod_erase (s:=Finset.univ) _ (Finset.mem_univ i),fresh]
    cases q : w i <;> simp [coinAt,q] <;> ring
  simp only [conditionalExpected,h,add_mul,div_mul_eq_mul_div]
  rw [←Finset.sum_div,Finset.sum_add_distrib]

theorem conditional_full_exact (word : U→Bool) (s : (U→Bool)→ℚ) :
    conditionalExpected (fun i=>some (word i)) s=s word := by
  have actual (w : U→Bool) : conditionalMass (fun i=>some (word i)) w =
      if w=word then 1 else 0 := by
    unfold conditionalMass
    by_cases eq : w=word
    · subst w
      simp [coinAt]
    · rw [if_neg eq]
      have witness : ∃ i,w i≠word i := by
        by_contra! h
        exact eq (funext h)
      obtain ⟨i,h⟩ := witness
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [coinAt,h])
  simp only [conditionalExpected,actual]
  rw [Finset.sum_eq_single word]
  · simp
  · intro w _ h
    simp [h]
  · simp

#print axioms coinAt_mass
#print axioms conditional_mass_total
#print axioms conditional_expected_mult
#print axioms conditional_pattern_exact
#print axioms set_coordinate_mass
#print axioms conditional_split
#print axioms conditional_full_exact
end
end J4R43LiteralOutside

