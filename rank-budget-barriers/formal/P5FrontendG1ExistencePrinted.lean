import P5FrontendG1ExistenceLocal
import P5FrontendG1ExistenceWalsh

/-! Instantiate the exact finite Walsh and local-code bounds in the original
printed dimensions. The proof yields valid witnesses, not an operational
bit-cost bound for enumerating them. -/
namespace Paper5.FrontendG1.Tanner
open scoped BigOperators
open Real

abbrev SourceShifts (B m : ℕ) := Fin (sourceDegree B m)→Word (sourceEll B m)

noncomputable def biasEpsilon (B m : ℕ) : ℝ := 1/(biasDenom B m:ℝ)

theorem bias_denom_pos {B m : ℕ} (hB : 0<B) : 0<biasDenom B m := by
  unfold biasDenom sourceMu
  positivity

theorem source_eps_positive {B m : ℕ} (hB : 0<B) : 0<biasEpsilon B m := by
  have hd := bias_denom_pos (m:=m) hB
  unfold biasEpsilon
  positivity

theorem source_eps_exponent_exact {B m : ℕ} (hB : 0<B) (hm : 0<m)
    (hq : 1<sourceQ B m) :
    (biasEpsilon B m)^2*(sourceDegree B m:ℝ)/2=4*(sourceMu m:ℝ) := by
  have hBr : (B:ℝ)≠0 := by exact_mod_cast hB.ne'
  have hMu : (sourceMu m:ℝ)≠0 := by
    exact_mod_cast (show sourceMu m≠0 by unfold sourceMu; omega)
  rw [source_d_eq_D_of_q_gt_one hB hm hq,biasEpsilon,biasDenom,sourceD]
  push_cast
  field_simp
  ring

theorem source_q_below_binary_lift {B m : ℕ} (hB : 0<B) (hm : 0<m) :
    sourceQ B m<2^(sourceMu m+1) := by
  have hD := source_d_pos hB hm
  have hlog : m<2^(sourceMu m) := Nat.lt_pow_succ_log_self (by decide) m
  calc
    _ = sourceQ B m*1 := (Nat.mul_one _).symm
    _ ≤ sourceQ B m*sourceDegree B m :=
      Nat.mul_le_mul_left _ (Nat.one_le_of_lt hD)
    _ < 2*m := source_q_slots_lt_twice hB hm
    _ < 2*2^(sourceMu m) := Nat.mul_lt_mul_of_pos_left hlog (by decide)
    _ = _ := by rw [pow_succ']

theorem source_walsh_union_factor_lt_one {B m : ℕ} (hB : 0<B) (hm : 0<m) :
    2*(sourceQ B m:ℝ)*exp (-(4*(sourceMu m:ℝ)))<1 := by
  let u := sourceMu m
  have hu : 1≤u := by change 1≤Nat.log 2 m+1; omega
  have hp : 2*sourceQ B m<2^(4*u) := by
    calc
      _ < 2*2^(u+1) := Nat.mul_lt_mul_of_pos_left (source_q_below_binary_lift hB hm) (by decide)
      _ = 2^(u+2) := (pow_succ' (2:ℕ) (u+1)).symm
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  have hTwo : (2:ℝ)<exp 1 := by
    have hh := Real.add_one_lt_exp (by norm_num : (1:ℝ)≠0)
    norm_num at hh
    exact hh
  have hReal : 2*(sourceQ B m:ℝ)<exp (4*(u:ℝ)) := by
    calc
      _ < (2:ℝ)^(4*u) := by exact_mod_cast hp
      _ < (exp (1:ℝ))^(4*u) := pow_lt_pow_left₀ hTwo (by norm_num) (by omega)
      _ = _ := by rw [←Real.exp_nat_mul]; push_cast; ring_nf
  change 2*(sourceQ B m:ℝ)*exp (-(4*(u:ℝ)))<1
  rw [Real.exp_neg,←div_eq_mul_inv,div_lt_iff₀ (Real.exp_pos _),one_mul]
  exact hReal

def badAtCharacter (B m : ℕ) (b : Word (sourceEll B m)) : Finset (SourceShifts B m) :=
  Finset.univ.filter fun s =>
    sourceDegree B m<(sourceWalsh s b).natAbs*biasDenom B m

theorem badAtCharacter_exact {B m : ℕ} (hB : 0<B) (b : Word (sourceEll B m)) :
    badAtCharacter B m b=badAbsTail (sourceDegree B m) b (biasEpsilon B m) := by
  classical
  have hd : (0:ℝ)<biasDenom B m := by exact_mod_cast bias_denom_pos (m:=m) hB
  ext s
  simp only [badAtCharacter,badAbsTail,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [biasEpsilon,one_div_mul_eq_div,div_lt_iff₀ hd,←sourceAbsWalsh_eq_real]
  exact_mod_cast Iff.rfl

theorem actual_bad_character_count {B m : ℕ} (hB : 0<B) (hm : 0<m)
    (hq : 1<sourceQ B m) (b : Word (sourceEll B m)) (hb : b≠0) :
    ((badAtCharacter B m b).card:ℝ) ≤
      2*(Fintype.card (SourceShifts B m):ℝ)*exp (-(4*(sourceMu m:ℝ))) := by
  rw [badAtCharacter_exact hB]
  have h := bad_abs_tail_bound (d:=sourceDegree B m) b hb (biasEpsilon B m)
    (source_eps_positive (m:=m) hB).le
  rw [source_eps_exponent_exact hB hm hq] at h
  exact h

theorem source_valid_shift_tuple_exists {B m : ℕ} (hB : 0<B) (hm : 0<m) :
    ∃ s : SourceShifts B m,biasViolations B m s=∅ := by
  classical
  by_cases hq : sourceQ B m=1
  · exact ⟨fun _=>0,q_one_has_no_bias_test hq _⟩
  have hq0 : 0<sourceQ B m := by unfold sourceQ; positivity
  have hq1 : 1<sourceQ B m := by omega
  let C : Finset (Word (sourceEll B m)) := Finset.univ.filter fun b=>b≠0
  let U : Finset (SourceShifts B m) := C.biUnion (badAtCharacter B m)
  let T := Fintype.card (SourceShifts B m)
  let X := exp (-(4*(sourceMu m:ℝ)))
  have hT : 0<(T:ℝ) := by exact_mod_cast (show 0<T from Fintype.card_pos)
  have hC : (C.card:ℝ)≤(sourceQ B m:ℝ) := by
    have h := Finset.card_filter_le (Finset.univ : Finset (Word (sourceEll B m))) (fun b=>b≠0)
    have hf : Fintype.card (Word (sourceEll B m))=sourceQ B m := by
      simp [Word,F₂,sourceQ]
    rw [Finset.card_univ,hf] at h
    exact_mod_cast h
  have hUreal : (U.card:ℝ)<(T:ℝ) := by
    calc
      _ ≤ ∑ b∈C,((badAtCharacter B m b).card:ℝ) := by
        have hh : U.card≤∑ b∈C,(badAtCharacter B m b).card := Finset.card_biUnion_le
        exact_mod_cast hh
      _ ≤ ∑ _b∈C,2*(T:ℝ)*X := by
        exact Finset.sum_le_sum fun b hb=> actual_bad_character_count hB hm hq1 b
          (Finset.mem_filter.mp hb).2
      _ = (C.card:ℝ)*(2*(T:ℝ)*X) := by simp [nsmul_eq_mul]
      _ ≤ (sourceQ B m:ℝ)*(2*(T:ℝ)*X) := by
        apply mul_le_mul_of_nonneg_right hC
        dsimp [X]
        positivity
      _ = (2*(sourceQ B m:ℝ)*X)*(T:ℝ) := by ring
      _ < _ := by
        simpa only [one_mul] using
          (mul_lt_mul_of_pos_right (source_walsh_union_factor_lt_one hB hm) hT)
  have hU : U.card<T := by exact_mod_cast hUreal
  have hExists : ∃ s : SourceShifts B m,s∉U := by
    by_contra! he
    have hs : (Finset.univ : Finset (SourceShifts B m))⊆U := fun a _=>he a
    have hh := Finset.card_le_card hs
    rw [Finset.card_univ] at hh
    exact (not_le_of_gt hU) hh
  obtain ⟨s,hs⟩ := hExists
  refine ⟨s,Finset.eq_empty_iff_forall_notMem.mpr ?_⟩
  intro b hbad
  obtain ⟨_,hn,hl⟩ := Finset.mem_filter.mp hbad
  exact hs (Finset.mem_biUnion.mpr ⟨b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl⟩⟩)

theorem actual_printed_input_exists {C : Type*} [Fintype C] {B : ℕ}
    (hB : 0<B) (hm : 0<Fintype.card C) :
    ∃ P : PrintedInput C B, SourceBias B (Fintype.card C) P.shifts := by
  obtain ⟨s,hs⟩ := source_valid_shift_tuple_exists hB hm
  obtain ⟨A,hA⟩ := source_local_matrix_exists hB hm
  obtain ⟨keep⟩ := printed_kept_columns_exist C B hB hm
  exact ⟨checkedInput s A keep hA,(biasViolations_empty_exact hB s).mp hs⟩

#print axioms bias_denom_pos
#print axioms source_eps_positive
#print axioms source_eps_exponent_exact
#print axioms source_q_below_binary_lift
#print axioms source_walsh_union_factor_lt_one
#print axioms badAtCharacter_exact
#print axioms actual_bad_character_count
#print axioms source_valid_shift_tuple_exists
#print axioms actual_printed_input_exists
end Paper5.FrontendG1.Tanner