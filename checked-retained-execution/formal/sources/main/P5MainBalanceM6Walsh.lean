import P5MainIteratorMeasure

/-! The full rational printed swap character basis, including every
copy/orbit, gives a canonical dual. Unlike the §6 lower bound this
argument needs completeness, not only an orthonormal subframe. -/
namespace P5MainBalance.M6
open P5MainIterator
open scoped BigOperators Classical

variable {O : Type*} (A : O→Type*) [Fintype O] [∀ o,Fintype (A o)]

theorem qWalsh_symm {J : Type*} [Fintype J] (a b : J→Bool) :
    qWalsh a b=qWalsh b a := by
  unfold qWalsh
  simp_rw [Bool.and_comm]

theorem qWalsh_dot {J : Type*} [Fintype J] (a b : J→Bool) :
    (∑ w, qWalsh a w*qWalsh b w)=if a=b then (2:ℚ)^Fintype.card J else 0 := by
  apply Rat.cast_injective (α:=ℝ)
  by_cases h : a=b
  · rw [if_pos h]; push_cast
    simpa only [cast_qWalsh,if_pos h] using walsh_orthogonal a b
  · rw [if_neg h]; push_cast
    simpa only [cast_qWalsh,if_neg h] using walsh_orthogonal a b

omit [Fintype O] in
theorem qOrbitRow_symm (r s : OrbitSlots A) :
    qOrbitRow A r s=qOrbitRow A s r := by
  rcases r with ⟨o,a⟩
  rcases s with ⟨p,b⟩
  by_cases h : o=p
  · subst p
    simpa only [qOrbitRow,dif_pos rfl] using qWalsh_symm a b
  · simp [qOrbitRow,h,Ne.symm h]

noncomputable def qNorm (r : OrbitSlots A) : ℚ := (2:ℚ)^Fintype.card (A r.1)

omit [Fintype O] in
theorem qNorm_pos (r : OrbitSlots A) : 0<qNorm A r := by unfold qNorm; positivity

set_option maxHeartbeats 8200000 in
theorem qOrbitRows_dot (r s : OrbitSlots A) :
    (∑ x,qOrbitRow A r x*qOrbitRow A s x)=if r=s then qNorm A r else 0 := by
  rcases r with ⟨o,a⟩
  rcases s with ⟨p,b⟩
  rw [Fintype.sum_sigma]
  by_cases h : o=p
  · subst p
    rw [Finset.sum_eq_single o]
    · simpa only [qOrbitRow,dif_pos rfl,Sigma.mk.injEq,heq_eq_eq,and_true,true_and,qNorm] using
        qWalsh_dot a b
    · intro q _ hq
      apply Finset.sum_eq_zero
      intro x _
      simp [qOrbitRow,Ne.symm hq]
    · simp
  · rw [if_neg (fun h' => h (congrArg Sigma.fst h'))]
    apply Finset.sum_eq_zero
    intro q _
    apply Finset.sum_eq_zero
    intro x _
    by_cases hq : o=q
    · subst q
      simp [qOrbitRow,Ne.symm h]
    · simp [qOrbitRow,hq]

theorem qOrbit_dual (r s : OrbitSlots A) :
    (∑ x,qOrbitRow A x r*qOrbitRow A x s/qNorm A x)=if r=s then 1 else 0 := by
  simp_rw [fun x=>qOrbitRow_symm A x r,fun x=>qOrbitRow_symm A x s]
  have h : (∑ x,qOrbitRow A r x*qOrbitRow A s x/qNorm A x)=
      ∑ x,qOrbitRow A r x*qOrbitRow A s x/qNorm A r := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : r.1=x.1
    · rw [show qNorm A x=qNorm A r by simp only [qNorm,←h]]
    · simp [qOrbitRow,h]
  rw [h,←Finset.sum_div,qOrbitRows_dot]
  by_cases h : r=s <;> simp [h,(qNorm_pos A _).ne']

noncomputable def qRead (ζ : OrbitSlots A→ℚ) (r : OrbitSlots A) : ℚ :=
  ∑ x,qOrbitRow A r x*ζ x

theorem qRead_recover (ζ : OrbitSlots A→ℚ) :
    (∑ r, (qRead A ζ r/qNorm A r) • qOrbitRow A r)=ζ := by
  funext x
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  unfold qRead
  simp only [Finset.sum_div,Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    _ = ∑ s,(∑ r,qOrbitRow A r x*qOrbitRow A r s/qNorm A r)*ζ s := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun r _=>by ring)
    _ = _ := by
      simp_rw [qOrbit_dual,ite_mul,one_mul,zero_mul]
      simp

/-- A concrete operator which fixes every retained-weight swap basis vector
fixes the kernel of exactly the measured exceptional rows. -/
theorem fixes_raw_kernel (keep : ℕ→Prop)
    (M : Matrix (OrbitSlots A) (OrbitSlots A) ℚ)
    (hEigen : ∀ r : OrbitSlots A, ¬keep (boolWeight r.2) →
        M.mulVec (qOrbitRow A r)=qOrbitRow A r)
    (ζ : OrbitSlots A→ℚ) (hζ : (rawRows A keep).mulVec ζ=0) :
    M.mulVec ζ=ζ := by
  have hz (r : OrbitSlots A) (hr : keep (boolWeight r.2)) : qRead A ζ r=0 := by
    exact congrFun hζ ⟨r,hr⟩
  calc
    _ = M.mulVec (∑ r, (qRead A ζ r/qNorm A r) • qOrbitRow A r) := by rw [qRead_recover]
    _ = ∑ r, (qRead A ζ r/qNorm A r) • qOrbitRow A r := by
      rw [Matrix.mulVec_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [Matrix.mulVec_smul]
      by_cases h : keep (boolWeight r.2)
      · simp [hz r h]
      · rw [hEigen r h]
    _ = _ := qRead_recover A ζ

#print axioms qWalsh_dot
#print axioms qOrbitRow_symm
#print axioms qOrbitRows_dot
#print axioms qOrbit_dual
#print axioms qRead_recover
#print axioms fixes_raw_kernel
end P5MainBalance.M6
