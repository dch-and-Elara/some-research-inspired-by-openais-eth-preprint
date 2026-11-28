import V8CapacitySpecialFrobenius

/-! Sharp residues for J6: choose only the lowest jet digit everywhere,
and turn on one higher digit in the witness row when its exponent is
nonzero in the residue field. -/
namespace V8CapacitySpecialResidueJet
open scoped Polynomial Classical BigOperators
open Polynomial V8CapacityFeatures V8CapacitySymbolic V8CapacitySpecialFrobenius

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {K H : Type*} [Field K] [Fintype H] {k : ℕ}

def testDigit (i : H) (t : ℕ) (a : Digits H k) : K :=
  if a.2.val=1 then 1 else if a.1=i ∧ a.2.val=t+1 then 1 else 0

theorem shift_lowest (i e : H) (h : 1<k) :
    shiftedPolynomial (0:K) k (asInput (testDigit (k:=k) i 0) e)=(X:K[X]) := by
  unfold shiftedPolynomial
  rw [zero_mul,map_zero,zero_add]
  have hsum : (∑ r ∈ Finset.range (k-1), C (asInput (testDigit (k:=k) i 0) e (r+1))*X^r : K[X])=1 := by
    rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega))]
    · simp [asInput,testDigit,h]
    · intro r hr h0
      have hh : r+1<k := by have := Finset.mem_range.mp hr; omega
      simp [asInput,testDigit,hh,h0]
  rw [hsum,mul_one]

theorem shift_one_extra (i e : H) (t : ℕ) (ht : 0<t) (h : t+1<k) :
    shiftedPolynomial (0:K) k (asInput (testDigit (k:=k) i t) e)=
      (X:K[X])*(if e=i then (1+X^t) else 1) := by
  unfold shiftedPolynomial
  rw [zero_mul,map_zero,zero_add]
  congr 1
  have H0 : 0∈Finset.range (k-1) := Finset.mem_range.mpr (by omega)
  have HT : t∈Finset.range (k-1) := Finset.mem_range.mpr (by omega)
  have hf (r : ℕ) (hr : r∈Finset.range (k-1)) :
      asInput (testDigit (k:=k) (K:=K) i t) e (r+1)=
        (if r=0 then 1 else 0)+(if e=i ∧ r=t then 1 else 0) := by
    have hi : r+1<k := by have := Finset.mem_range.mp hr; omega
    simp only [asInput,dif_pos hi,testDigit,Nat.succ.injEq]
    by_cases hz : r=0
    · simp [hz,Ne.symm (Nat.ne_of_gt ht)]
    · simp [hz]
  calc
    (∑ r ∈ Finset.range (k-1), C (asInput (testDigit (k:=k) i t) e (r+1))*X^r : K[X]) =
        (∑ r ∈ Finset.range (k-1), C (if r=0 then (1:K) else 0)*X^r)+
          ∑ r ∈ Finset.range (k-1), C (if e=i ∧ r=t then (1:K) else 0)*X^r := by
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r hr
      rw [hf r hr,map_add,add_mul]
    _ = if e=i then (1+X^t) else 1 := by
      rw [Finset.sum_eq_single_of_mem 0 H0 (fun r _ hr => by simp [hr])]
      by_cases he : e=i
      · rw [Finset.sum_eq_single_of_mem t HT (fun r _ hr => by simp [hr])]
        simp [he]
      · simp [he]

theorem lowest_nonzero (β : H → ℕ) (i : H) (h : 1<k) :
    feature (0:K) k β (∑ e : H,β e)≠0 := by
  intro hz
  have hv := feature_eval (0:K) k β (∑ e : H,β e) (testDigit (k:=k) i 0)
  rw [hz,map_zero] at hv
  unfold rawFeature at hv
  simp_rw [shift_lowest i _ h,Finset.prod_pow_eq_pow_sum,coeff_X_pow_self] at hv
  exact zero_ne_one hv

theorem one_higher_coefficient (n t : ℕ) (hn : 0<n) (ht : 0<t) :
    (((1:K[X])+X^t)^n).coeff t=(n:K) := by
  rw [add_comm,add_pow,finset_sum_coeff]
  have hterm (j : ℕ) :
      (((X:K[X])^t)^j*1^(n-j)*(n.choose j)).coeff t =
        if t=t*j then ↑(n.choose j) else 0 := by
    rw [one_pow,mul_one,← pow_mul,mul_comm,← map_natCast (C : K →+* K[X]),coeff_C_mul_X_pow]
  simp_rw [hterm]
  rw [Finset.sum_eq_single_of_mem 1 (Finset.mem_range.mpr (by omega))]
  · simp
  · intro j _ hj
    have h : t≠t*j := by
      intro h'
      apply hj
      exact (Nat.eq_of_mul_eq_mul_left ht (by simpa using h'.symm))
    rw [if_neg h]

theorem one_higher_nonzero (β : H → ℕ) (i : H) (t : ℕ) (ht : 0<t)
    (hb : (β i:K)≠0) (hk : (∑ e : H,β e)+t<k) :
    feature (0:K) k β ((∑ e : H,β e)+t)≠0 := by
  have hn : 0<β i := Nat.pos_of_ne_zero (fun h => hb (by simp [h]))
  have hsum : β i ≤∑ e : H, β e :=
    Finset.single_le_sum (f:=β) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hkt : t+1<k := by omega
  intro hz
  have hv := feature_eval (0:K) k β ((∑ e : H,β e)+t) (testDigit (k:=k) i t)
  rw [hz,map_zero] at hv
  unfold rawFeature at hv
  simp_rw [shift_one_extra i _ t ht hkt,mul_pow,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum] at hv
  rw [Finset.prod_eq_single_of_mem i (Finset.mem_univ _) (fun x _ hx => by simp [hx])] at hv
  simp only [if_true] at hv
  rw [coeff_X_pow_mul',if_pos (Nat.le_add_right _ _),Nat.add_sub_cancel_left,
    one_higher_coefficient (β i) t hn ht] at hv
  exact hb hv.symm

variable {c : ℕ} [ExpChar (MvPolynomial (Digits H k) K) c]

/-- Exact support test for any valid common Frobenius decomposition.
Taking the maximal common c-power gives precisely the J6 support
criterion for every nonzero alpha. -/
theorem frobenius_support_exact (hc : 0<c) (s : ℕ) (α β : H → ℕ)
    (same : ∀ e, α e=c^s*β e) (i : H) (hn : (β i:K)≠0)
    (j : ℕ) (hj : j<k) :
    feature (0:K) k α j≠0 ↔ ∃ t : ℕ, j=(∑ e : H, α e)+c^s*t := by
  constructor
  · exact only_frobenius_offsets hc s α β same j
  · rintro ⟨t,ht⟩
    have hsum : (∑ e : H,α e)=c^s*(∑ e : H,β e) := by simp_rw [same,Finset.mul_sum]
    have hJ : j=c^s*((∑ e : H, β e)+t) := by rw [ht,hsum,mul_add]
    have hd : 0<c^s := pow_pos hc s
    have dJ : c^s∣j := ⟨_,hJ⟩
    have nJ : j/c^s=(∑ e : H,β e)+t := by rw [hJ,Nat.mul_div_cancel_left _ hd]
    have hb : (∑ e : H,β e)+t<k := by
      apply lt_of_le_of_lt _ hj
      rw [hJ]
      conv_lhs => rw [← one_mul ((∑ e : H,β e)+t)]
      exact Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hd)
    rw [feature_of_scaled_exponents hc s α β same,if_pos dJ,nJ]
    apply pow_ne_zero _
    by_cases h0 : t=0
    · subst t
      rw [add_zero]
      have hpos : 0<β i := Nat.pos_of_ne_zero (fun he => hn (by simp [he]))
      have hh : β i ≤∑ e : H, β e :=
        Finset.single_le_sum (f:=β) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      exact lowest_nonzero β i (by omega)
    · exact one_higher_nonzero β i t (Nat.pos_of_ne_zero h0) hn hb

#print axioms shift_lowest
#print axioms shift_one_extra
#print axioms lowest_nonzero
#print axioms one_higher_coefficient
#print axioms one_higher_nonzero
#print axioms frobenius_support_exact
end
end V8CapacitySpecialResidueJet

