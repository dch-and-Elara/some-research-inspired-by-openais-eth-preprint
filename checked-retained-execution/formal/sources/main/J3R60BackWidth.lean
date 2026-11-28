import J3R60ActualTrace

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2300000

/-! Bit-sized arithmetic for the actual J3 back substitution. Knowing
that the exact solution consists of bits is a semantic correctness fact
about the input, not a numerical parameter to the solver. -/
namespace J3R60
open J3R59
open scoped BigOperators

theorem sized_add {a b : ℚ} {T S : ℕ} (ha : IntSized T a) (hb : IntSized S b) :
    IntSized (T+S) (a+b) := by
  obtain ⟨n,hn,hn'⟩ := ha
  obtain ⟨m,hm,hm'⟩ := hb
  exact ⟨n+m,by rw [hn,hm,Int.cast_add],
    (Int.natAbs_add_le ..).trans (Nat.add_le_add hn' hm')⟩

theorem sized_sub {a b : ℚ} {T S : ℕ} (ha : IntSized T a) (hb : IntSized S b) :
    IntSized (T+S) (a-b) := by
  obtain ⟨m,hm,hm'⟩ := hb
  rw [sub_eq_add_neg]
  exact sized_add ha ⟨-m, by rw [hm,Int.cast_neg], by simpa using hm'⟩

theorem sized_partial_sum {I : Type*} (a : I → ℚ) (T : ℕ)
    (ha : ∀ i, IntSized T (a i)) (s : Finset I) :
    IntSized (s.card*T) (∑ i ∈ s,a i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.card_empty, zero_mul, Finset.sum_empty]
    exact ⟨0,by simp,by simp⟩
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.card_insert_of_notMem hi, Nat.add_mul, one_mul, add_comm]
    exact sized_add (ha i) ih

theorem sized_mul_bit {a x : ℚ} {T : ℕ} (ha : IntSized T a) (hx : x=0 ∨ x=1) :
    IntSized T (a*x) := by
  rcases hx with rfl|rfl
  · rw [mul_zero]
    exact ⟨0, by simp, Nat.zero_le _⟩
  · simpa only [mul_one] using ha

theorem bit_partial_dot {n : ℕ} (T : ℕ) (a x : Fin n → ℚ)
    (ha : ∀ j, IntSized T (a j)) (hx : ∀ j, x j=0 ∨ x j=1) (s : Finset (Fin n)) :
    IntSized (s.card*T) (∑ j ∈ s, a j*x j) :=
  sized_partial_sum _ _ (fun j => sized_mul_bit (ha j) (hx j)) s

structure BackLocalBound {I : Type*} {n : ℕ} (T : ℕ) (A : I → Fin (n+1) → ℚ)
    (b : I → ℚ) (p : I) (x : Fin n → ℚ) : Prop where
  prefixes : ∀ s : Finset (Fin n), IntSized (s.card*T) (∑ j ∈ s, A p j.succ*x j)
  exactStep : ExactIntegerDivision ((n+1)*T)
    (b p - dot (fun j => A p j.succ) x) (A p 0) (backHead A b p x)
  bit : backHead A b p x = 0 ∨ backHead A b p x = 1

theorem actual_back_local {I : Type*} {n : ℕ} (T : ℕ) (A : I → Fin (n+1) → ℚ)
    (b : I → ℚ) (p : I) {prev : ℚ} (hw : StateBound T A b prev)
    (hp : A p 0 ≠ 0) (x : Fin (n+1) → ℚ)
    (hx : ∀ j, x j=0 ∨ x j=1) (he : dot (A p) x = b p) :
    BackLocalBound T A b p (fun j => x j.succ) := by
  have hw' (s : Finset (Fin n)) :=
    bit_partial_dot T (fun j => A p j.succ) (fun j => x j.succ)
      (fun j => hw.1 p j.succ) (fun j => hx j.succ) s
  have hd : IntSized (n*T) (dot (fun j => A p j.succ) (fun j => x j.succ)) := by
    simpa [dot] using hw' Finset.univ
  have hn : IntSized ((n+1)*T) (b p - dot (fun j => A p j.succ) (fun j => x j.succ)) := by
    rw [Nat.add_mul, one_mul, add_comm]
    exact sized_sub (hw.2.1 p) hd
  have hback := head_exact A b p x he hp
  have hbit : backHead A b p (fun j => x j.succ)=0 ∨
      backHead A b p (fun j => x j.succ)=1 := by rw [hback]; exact hx 0
  refine ⟨hw',?_,hbit⟩
  obtain ⟨q,hq,hq'⟩ := hn
  obtain ⟨d,hd',_⟩ := hw.1 p 0
  have hi : IntSized 1 (backHead A b p (fun j => x j.succ)) := by
    rcases hbit with h|h
    · exact ⟨0,by simpa using h,by decide⟩
    · exact ⟨1,by simpa using h,by decide⟩
  obtain ⟨z,hz,_⟩ := hi
  refine ⟨q,d,z,hq,hd',hz,hq',?_,?_⟩
  · intro hz
    exact hp (by rw [hd',hz]; rfl)
  · have hz' := hz
    unfold backHead at hz'
    have hc := (div_eq_iff hp).mp hz'
    rw [hq,hd'] at hc
    exact mul_comm d z ▸ (by exact_mod_cast hc : q = z*d)

/-- Back operations use the same first-pivot branches as the original
solver. The proof's bit word is not used to select pivots or compute values. -/
def BackBound {I : Type*} (rows : List I) (T : ℕ) :
    (n : ℕ) → (I → Fin n → ℚ) → (I → ℚ) → ℚ → (Fin n → ℚ) → Prop
  | 0, _, _, _, _ => True
  | n+1, A, b, prev, x =>
    match rows.find? (fun r => decide (A r 0 ≠ 0)) with
    | none => False
    | some p => BackLocalBound T A b p (fun j => x j.succ) ∧
      BackBound rows T n (tailMatrix A p prev) (tailRhs A b p prev) (A p 0)
        (fun j => x j.succ)

theorem true_bit_back_width {I : Type*} (rows : List I) (all : ∀ r, r∈rows)
    (T n : ℕ) (A : I → Fin n → ℚ) (b : I → ℚ) (prev : ℚ)
    (hp : prev ≠ 0) (hi : ∀ y : Fin n → ℚ, (∀ r, dot (A r) y=0) → y=0)
    (x : Fin n → ℚ) (hx : ∀ j, x j=0 ∨ x j=1) (he : ∀ r, dot (A r) x=b r)
    (fw : ForwardBound rows T n A b prev) :
    BackBound rows T n A b prev x := by
  induction n generalizing b prev with
  | zero => exact True.intro
  | succ n ih =>
    rw [ForwardBound] at fw
    obtain ⟨hw, htail⟩ := fw
    rw [BackBound]
    cases hs : rows.find? (fun r => decide (A r 0 ≠ 0)) with
    | none =>
      have h := fractionFree_exact rows all (n+1) A b prev hp hi x he
      rw [fractionFree,hs] at h
      exact Option.noConfusion h
    | some p =>
      have hp' : (fun r : I => decide (A r 0 ≠ 0)) p = true :=
        List.find?_some (p := fun r : I => decide (A r 0 ≠ 0)) (a := p) hs
      have hp0 : A p 0 ≠ 0 := of_decide_eq_true hp'
      rw [hs] at htail
      refine ⟨actual_back_local T A b p hw hp0 x hx (he p),?_⟩
      exact ih (tailMatrix A p prev) (tailRhs A b p prev) (A p 0) hp0
        (tail_zero_injective A p prev hp0 hp hi) (fun j => x j.succ)
        (fun j => hx j.succ) (tail_exact A b p prev x he) htail.2

#print axioms bit_partial_dot
#print axioms actual_back_local
#print axioms true_bit_back_width

end J3R60
