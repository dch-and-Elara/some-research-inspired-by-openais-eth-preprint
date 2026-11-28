import JointContraction

/-! J4–J5: the finite dense streaming moment table, not merely a support bound. -/
namespace J45Cost
open scoped BigOperators Classical

abbrev Box {D : Type*} (H : D → ℕ) := ∀ d, Fin (H d + 1)

variable {D : Type*} (H : D → ℕ)

def intIndex (x : Box H) : D → ℤ := fun d => (x d).val

def zeroIndex : Box H := fun _ => ⟨0,Nat.zero_lt_succ _⟩

theorem intIndex_injective : Function.Injective (intIndex H) := by
  intro x y h
  funext d
  apply Fin.ext
  have hx := congrFun h d
  change ((x d).val : ℤ) = ((y d).val : ℤ) at hx
  exact_mod_cast hx

section DP

variable {R V : Type*} [CommSemiring R] [DecidableEq V] {U : V → Type*}
  [∀ v, Fintype (U v)]

/-- A guarded read into the previous array. Nonnegative increments mean a
missing predecessor really is out of the reachable region, not an alias. -/
noncomputable def predecessor (prev : Box H → R) (x : Box H) (inc : D → ℕ) : R := by
  classical
  exact if h : ∀ d, inc d ≤ (x d).val then
    prev (fun d => ⟨(x d).val - inc d, by have hu := (x d).isLt; omega⟩)
  else 0

/-- One dense gather sweep; the next array never overwrites the previous one. -/
noncomputable def dpStep (v : V) (w : ∀ v, U v → R) (inc : ∀ v, U v → D → ℕ)
    (prev : Box H → R) : Box H → R :=
  fun x => ∑ z : U v, w v z * predecessor H prev x (inc v z)

/-- Each vertex is processed once, from the tail to the head of the list. -/
noncomputable def dpRun (w : ∀ v, U v → R) (inc : ∀ v, U v → D → ℕ) : List V → Box H → R
  | [] => fun x => if x=zeroIndex H then 1 else 0
  | v::qs => dpStep H v w inc (dpRun w inc qs)

abbrev intInc (inc : ∀ v, U v → D → ℕ) (v : V) (z : U v) : D → ℤ :=
  fun d => inc v z d

/-- Appending nonnegative feature increments cannot make a negative index
reachable. This is why finite arrays may ignore such predecessors. -/
theorem distribution_negative (s : Finset V) (w : ∀ v, U v → R) (inc : ∀ v, U v → D → ℕ)
    (d : D) (j : D → ℤ) (hj : j d < 0) :
    JointContraction.distribution s w (intInc inc) j = 0 := by
  classical
  induction s using Finset.induction_on generalizing j with
  | empty =>
    rw [JointContraction.distribution_empty]
    have hne : (0 : D → ℤ) ≠ j := by
      intro e
      have h := congrFun e d
      change 0 = j d at h
      omega
    simp [AddMonoidAlgebra.one_def, hne]
  | insert v s hv ih =>
    rw [JointContraction.distribution_insert_entry v s hv]
    apply Finset.sum_eq_zero
    intro z _
    have hn : (j-intInc inc v z) d < 0 := by
      change j d - (inc v z d : ℤ) < 0
      omega
    rw [ih _ hn,mul_zero]

theorem gather_step_exact (v : V) (s : Finset V) (hv : v ∉ s)
    (w : ∀ v, U v → R) (inc : ∀ v, U v → D → ℕ) (x : Box H) :
    dpStep H v w inc (fun old => JointContraction.distribution s w (intInc inc) (intIndex H old)) x =
      JointContraction.distribution (insert v s) w (intInc inc) (intIndex H x) := by
  classical
  rw [dpStep,JointContraction.distribution_insert_entry v s hv]
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  unfold predecessor
  split_ifs with h
  · apply congrArg (fun j => JointContraction.distribution s w (intInc inc) j)
    funext d
    change (((x d).val - inc v z d : ℕ) : ℤ) = (x d).val - (inc v z d : ℤ)
    exact Int.ofNat_sub (h d)
  · push_neg at h
    obtain ⟨d,hd⟩ := h
    symm
    apply distribution_negative s w inc d
    change ((x d).val : ℤ) - (inc v z d : ℤ) < 0
    omega

theorem dpRun_exact (s : List V) (nodup : s.Nodup) (w : ∀ v, U v → R)
    (inc : ∀ v, U v → D → ℕ) (x : Box H) :
    dpRun H w inc s x = JointContraction.distribution s.toFinset w (intInc inc) (intIndex H x) := by
  classical
  induction s generalizing x with
  | nil =>
    rw [dpRun,List.toFinset_nil,JointContraction.distribution_empty]
    by_cases h : x=zeroIndex H
    · subst x
      have hz : intIndex H (zeroIndex H) = (0 : D → ℤ) := rfl
      simp [AddMonoidAlgebra.one_def, hz]
    · have hn : (0 : D → ℤ) ≠ intIndex H x := by
        intro hh
        exact h ((intIndex_injective H) (hh.symm.trans rfl))
      simp [h,AddMonoidAlgebra.one_def,hn]
  | cons v s ih =>
    rw [List.nodup_cons] at nodup
    rw [dpRun,List.toFinset_cons,← gather_step_exact H v s.toFinset (by simpa using nodup.1)]
    congr 1
    funext y
    exact ih nodup.2 y

end DP

section FullReadout

variable {V R : Type*} [Fintype V] [DecidableEq V] [Fintype D] [CommSemiring R]
  {U : V → Type*} [∀ v,Fintype (U v)]

theorem box_card : Fintype.card (Box H) = ∏ d, (H d+1) := by classical simp [Box]

theorem finite_readout_exact (s : List V) (nodup : s.Nodup) (full : s.toFinset=Finset.univ)
    (w : ∀ v, U v → R) (inc : ∀ v, U v → D→ℕ) (moment : (D→ℤ) → R)
    (bound : ∀ a : (∀ v,U v), ∀ d, (∑ v, inc v (a v)) d ≤ H d) :
    (∑ x : Box H, dpRun H w inc s x * moment (intIndex H x)) =
      JointContraction.readout moment (JointContraction.distribution Finset.univ w (intInc inc)) := by
  classical
  simp_rw [dpRun_exact H s nodup, full, JointContraction.distribution_entry,
    Finset.sum_mul]
  rw [Finset.sum_comm,JointContraction.readout_distribution]
  apply Finset.sum_congr rfl
  intro y _
  let x : Box H := fun d => ⟨(∑ v, inc v (y v)) d, Nat.lt_succ_of_le (bound y d)⟩
  have hx : intIndex H x = ∑ v, intInc inc v (y v) := by
    funext d
    change (((∑ v, inc v (y v)) d : ℕ) : ℤ) = (∑ v, intInc inc v (y v)) d
    simp [Finset.sum_apply]
  rw [Finset.sum_eq_single x]
  · rw [← hx, if_pos rfl]
  · intro z _ hz
    have hn : (∑ v, intInc inc v (y v)) ≠ intIndex H z := by
      rw [← hx]
      exact fun h => hz ((intIndex_injective H h).symm)
    rw [if_neg hn, zero_mul]
  · simp

end FullReadout

#print axioms intIndex_injective
#print axioms distribution_negative
#print axioms gather_step_exact
#print axioms dpRun_exact
#print axioms box_card
#print axioms finite_readout_exact

end J45Cost