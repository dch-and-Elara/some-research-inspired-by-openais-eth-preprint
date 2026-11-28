import BooleanCube.Walsh

namespace LocalReconstruction

def toggle {q : ℕ} (a x : Cube q) : Cube q := fun i => (a i).xor (x i)

def shift {q : ℕ} (a : Cube q) (f : Cube q → ℚ) : Cube q → ℚ :=
  fun x => f (toggle a x)

def oneBit {q : ℕ} (i : Fin q) : Cube q := fun j => decide (j = i)

def FlipInvariant {q : ℕ} (W : Submodule ℚ (Cube q → ℚ)) : Prop :=
  ∀ i f, f ∈ W → shift (oneBit i) f ∈ W

def walshSpace {q : ℕ} (A : Set (Cube q)) : Submodule ℚ (Cube q → ℚ) :=
  Submodule.span ℚ (walsh '' A)

theorem walsh_toggle {q : ℕ} (s a x : Cube q) :
    walsh s (toggle a x) = walsh s a * walsh s x := by
  unfold walsh
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  unfold toggle
  cases s i <;> cases a i <;> cases x i <;> norm_num [signBit, Bool.xor]

private theorem all_shifts {q : ℕ} {W : Submodule ℚ (Cube q → ℚ)}
    (hW : FlipInvariant W) (a : Cube q) (f : Cube q → ℚ) (hf : f ∈ W) : shift a f ∈ W := by
  classical
  have partialShift (U : Finset (Fin q)) :
      shift (fun j => if j ∈ U then a j else false) f ∈ W := by
    induction U using Finset.induction_on with
    | empty =>
      have e : shift (fun _ => false) f = f := by
        funext x
        apply congrArg f
        funext i
        cases h : x i <;> simp [toggle, h]
      simpa only [Finset.notMem_empty, if_false, e] using hf
    | @insert i U hi ih =>
      cases ha : a i with
      | false =>
        convert ih using 1
        congr 1
        funext j
        by_cases hj : j = i <;> simp_all
      | true =>
        convert hW i _ ih using 1
        funext x
        apply congrArg f
        funext j
        by_cases hj : j = i
        · subst j
          simp [toggle, oneBit, hi, ha]
        · simp [toggle, oneBit, hj]
  simpa using partialShift Finset.univ

def coefficient {q : ℕ} (s : Cube q) (f : Cube q → ℚ) : ℚ :=
  ∑ y : Cube q, f y * walsh s y

private def translateEquiv {q : ℕ} (x : Cube q) : Cube q ≃ Cube q where
  toFun a := toggle a x
  invFun a := toggle a x
  left_inv a := by funext i; cases h : a i <;> cases k : x i <;> simp [toggle,h,k]
  right_inv a := by funext i; cases h : a i <;> cases k : x i <;> simp [toggle,h,k]

theorem frequency_mem {q : ℕ} {W : Submodule ℚ (Cube q → ℚ)} (hW : FlipInvariant W)
    (s : Cube q) (f : Cube q → ℚ) (hf : f ∈ W) : coefficient s f • walsh s ∈ W := by
  classical
  have hm : (∑ a : Cube q, walsh s a • shift a f) ∈ W :=
    W.sum_mem fun a _ => W.smul_mem _ (all_shifts hW a f hf)
  convert hm using 1
  funext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, shift, coefficient, Finset.sum_mul]
  calc
    _ = ∑ y : Cube q, walsh s (toggle y x) * f y := by
      apply Finset.sum_congr rfl
      intro y _
      rw [walsh_toggle]
      ring
    _ = _ := by
      have h := (translateEquiv x).sum_comp (fun a => walsh s a * f (toggle a x))
      have e (a : Cube q) : toggle (toggle a x) x = a := (translateEquiv x).left_inv a
      change (∑ a : Cube q, walsh s (toggle a x) * f (toggle (toggle a x) x)) = _ at h
      simpa only [e] using h

theorem flipInvariant_iff {q : ℕ} (W : Submodule ℚ (Cube q → ℚ)) :
    FlipInvariant W ↔ ∃ A : Set (Cube q), W = walshSpace A := by
  classical
  constructor
  · intro hW
    let A : Set (Cube q) := {s | walsh s ∈ W}
    refine ⟨A, le_antisymm ?_ (Submodule.span_le.mpr ?_)⟩
    · intro f hf
      have sum_mem : (∑ s : Cube q, coefficient s f • walsh s) ∈ walshSpace A := by
        apply Submodule.sum_mem
        intro s _
        by_cases h : coefficient s f = 0
        · simp [h]
        · have hw : walsh s ∈ W := by
            have := W.smul_mem (coefficient s f)⁻¹ (frequency_mem hW s f hf)
            simpa [smul_smul, h] using this
          exact (walshSpace A).smul_mem _ (Submodule.subset_span ⟨s, hw, rfl⟩)
      have eq : (∑ s : Cube q, coefficient s f • walsh s) = (2^q : ℚ) • f := by
        funext x
        simpa [coefficient, Finset.sum_apply] using synthesis f x
      rw [eq] at sum_mem
      have := (walshSpace A).smul_mem ((2:ℚ)^q)⁻¹ sum_mem
      simpa [smul_smul] using this
    · rintro v ⟨s, hs, rfl⟩
      exact hs
  · rintro ⟨A, rfl⟩ i f hf
    induction hf using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨s,hs,rfl⟩ := hv
      have eq : shift (oneBit i) (walsh s) = walsh s (oneBit i) • walsh s := by
        funext x
        exact walsh_toggle _ _ _
      rw [eq]
      exact (walshSpace A).smul_mem _ (Submodule.subset_span ⟨s,hs,rfl⟩)
    | zero => exact (walshSpace A).zero_mem
    | add x y _ _ hx hy => exact (walshSpace A).add_mem hx hy
    | smul a x _ hx => exact (walshSpace A).smul_mem a hx

end LocalReconstruction
