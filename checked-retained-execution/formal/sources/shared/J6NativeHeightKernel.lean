import J6NativeHeightDerivative
import J6NativeHeightPort
import Mathlib.Tactic

/-! At zeta = 0, the literal finite product for a source Cauchy matrix
entry has a root unless its omitted factor is that very mesh point.
Consequently the authentic row sum is exactly the same-packet wire
read used in the height and lifting certificates. -/
namespace J6NativeHeightKernel
open scoped BigOperators
open P1DyadicGrid P1DyadicGridBridge J6Mesh
open J6PhysicalPacking J6NativeHeightPort J6NativeHeightClearing

noncomputable def kernel (a : ℕ) (k t : ℤ) : ℚ :=
  (∏ q ∈ (grid a).erase k, ((t-q:ℤ):ℚ)) /
      (((cauchyPolynomial a).derivative.eval 0 : ℤ):ℚ)

theorem kernel_at_node (a : ℕ) (k t : ℤ) (ht : t ∈ grid a) :
    kernel a k t = if k=t then derivRatio a t else 0 := by
  unfold kernel
  by_cases h : k=t
  · subst k
    rw [if_pos rfl,derivRatio,cauchy_derivative_eval ht,Int.cast_prod]
  · rw [if_neg h]
    have hh : t ∈ (grid a).erase k := Finset.mem_erase.mpr ⟨Ne.symm h,ht⟩
    rw [Finset.prod_eq_zero hh (by simp),zero_div]

variable {C : Type*} [DecidableEq C]
noncomputable def sourceWeight (rho : C) (m l : ℕ) (h : m ≤ K m)
    (i : Fin (m+1)) (p q : Wire rho m (K m) l) : ℚ :=
  let s := place rho m (K m) l h p
  let r := place rho m (K m) l h q
  if s.1=r.1 ∧ s.2.1=r.2.1 then
    kernel (a m) ((r.2.2.val:ℤ)-(s.2.2.val:ℤ)) (index m i)
  else 0

theorem sourceWeight_eq (rho : C) (m l : ℕ) (h : m ≤ K m)
    (i : Fin (m+1)) (p q : Wire rho m (K m) l) :
    sourceWeight rho m l h i p q =
      if shiftedWire rho m (K m) l h (index m i) p = some q then point m i else 0 := by
  classical
  let s := place rho m (K m) l h p
  let r := place rho m (K m) l h q
  have ht0 : 0 < (index m i : ℤ) := by exact_mod_cast (address_index m i).1
  have hbound : (index m i : ℤ) < pow₂ (a m) := by
    unfold pow₂
    exact_mod_cast (address_index m i).2.2.2
  have ht := mem_grid.mpr (show -pow₂ (a m) ≤ (index m i : ℤ) ∧ _ from
    ⟨by have hp := pow₂_pos (a m); omega,hbound⟩)
  simp only [sourceWeight,shifted_iff_reaches]
  change (if s.1=r.1 ∧ s.2.1=r.2.1 then
      kernel (a m) ((r.2.2.val:ℤ)-(s.2.2.val:ℤ)) (index m i) else 0) =
      if reaches (index m i) s r then point m i else 0
  rw [kernel_at_node _ _ _ ht,J6NativeHeightDerivative.source_scalar_eq_actual_mesh]
  by_cases he : s.1=r.1 ∧ s.2.1=r.2.1
  · have he' : (r.2.2.val:ℤ)-(s.2.2.val:ℤ) = (index m i:ℤ) ↔
        s.2.2.val + index m i = r.2.2.val := by omega
    simp [reaches,he.1,he.2,he']
  · have hn : ¬ reaches (index m i) s r := fun hr => he ⟨hr.1,hr.2.1⟩
    simp [he,hn]

theorem literal_row_reduction [Fintype C] (rho : C) (m l : ℕ) (h : m ≤ K m)
    (i : Fin (m+1)) (p : Wire rho m (K m) l) (x : Wire rho m (K m) l → Bool) :
    (∑ q, sourceWeight rho m l h i p q * (if x q then (1:ℚ) else 0)) =
      if packedRead rho m (K m) l h (index m i) p x then point m i else 0 := by
  classical
  cases hq : shiftedWire rho m (K m) l h (index m i) p with
  | none => simp [sourceWeight_eq,packedRead,hq]
  | some q =>
    simp only [sourceWeight_eq,packedRead,hq,Option.map_some,Option.getD_some]
    rw [Finset.sum_eq_single_of_mem q (Finset.mem_univ q)]
    · cases x q <;> simp
    · intro q' _ hn
      have hh : q ≠ q' := Ne.symm hn
      simp [hh]

/-- The native zero-mode row sums before collapsing the partial shift.
The two Boolean tensor arguments can be the product of any literal
old clause/equality tables and the product of new subdivision equalities. -/
noncomputable def sourceContraction [Fintype C] (rho : C) (m l : ℕ) (h : m ≤ K m)
    (i : Fin (m+1)) (A B : (Wire rho m (K m) l → Bool) → Bool) : ℚ :=
  ∑ y : Wire rho m (K m) l → Bool, ∑ x : Wire rho m (K m) l → Bool,
    if A y && B x then
      ∏ p, (let z := ∑ q, sourceWeight rho m l h i p q * (if x q then (1:ℚ) else 0)
             if y p then z else 1-z)
    else 0

theorem full_contraction_reduction [Fintype C] (rho : C) (m l : ℕ) (h : m ≤ K m)
    (i : Fin (m+1)) (A B : (Wire rho m (K m) l → Bool) → Bool) :
    sourceContraction rho m l h i A B =
      rationalSlot A B (packedRead rho m (K m) l h (index m i)) (point m i) := by
  classical
  unfold sourceContraction rationalSlot
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  split
  · apply Finset.prod_congr rfl
    intro p _
    rw [literal_row_reduction rho m l h i p x]
    cases y p <;> cases packedRead rho m (K m) l h (index m i) p x <;>
      simp [LayerRecovery.wireFactor]
  · rfl

#print axioms full_contraction_reduction
#print axioms kernel_at_node
#print axioms sourceWeight_eq
#print axioms literal_row_reduction
end J6NativeHeightKernel
