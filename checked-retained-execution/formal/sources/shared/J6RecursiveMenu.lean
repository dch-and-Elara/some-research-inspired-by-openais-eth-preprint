import J6RecursiveModes
import Mathlib.Tactic

/-! The actual complete weighted tape of nonnegative mode tuples in
the printed rule. No arbitrary subset of modes is used in this certificate. -/
namespace J6RecursiveMenu
open scoped BigOperators
variable {M : Type*} [Fintype M] [DecidableEq M]

noncomputable def code (p : ℕ) (x : M → Fin p) : M →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun m => (x m).val)

omit [DecidableEq M] in
theorem code_apply (p : ℕ) (x : M → Fin p) (m : M) : code p x m = (x m).val := by
  unfold code
  exact congrFun ((Finsupp.equivFunOnFinite : (M →₀ ℕ) ≃ (M → ℕ)).apply_symm_apply (fun i => (x i).val)) m

def weighted (w : M → ℕ) (β : M →₀ ℕ) : ℕ :=
  ∑ m, w m * β m

noncomputable def menu (p : ℕ) (w : M → ℕ) : Finset (M →₀ ℕ) := by
  classical
  exact ((Finset.univ : Finset (M → Fin p)).image (code p)).filter (fun β => weighted w β < p)

theorem exact_printed_menu (p : ℕ) (w : M → ℕ) (hw : ∀ m, 0 < w m) (β : M →₀ ℕ) :
    β ∈ menu p w ↔ weighted w β < p := by
  classical
  unfold menu
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    have hm (m : M) : β m < p := by
      apply lt_of_le_of_lt _ h
      exact (Nat.le_mul_of_pos_left _ (hw m)).trans
        (Finset.single_le_sum (fun j _ => Nat.zero_le (w j * β j)) (Finset.mem_univ m))
    let x : M → Fin p := fun m => ⟨β m,hm m⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨x,Finset.mem_univ x,?_⟩,h⟩
    ext m
    exact code_apply p x m

theorem zero_in_menu (p : ℕ) (hp : 0 < p) (w : M → ℕ) (hw : ∀ m,0 < w m) :
    (0 : M →₀ ℕ) ∈ menu p w := by
  rw [exact_printed_menu p w hw]
  simpa [weighted] using hp

#print axioms exact_printed_menu
#print axioms zero_in_menu
end J6RecursiveMenu
