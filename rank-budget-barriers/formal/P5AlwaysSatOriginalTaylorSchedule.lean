import P5AlwaysSatOriginalTaylorCaps

/-! The printed β=1 is a derived source choice for both (M.7) branches.
The sparse branch is the original unfixed one at that size. -/
namespace Paper5.AlwaysSatOriginal.Physical.Taylor
open P5MainBalance
open scoped Classical

variable {V : Type*} [Fintype V]
variable (E : Finset (V×V)) (T : Finset V)

def BetaLegal {X W F : Type*} (n b : ℕ) (o : X→W) (f : X→F) : Prop :=
  1≤b ∧
  (∀ w,Nat.card {x : X // o x=w}≤(mainLambda n)^b) ∧
  (∀ v,Nat.card {x : X // f x=v}≤(mainLambda n)^b)

theorem lambda_large_for_roots (hN : 8≤Fintype.card V) :
    4≤mainLambda (mainN E T) := by
  have hp := original_port_card E T
  have h : 8<mainN E T := by unfold mainN; omega
  rw [mainLambda_as_clog]
  exact Nat.succ_le_of_lt ((Nat.lt_clog_iff_pow_lt (by decide : 1<(2:ℕ))).mpr h)

theorem actual_direct_beta_one (hN : 8≤Fintype.card V) :
    IsLeast {b : ℕ | BetaLegal (mainN E T) b (portOwner E T) (portFactor E T)} 1 := by
  have h := lambda_large_for_roots E T hN
  constructor
  · change BetaLegal (mainN E T) 1 (portOwner E T) (portFactor E T)
    refine ⟨le_rfl,fun w=>?_,fun f=>?_⟩
    · rw [pow_one]
      exact (physical_copy_degree_le E T w).trans (by omega)
    · rw [pow_one]
      exact (factor_fibre_degree E T f).2.trans (by omega)
  · intro b hb
    exact hb.1

theorem actual_sparse_beta_one (hN : 8≤Fintype.card V) :
    IsLeast {b : ℕ | BetaLegal (mainN E T) b (sparseOwner E T) (sparseFactor E T)} 1 := by
  have h := lambda_large_for_roots E T hN
  constructor
  · change BetaLegal (mainN E T) 1 (sparseOwner E T) (sparseFactor E T)
    refine ⟨le_rfl,fun w=>?_,fun f=>?_⟩
    · rw [pow_one]
      exact (sparse_copy_degree_le E T w).trans h
    · rw [pow_one]
      exact (sparse_factor_degree E T f).2.trans (by omega)
  · intro b hb
    exact hb.1

theorem printed_sparse_branch_unchanged (hN : 8≤Fintype.card V) : sparseHeavy E T=∅ := by
  apply sparse_printed_heavy_empty
  have h := (main_port_card_lower E T).1
  omega

#print axioms lambda_large_for_roots
#print axioms actual_direct_beta_one
#print axioms actual_sparse_beta_one
#print axioms printed_sparse_branch_unchanged
end Paper5.AlwaysSatOriginal.Physical.Taylor