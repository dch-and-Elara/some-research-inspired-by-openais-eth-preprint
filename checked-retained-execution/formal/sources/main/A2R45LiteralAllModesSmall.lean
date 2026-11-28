import A2R45LiteralAllModesNormalize
import A2R45LiteralAllModesSparse

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3600000
set_option maxRecDepth 1800

/-! A2 line 2349: exact direct-sum fallback below a fixed normalized
size bound. Candidate count is explicit; this is not a bit trace. -/
namespace A2R45Literal
open scoped Classical BigOperators
open Std.Sat J7R9Compiler

noncomputable section
variable {V : Type} [Fintype V]

def smallDirectSum (F : CNF V) : ℕ :=
  ∑ x : V→Bool,if CNF.Sat x F then 1 else 0

theorem direct_sum_is_raw_count (F : CNF V) : smallDirectSum F=PinnedCNF.modelCount F := by
  rw [modelCount_card F,Nat.card_eq_fintype_card,Fintype.card_subtype]
  unfold smallDirectSum
  rw [←Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
  norm_cast

variable [DecidableEq V] (F : CNF V)

theorem small_normalized_case_exact (K : ℕ) (guard : sparseS (normalizeSparse F)≤K) :
    Fintype.card (Used (J7R9Clause.clean F)→Bool)≤2^K ∧
      smallDirectSum (normalizeSparse F)*2^Nat.card (Unused (J7R9Clause.clean F)) =
        PinnedCNF.modelCount F := by
  constructor
  · rw [Fintype.card_fun,Fintype.card_bool]
    exact Nat.pow_le_pow_right (by decide)
      ((Nat.le_add_right _ (normalizeSparse F).length).trans guard)
  · rw [direct_sum_is_raw_count]
    exact (normalizeSparse_count F).symm

#print axioms direct_sum_is_raw_count
#print axioms small_normalized_case_exact
end
end A2R45Literal
