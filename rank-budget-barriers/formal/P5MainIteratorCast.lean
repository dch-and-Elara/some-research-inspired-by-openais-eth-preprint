import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! Scalar extension cannot inflate the rank of a finite matrix: factor
through an actual basis of the original column span. -/
namespace P5MainIterator
open Matrix Module
open scoped BigOperators Classical

variable {R S H V : Type*} [Field R] [Field S] [Fintype H] [Fintype V]

theorem rank_map_le (f : R →+* S) (C : Matrix H V R) :
    (C.map f).rank ≤ C.rank := by
  let U : Submodule R (H→R) := Submodule.span R (Set.range C.col)
  let b := Module.finBasis R U
  let c (v : V) : U := ⟨C.col v,Submodule.subset_span ⟨v,rfl⟩⟩
  let A : Matrix H (Fin (Module.finrank R U)) R := Matrix.of fun i j => (b j).val i
  let B : Matrix (Fin (Module.finrank R U)) V R := Matrix.of fun i j => b.repr (c j) i
  have hC : A*B=C := by
    apply Matrix.ext
    intro i j
    have h := congrArg (fun (v : U) => v.val i) (b.sum_repr (c j))
    change (∑ k, (b k).val i * b.repr (c j) k) = C i j
    simpa only [Submodule.coe_sum,Submodule.coe_smul,Finset.sum_apply,Pi.smul_apply,
      smul_eq_mul,mul_comm] using h
  conv_lhs => rw [←hC,Matrix.map_mul]
  have ha : ((A.map f).rank) ≤ Module.finrank R U := by
    simpa using (A.map f).rank_le_card_width
  calc
    _ ≤ (A.map f).rank := Matrix.rank_mul_le_left _ _
    _ ≤ Module.finrank R U := ha
    _ = C.rank := by rw [Matrix.rank_eq_finrank_span_cols]

#print axioms rank_map_le
end P5MainIterator
