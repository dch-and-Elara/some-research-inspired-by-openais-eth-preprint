import A1R43LiteralColumns

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 12000000

/-! The same original binary star graph has an easy terminal answer.
At the origin the odd wires are pinned by their unary columns; every
NAND row sees two zeros and every old equality column leaves one bit. -/
namespace A1R43Literal
open scoped Classical BigOperators Polynomial
open Polynomial J6R10Repack J6R9Recursive
noncomputable section

variable {V Pad : Type} [DecidableEq V] [Fintype V] [Fintype Pad]
variable (F : Finset (V×V))
local notation "N" => network F Pad
local notation "E" => Wire F Pad

omit [Fintype V] [Fintype Pad] in
theorem origin_rows_all_accept (σ : V→Bool) (r : Row F Pad) :
    rowFlag F (vertexLift F Pad σ) r=true := by
  cases r with
  | inl e => rw [row_NAND]; rfl
  | inr z => exact row_dummy F _ z

theorem original_star_count (f : ℤ[X]) (base : ℕ) (hb : 0<base)
    (hf : f.Monic) (hF : 0<f.natDegree) (positive : ∀ v,0<GraphCutMoments.degree F v) :
    trueContraction N (file F f base) hf = (2^(Fintype.card V):ℕ) := by
  calc
    _ = ∑ x : E→Bool,(∏ c : Col F Pad,spin (colFlag F x c)) *
      (∏ r : Row F Pad,spin (rowFlag F x r)) := by
      unfold trueContraction
      apply Finset.sum_congr (by ext u; simp only [Finset.mem_univ])
      intro x _
      rw [Fintype.prod_sum_type,mul_comm]
      congr 1
      · exact Finset.prod_congr rfl (fun c _=>file_frozen F f base hb hf hF (.inr c) _)
      · exact Finset.prod_congr rfl (fun r _=>file_frozen F f base hb hf hF (.inl r) _)
    _ = ∑ _σ : V→Bool,(1:IntRing f 1) := by
      rw [weighted_columns F positive]
      apply Finset.sum_congr rfl
      intro σ _
      apply Finset.prod_eq_one
      intro r _
      rw [origin_rows_all_accept F σ r]
      rfl
    _ = _ := by
      simp

#print axioms origin_rows_all_accept
#print axioms original_star_count
end
end A1R43Literal
