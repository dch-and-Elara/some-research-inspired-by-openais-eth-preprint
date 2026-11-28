import J4R43LiteralOutsideEnumeration

/-! Exact list sizes for the original general J4 boundary evaluator.
This is its boundary-bit traversal, not the printed recursively
materialized alternative. Local acquisitions are genuine source words
on the indicated old vertices, not arbitrary group scalars. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R10Repack J6R9PacketScopes
open J5R41LiteralChildCost
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5000000

variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B]
    [LinearOrder G] [Fintype G] {a : ℕ} {N : Network E A B}
variable (P : PhysicalPacking N a G) (i : Fin a) (g : G) (t : ℤ)

abbrev localRowQueries := Σ v : RowVertex P i g,RowPort P i g v→Bool
abbrev localColQueries := Σ v : ColVertex P i g,ColPort P i g v→Bool

theorem actual_group_boundary_visits :
    Fintype.card (Boundary P i g t→Bool)=2^(matched P i g t).card := by
  rw [Fintype.card_fun,Fintype.card_bool,Fintype.card_coe]

theorem actual_group_boundary_acquisitions :
    Fintype.card ((Boundary P i g t→Bool)×(localRowQueries P i g⊕localColQueries P i g)) =
      2^(matched P i g t).card*
        ((∑ v : RowVertex P i g,2^Fintype.card (RowPort P i g v))+
          ∑ v : ColVertex P i g,2^Fintype.card (ColPort P i g v)) := by
  rw [Fintype.card_prod,actual_group_boundary_visits,Fintype.card_sum,Fintype.card_sigma,
    Fintype.card_sigma]
  simp only [Fintype.card_fun,Fintype.card_bool]

theorem actual_group_boundary_degree_cost (Δ : ℕ)
    (hr : ∀ v : RowVertex P i g,Fintype.card (RowPort P i g v)≤Δ)
    (hc : ∀ v : ColVertex P i g,Fintype.card (ColPort P i g v)≤Δ) :
    Fintype.card ((Boundary P i g t→Bool)×(localRowQueries P i g⊕localColQueries P i g)) ≤
      2^(matched P i g t).card*
        ((Fintype.card (RowVertex P i g)+Fintype.card (ColVertex P i g))*2^Δ) := by
  rw [actual_group_boundary_acquisitions]
  apply Nat.mul_le_mul_left
  rw [Nat.add_mul]
  apply Nat.add_le_add
  · refine (Finset.sum_le_sum (fun v _=>Nat.pow_le_pow_right (by decide) (hr v))).trans ?_
    simp
  · refine (Finset.sum_le_sum (fun v _=>Nat.pow_le_pow_right (by decide) (hc v))).trans ?_
    simp

theorem actual_all_groups_boundary_visits :
    (∑ z : G,Fintype.card (Boundary P i z t→Bool))≤
      Fintype.card G*2^(3*Nat.card E*(2^a-t.natAbs)/(2^a)) := by
  calc
    _≤∑ z : G,2^(3*Nat.card E*(2^a-t.natAbs)/(2^a)) := by
      refine Finset.sum_le_sum fun z _=>?_
      rw [actual_group_boundary_visits]
      apply Nat.pow_le_pow_right (by decide)
      exact (Nat.le_div_iff_mul_le (by positivity)).mpr (actual_match_count P i z t)
    _=_ := by simp

theorem both_odd_outside_boundary_cost (outer : t.natAbs=2^a-1) :
    (∑ z : G,Fintype.card (Boundary P i z t→Bool))≤
      Fintype.card G*2^(3*Nat.card E/(2^a)) := by
  have pos : 0<(2:ℕ)^a := by positivity
  have one : 2^a-t.natAbs=1 := by omega
  simpa only [one,mul_one] using actual_all_groups_boundary_visits P i t

#print axioms actual_group_boundary_visits
#print axioms actual_group_boundary_acquisitions
#print axioms actual_group_boundary_degree_cost
#print axioms actual_all_groups_boundary_visits
#print axioms both_odd_outside_boundary_cost
end
end J4R43LiteralOutside

