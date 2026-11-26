import P5GenericReadoutIntrinsic
import P5A2One
import P5A2SimulRank

/-! Reuse the already-verified actual quotient ranks, now identified
with the exact generic linear-form separation widths. -/
namespace Paper5.GenericReadout
open Module
open scoped BigOperators Classical

variable {K : Type*} [Field K]

theorem one_intrinsic_rank_if_highest (k : ℕ) (read : P5A2.Trunc K k→ₗ[K]K) (hr : read≠0) :
    ∃ r : Fin k,read (P5A2.powers K k r)≠0 ∧
      (∀ j : Fin k,r<j → read (P5A2.powers K k j)=0) ∧ rho read=r.val+1 := by
  obtain ⟨r,hn,hTail,hRank⟩ := P5A2.one_pairing_rank k read hr
  refine ⟨r,hn,hTail,?_⟩
  rw [←capacity_eq_rho (P5A2.powers K k)]
  exact hRank

theorem one_intrinsic_top_sharp (k : ℕ) :
    let b := P5A2.powers K (k+1)
    rho (b.coord (Fin.last k))=k+1 := by
  let b := P5A2.powers K (k+1)
  change rho (b.coord (Fin.last k))=_
  rw [←capacity_eq_rho b]
  apply P5A2.one_pairing_rank_of_last (k+1) (b.coord (Fin.last k)) (Fin.last k)
  · change b.coord (Fin.last k) (b (Fin.last k))≠0
    rw [P5A2.coord_basis,if_pos rfl]
    exact one_ne_zero
  · intro j h
    exact False.elim ((not_lt_of_ge (Fin.le_last j)) h)

theorem rectangle_intrinsic_monomial {k l : ℕ} (hk : 0<k) (a : Fin k × Fin l) :
    rho ((P5A2.simultaneousBasis (K:=K) k l hk).coord a)=(a.1.val+1)*(a.2.val+1) := by
  rw [←capacity_eq_rho (P5A2.simultaneousBasis (K:=K) k l hk)]
  exact P5A2.simultaneous_coordinate_rank hk a

theorem rectangle_intrinsic_top_sharp (k l : ℕ) :
    rho ((P5A2.simultaneousBasis (K:=K) (k+1) (l+1) (Nat.succ_pos _)).coord (Fin.last k,Fin.last l))=
      (k+1)*(l+1) := by
  exact rectangle_intrinsic_monomial (K:=K) (Nat.succ_pos _) (Fin.last k,Fin.last l)


theorem sharp_equals_dimension_uni (k : ℕ) :
    ∃ read : P5A2.Trunc K (k+1)→ₗ[K]K,rho read=Module.finrank K (P5A2.Trunc K (k+1)) := by
  let b := P5A2.powers K (k+1)
  refine ⟨b.coord (Fin.last k),?_⟩
  rw [Module.finrank_eq_card_basis b,Fintype.card_fin]
  exact one_intrinsic_top_sharp (K:=K) k

theorem sharp_equals_dimension_rectangle (k l : ℕ) :
    ∃ read : P5A2.Simultaneous K (k+1) (l+1)→ₗ[K]K,
      rho read=Module.finrank K (P5A2.Simultaneous K (k+1) (l+1)) := by
  let b := P5A2.simultaneousBasis (K:=K) (k+1) (l+1) (Nat.succ_pos _)
  refine ⟨b.coord (Fin.last k,Fin.last l),?_⟩
  rw [Module.finrank_eq_card_basis b,Fintype.card_prod,Fintype.card_fin,Fintype.card_fin]
  exact rectangle_intrinsic_top_sharp (K:=K) k l

#print axioms one_intrinsic_rank_if_highest
#print axioms one_intrinsic_top_sharp
#print axioms rectangle_intrinsic_monomial
#print axioms rectangle_intrinsic_top_sharp
#print axioms sharp_equals_dimension_uni
#print axioms sharp_equals_dimension_rectangle
end Paper5.GenericReadout
