import P5HermiteTransportGenericRank

/-! Original H.3 entrance refinements. Splitting local maps is paid by
their summed ranks; collecting genuinely identical coefficient
entrances sums their scalar transfers BEFORE charging rank. -/
namespace Paper5.HermiteGeneric
open Matrix
open scoped BigOperators Kronecker Classical

variable {K T U V W : Type*} [Field K] [Fintype T] [DecidableEq T]
  [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] [Fintype W]

omit [Fintype W] in
theorem convolution_entrance_rank (L : Layout K T) (b : ℕ)
    (C : (t : T)→Fin (L.order t)→Matrix U V K) (J : T→Type*) [∀ t,Fintype (J t)]
    (parts : (t : T)→J t→Matrix (Fin (L.order t) × U) (Fin (L.order t) × V) K)
    (hParts : ∀t,convolution (C t)=∑ j,parts t j) :
    (compressed L b C).rank ≤∑ t,∑ j,(parts t j).rank := by
  refine (compressed_rank_bound L b C).trans (Finset.sum_le_sum ?_)
  intro t _
  rw [hParts]
  exact SeparatedRank.rank_sum_le _ _

omit [DecidableEq U] [Fintype W] in
theorem split_coefficient_entrance_rank (L : Layout K T) (b : ℕ)
    (C : (t : T)→Fin (L.order t)→Matrix U V K)
    (J : (t : T)→Fin (L.order t)→Type*) [∀ t a,Fintype (J t a)]
    (parts : (t : T)→(a : Fin (L.order t))→J t a→Matrix U V K)
    (hParts : ∀t a,C t a=∑ j,parts t a j) :
    (expanded L b C).rank ≤∑ t,∑ a,(transfer L b t a).rank*(∑ j,(parts t a j).rank) := by
  refine (expanded_rank_bound L b C).trans (Finset.sum_le_sum ?_)
  intro t _
  apply Finset.sum_le_sum
  intro a _
  apply Nat.mul_le_mul_left
  rw [hParts]
  exact SeparatedRank.rank_sum_le _ _

noncomputable def collectedTransfer (L : Layout K T) (b : ℕ)
    (c : (t : T)→Fin (L.order t)→W→K) (w : W) : Matrix (Fin b) (Fin b) K :=
  ∑ t,∑ a,c t a w • transfer L b t a

omit [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] in
set_option maxHeartbeats 9500000 in
theorem collect_identical_entrances (L : Layout K T) (b : ℕ)
    (C : (t : T)→Fin (L.order t)→Matrix U V K)
    (c : (t : T)→Fin (L.order t)→W→K) (Q : W→Matrix U V K)
    (hC : ∀t a,C t a=∑ w,c t a w • Q w) :
    expanded L b C = ∑ w,collectedTransfer L b c w ⊗ₖ Q w := by
  let S := Σ t : T,Fin (L.order t)
  have hL : expanded L b C=∑ s : S,transfer L b s.1 s.2 ⊗ₖ C s.1 s.2 :=
    (Fintype.sum_sigma (fun s : S=>transfer L b s.1 s.2 ⊗ₖ C s.1 s.2)).symm
  have hR (w : W) : collectedTransfer L b c w=∑ s : S,c s.1 s.2 w • transfer L b s.1 s.2 :=
    (Fintype.sum_sigma (fun s : S=>c s.1 s.2 w • transfer L b s.1 s.2)).symm
  rw [hL]
  simp_rw [hR,hC]
  apply Matrix.ext
  rintro ⟨i,u⟩ ⟨j,v⟩
  simp only [Matrix.sum_apply,Matrix.kronecker_apply,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro s _
  ring

omit [DecidableEq U] in
theorem distinct_entrance_rank (L : Layout K T) (b : ℕ)
    (C : (t : T)→Fin (L.order t)→Matrix U V K)
    (c : (t : T)→Fin (L.order t)→W→K) (Q : W→Matrix U V K)
    (hC : ∀t a,C t a=∑ w,c t a w • Q w) :
    (expanded L b C).rank ≤∑ w,(collectedTransfer L b c w).rank*(Q w).rank := by
  rw [collect_identical_entrances L b C c Q hC]
  exact (SeparatedRank.rank_sum_le _ _).trans (Finset.sum_le_sum fun w _=>
    kronecker_rank_le (collectedTransfer L b c w) (Q w))

#print axioms convolution_entrance_rank
#print axioms split_coefficient_entrance_rank
#print axioms collect_identical_entrances
#print axioms distinct_entrance_rank
end Paper5.HermiteGeneric
