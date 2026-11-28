import J6R15PlantedIdentityMesh
import J6DeformationPoly

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8500000

/-! The exact Appendix D kernel on the original signed grid at the
specific centre -1 and literal probe 0. Reflection is about -1/2;
the odd derivative degree gives the actual minus sign. -/
namespace A1R43Literal
open scoped Classical BigOperators Polynomial
open Polynomial DenominatorBudget P1DyadicGrid P11FullPacking
open J6R9Recursive J6R10Repack J6R10Integral J6R11Integral

noncomputable section

theorem minus_one_mem_grid (a : ℕ) : (-1:ℤ) ∈ grid a := by
  rw [mem_grid]
  have h := pow₂_pos a
  omega

theorem reflect_grid (a : ℕ) (q : ℤ) :
    -1-q ∈ grid a ↔ q ∈ grid a := by
  simp only [mem_grid]
  omega

theorem reflect_derivative (a : ℕ) :
    (cauchyPolynomial a).derivative.eval (-1) =
      -(cauchyPolynomial a).derivative.eval 0 := by
  rw [cauchy_derivative_eval (minus_one_mem_grid a),cauchy_derivative_eval (zero_mem_grid a)]
  have all : (∏ q ∈ (grid a).erase (-1), ((-1:ℤ)-q)) =
    ∏ q ∈ (grid a).erase 0, -((0:ℤ)-q) := by
    apply Finset.prod_bij (fun (q : ℤ) _ => -1-q)
    · intro q hq
      rw [Finset.mem_erase] at hq ⊢
      exact ⟨by omega,(reflect_grid a q).2 hq.2⟩
    · intro q _ t _ h
      omega
    · intro t ht
      rw [Finset.mem_erase] at ht
      exact ⟨-1-t,Finset.mem_erase.mpr ⟨by omega,(reflect_grid a t).2 ht.2⟩,by omega⟩
    · intro q _
      ring
  rw [all]
  have hp : (∏ q ∈ (grid a).erase (0:ℤ), -((0:ℤ)-q)) =
    ∏ q ∈ (grid a).erase 0,(-1:ℤ)*((0:ℤ)-q) :=
    Finset.prod_congr rfl (fun q _=>(neg_one_mul ((0:ℤ)-q)).symm)
  rw [hp,Finset.prod_mul_distrib,Finset.prod_const]
  have hc : ((grid a).erase (0:ℤ)).card=2*(2^a-1)+1 := by
    rw [Finset.card_erase_of_mem (zero_mem_grid a),J6DeformationPoly.grid_card]
    have hp : 0 < (2:ℕ)^a := pow_pos (by decide) _
    omega
  rw [hc,pow_add,pow_mul]
  norm_num

theorem rho_minus_one (a : ℕ) : J6R9PacketCoeff.rho a (-1)=(-1:TwoLocal) := by
  apply twoLocalRat_injective
  rw [J6R9PacketCoeff.rho_rat (minus_one_mem_grid a),map_neg,map_one]
  unfold P1DyadicGridBridge.derivRatio
  rw [reflect_derivative]
  have hn : (↑((cauchyPolynomial a).derivative.eval 0) : ℚ) ≠ 0 := by
    exact_mod_cast cauchy_derivative_nonzero (zero_mem_grid a)
  push_cast
  rw [neg_div,div_self hn]

theorem minus_one_odd_index (a : ℕ) (i : Fin a) (hi : i.val=0) :
    padicValInt 2 (-1)=i.val := by simp [hi]

variable {E A B G : Type*} [LinearOrder G] [Fintype G] {a : ℕ}
variable [Fintype E] [Fintype A] [Fintype B]
variable {N : Network E A B}

def unitPredecessor (P : PhysicalPacking N a G) (r s : E) : Prop :=
  (P.seat r).1=(P.seat s).1 ∧ (P.seat s).2.val+1=(P.seat r).2.val

omit [Fintype E] [Fintype A] [Fintype B] in
theorem unitPredecessor_unique (P : PhysicalPacking N a G) (r s s' : E)
    (hs : unitPredecessor P r s) (hs' : unitPredecessor P r s') : s=s' := by
  apply P.seat.injective
  exact Prod.ext (hs.1.symm.trans hs'.1) (Fin.ext (by have h:=hs.2; have h':=hs'.2; omega))

omit [Fintype E] [Fintype A] [Fintype B] in
theorem actual_kernel_minus_one (P : PhysicalPacking N a G)
    (f : ℤ[X]) (ell p : ℕ) (r s : E) :
    finiteEntry p f ell (parentAtlas P) (-1) 0 r s =
      if unitPredecessor P r s then -1 else 0 := by
  unfold finiteEntry
  rw [J6R15PlantedIdentity.W_eval_zero,rho_minus_one,map_neg,map_one]
  have diff : (parentAtlas P).index s-(parentAtlas P).index r= -1 ↔
      (P.seat s).2.val+1=(P.seat r).2.val := by
    change ((P.seat s).2.val:ℤ)-((P.seat r).2.val:ℤ)= -1 ↔ _
    omega
  by_cases h : (P.seat r).1=(P.seat s).1
  · have hh : (parentAtlas P).page r=(parentAtlas P).page s := h
    rw [if_pos hh]
    by_cases d : (P.seat s).2.val+1=(P.seat r).2.val
    · rw [if_pos (diff.2 d),if_pos (show unitPredecessor P r s from ⟨h,d⟩)]
    · rw [if_neg (fun e=>d (diff.1 e)),if_neg (fun e : unitPredecessor P r s=>d e.2)]
  · have hh : ¬(parentAtlas P).page r=(parentAtlas P).page s := h
    rw [if_neg hh,if_neg (fun e : unitPredecessor P r s=>h e.1)]

#print axioms minus_one_mem_grid
#print axioms reflect_derivative
#print axioms rho_minus_one
#print axioms minus_one_odd_index
#print axioms unitPredecessor_unique
#print axioms actual_kernel_minus_one
end
end A1R43Literal
