import J4R43LiteralOutsideVEFinish

/-! An independently supplied legal order for each actual group
evaluates the original *complete* zero slot. Values remain the
products of the same native lifts with the true partial wiring. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R10Repack J6R9PacketScopes J6R10RowAffine
open J5R41LiteralChildCost
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5500000

variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B]
    [LinearOrder G] [Fintype G] {a : ℕ} {N : Network E A B}
variable {f : ℤ[X]} {ell : ℕ}
variable (P : PhysicalPacking N a G) (i : Fin a) (t : ℤ)
variable (p : ℕ) (hnil : (2:Residue f ell p)^p=0)
variable (old : EntryFile f ell N) (hf : f.Monic)

theorem complete_slot_from_explicit_width (ht : t≠0) (hv : padicValInt 2 t=i.val) (hp : 0<p)
    (w : ℕ) (order : ∀ g : G,List (Boundary P i g t))
    (legal : ∀ g : G,VE.LegalOrder w Finset.univ (literalVEFactors P i g t p hnil old hf) (order g)) :
    let initial := fun g=>literalVEFactors P i g t p hnil old hf
    V8PooledMenu.slot P i ht hv p hnil 0 old hf 0 =
        ∏ g : G,VE.prodAt (VE.finalFactors (initial g) (order g)) (fun _=>false) ∧
    (∑ g : G,VE.orderCost (initial g) (order g))+Fintype.card G≤
      ∑ g : G,((order g).length*2^w*(2*((initial g).length+(order g).length)+1)+
        (initial g).length+(order g).length+1) := by
  dsimp only
  have H (g : G) := original_width_group_evaluation P i g t p hnil old hf ht hv hp w (order g) (legal g)
  constructor
  · unfold V8PooledMenu.slot
    exact Finset.prod_congr rfl (fun g _=>(H g).1)
  · rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
    exact Nat.add_le_add_right (Finset.sum_le_sum fun g _=>(H g).2) (Fintype.card G)

#print axioms complete_slot_from_explicit_width
end
end J4R43LiteralOutside

