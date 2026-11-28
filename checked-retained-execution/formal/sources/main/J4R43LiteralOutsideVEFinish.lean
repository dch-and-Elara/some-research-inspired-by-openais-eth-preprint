import J4R43LiteralOutsideVELiteral
import J4R43LiteralOutsideVEPlan

/-! Conditional induced-width evaluator for the original native register.
Input factors are the actual local old-file marginals; the only extra
input is a checked variable order. There is no claimed guarantee that
any fixed original packing has small induced width. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R10Repack J6R9PacketScopes J6R10RowAffine
open J5R41LiteralChildCost
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 7000000
set_option maxRecDepth 2200
set_option Elab.async false

variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B]
    [LinearOrder G] [Fintype G] {a : ℕ} {N : Network E A B}
variable {f : ℤ[X]} {ell : ℕ}
variable (P : PhysicalPacking N a G) (i : Fin a) (g : G) (t : ℤ)

local notation "D" => Boundary P i g t

theorem actual_row_scope_card (u : RowVertex P i g) :
    (actualRowScope P i g t u).card≤Fintype.card (RowPort P i g u) := by
  let S := actualRowScope P i g t u
  have h (m : S) : ∃ q : RowPort P i g u,matchingLink P i g t u q=some m.val :=
    (Finset.mem_filter.mp m.property).2
  let pick (m : S) := Classical.choose (h m)
  have inj : Function.Injective pick := by
    intro m n eq
    have x := Classical.choose_spec (h m)
    have y := Classical.choose_spec (h n)
    change matchingLink P i g t u (pick m)=_ at x
    change matchingLink P i g t u (pick n)=_ at y
    rw [eq,y] at x
    exact Subtype.ext (Option.some.inj x).symm
  rw [←Fintype.card_coe]
  exact Fintype.card_le_of_injective _ inj

theorem actual_col_scope_card (u : ColVertex P i g) :
    (actualColScope P i g t u).card≤Fintype.card (ColPort P i g u) := by
  let S := actualColScope P i g t u
  let K := boundaryPort P i g t
  have h (m : S) : (K m.val).1=u := (Finset.mem_filter.mp m.property).2
  let pick (m : S) : ColPort P i g u := h m ▸ (K m.val).2
  have e (m : S) : K m.val=⟨u,pick m⟩ := by
    unfold pick
    have castSame {left right : ColVertex P i g} (H : left=right) (x : ColPort P i g left) :
        HEq x (H ▸ x : ColPort P i g right) := by cases H; rfl
    exact Sigma.ext (h m) (castSame (h m) (K m.val).2)
  have inj : Function.Injective pick := by
    intro m n eq
    apply Subtype.ext
    apply boundaryCol_injective P i g t
    apply (colChart P i g).symm.injective
    change K m.val=K n.val
    rw [e m,e n,eq]
  rw [←Fintype.card_coe]
  exact Fintype.card_le_of_injective _ inj

variable (p : ℕ) (hnil : (2:Residue f ell p)^p=0)
variable (old : EntryFile f ell N) (hf : f.Monic)

theorem original_width_group_evaluation (ht : t≠0) (hv : padicValInt 2 t=i.val) (hp : 0<p)
    (w : ℕ) (order : List D)
    (legal : VE.LegalOrder w Finset.univ (literalVEFactors P i g t p hnil old hf) order) :
    let initial := literalVEFactors P i g t p hnil old hf
    physicalReply P i ht hv p hnil old hf 0 g =
      VE.prodAt (VE.finalFactors initial order) (fun _=>false) ∧
    VE.orderCost initial order≤
      order.length*2^w*(2*(initial.length+order.length)+1)+initial.length+order.length := by
  dsimp only
  refine ⟨?_,VE.actual_order_cost legal⟩
  rw [literal_group_boundary_exact P i g p hnil old hf ht hv hp,
    ←literal_factors_boundary_exact P i g t p hnil old hf,VE.actual_order_returns_value legal]

theorem literal_original_bucket_seed_count :
    (literalVEFactors P i g t p hnil old hf).length =
      Fintype.card (RowVertex P i g)+Fintype.card (ColVertex P i g) := by
  simp only [literalVEFactors,List.length_append,List.length_map,Finset.length_toList,Finset.card_univ]

#print axioms actual_row_scope_card
#print axioms actual_col_scope_card
#print axioms original_width_group_evaluation
#print axioms literal_original_bucket_seed_count
end
end J4R43LiteralOutside

