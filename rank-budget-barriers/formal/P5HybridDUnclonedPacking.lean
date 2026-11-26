import P5HybridDUnclonedDegree
import P5HybridDUnclonedTags
import P5HybridDOnlyLayout
import J6R9PacketScopes
import J6R10RepackPhysical

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 26000000
set_option maxRecDepth 2200

/-! Use the general two-coordinate sampler on the genuine un-cloned D
network. The output has a single physical packing. Group colors are read
from the allocated physical pin seats, not fresh independent labels. -/
namespace Paper5.HybridDUncloned
open scoped Classical BigOperators
open J6R10Repack J6R9PacketScopes P11FullPacking J1MainSourceCollision
open Paper5.HybridClosure Paper5.HybridDOnly

noncomputable section

section RealPins
variable {W : Type} [Fintype W] [DecidableEq W] {a : ℕ}
variable (F : Finset (W×W)) (hC : ∀v,GraphCutMoments.degree F v=3)
variable (P : PhysicalPacking (network F hC) a (Fin 64))

def realPinGroup (i : Fin a) (w : W) : Fin 64 :=
  rowGroup P.mask i (P.seat (pinWire F w))

omit [Fintype W] in
theorem pin_group_is_row_label (i : Fin a) (w : W) :
    realPinGroup F hC P i w=P.rowLabel (.inr (.inl w)) i := by
  unfold realPinGroup rowGroup
  rw [P.exactCell]
  rfl
end RealPins

variable {V : Type} [Fintype V] [DecidableEq V]
variable (E : Finset (V×V)) (baseCubic : ∀v,GraphCutMoments.degree E v=3)
variable (loopless : ∀v,(v,v)∉E)
local notation "F" => replacedEdges E baseCubic
local notation "reg" => replaced_cubic E baseCubic loopless
local notation "N" => network F reg
local notation "n" => Fintype.card (TriVertex V)
local notation "M" => Nat.card (Wire F)

theorem on_same_uncloned_D_packing {a : ℕ}
    (exterior triangle : Fin a) (neq : exterior≠triangle) (Δ : ℕ)
    (hΔ : 3≤Δ) (hcell : 2*(J9PrintedSchedule.arrayCard a)^2*Δ≤M)
    (hslot : 2^a*J9PrintedSchedule.arrayCard a≤M) :
    ∃ (P : PhysicalPacking N a (Fin 64)) (c₁ : V→Fin 64) (c₂ : E→Fin 64),
      (∀ w, realPinGroup F reg P triangle w=mainPinColor c₁ w) ∧
      (∀ w, realPinGroup F reg P exterior w=dPinColor E baseCubic c₂ w) ∧
      P.copies=ceilCopies (2^a) (maxFiber (declaredCell N P.rowLabel P.colLabel)) ∧
      varianceScore (declaredCell N P.rowLabel P.colLabel)≤4*(M:ℚ)+3*n ∧
      varianceScore (declaredCell N P.rowLabel P.colLabel)≤2*(M:ℚ)*Δ ∧
      Nat.card (Page a P.copies (Fin 64))*2^a≤3*M ∧
      ∀ j g,Nat.card (rowsIn N (declaredGroup P.rowLabel P.colLabel j) g)≤3*M/64 ∧
            Nat.card (colsIn N (declaredGroup P.rowLabel P.colLabel j) g)≤3*M/64 := by
  letI : DecidableEq (Old F) := instDecidableEqSum
  letI : DecidableEq (Link F) := instDecidableEqSum
  have hm : M=10*n := by
    rw [Nat.card_eq_fintype_card,physical_wire_count F reg]
  obtain ⟨cfg,P,pr,_pc,hround,hscore,hdelta,hpages,hgroups⟩ :=
    same_packing_with_both_ties (E:=Wire F) (A:=Old F) (B:=Link F) (U:=V) (T:=↥E) (a:=a)
      N exterior triangle (innerTie E baseCubic) (outerTie E baseCubic)
      n Δ (fun e=>(subdivision_degree F reg e).le) (old_degree F reg)
      (fun v=>(inner_tag_fibre E baseCubic loopless v).le)
      (fun e=>(outer_tag_fibre E baseCubic loopless e).le)
      (tied_slots_inner E baseCubic loopless).le (tied_slots_outer E baseCubic loopless).le
      (by rw [hm]; omega) hΔ hcell hslot
  let c₁ : V→Fin 64 := fun v=>cfg (.inl (.inr (.inl v)),triangle)
  let c₂ : E→Fin 64 := fun e=>cfg (.inl (.inr (.inr e)),exterior)
  refine ⟨P,c₁,c₂,?_,?_,hround,hscore,hdelta,hpages,hgroups⟩
  · intro w
    rw [pin_group_is_row_label,pr]
    simp [rowWord,tiedAtom,twoTags_at_triangle neq,innerTie,liftPinTag,mainPinColor,c₁]
  · intro w
    rw [pin_group_is_row_label,pr]
    simp [rowWord,tiedAtom,twoTags_at_exterior,outerTie,liftPinTag,dPinColor,c₂]

include loopless in
theorem true_uncloned_bucket_count
    (g₁ g₂ : TriVertex V→Fin 64)
    (mono₁ : ∀e∈innerEdges V,g₁ e.1=g₁ e.2)
    (mono₂ : ∀e∈outerEdges E baseCubic,g₂ e.1=g₂ e.2)
    (σ : TriVertex V→Bool) :
    PinnedCNF.modelCount (PinnedCNF.formula F σ)=
      (∏ g : Fin 64,groupOperand (innerEdges V) g₁ mono₁ g (σ∘Subtype.val)) *
      (∏ g : Fin 64,groupOperand (outerEdges E baseCubic) g₂ mono₂ g (σ∘Subtype.val)) := by
  rw [PinnedCNF.count_eq_indicator,←edge_product_is_indicator,completed_operand,completed_operand]
  exact Finset.prod_union (triangle_split_disjoint E baseCubic loopless)

#print axioms pin_group_is_row_label
#print axioms on_same_uncloned_D_packing
#print axioms true_uncloned_bucket_count
end
end Paper5.HybridDUncloned
