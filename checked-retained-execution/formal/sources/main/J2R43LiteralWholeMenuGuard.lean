import J2R43LiteralWholeMenuGeometry

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
set_option maxRecDepth 2200
set_option linter.unusedSectionVars false

namespace J2R43LiteralWholeMenu
open scoped Classical Polynomial BigOperators
open Polynomial P11FullPacking P9BalancedChart OuterNodePacking
open J6R10Repack J9R14LowPrecisionGeometry
open Paper5.D1Literal Paper5.HybridClosure

noncomputable section
section Generic
variable {U A G : Type} [Fintype U] [DecidableEq U] [Nonempty U]
variable [LinearOrder G] [Fintype G] {a : ℕ}

theorem row_real_is_seat {b : ℕ} (seat : U×Bool ↪ Physical a b G) :
    rowReal (nativeSeats (fun e=>seat e) (fun e=>seat e))=realSlot seat := by
  funext z
  by_cases h : ∃ e : U×Bool, seat e=z <;> simp [rowReal,nativeSeats,realSlot,h]

theorem col_real_is_seat {b : ℕ} (seat : U×Bool ↪ Physical a b G) :
    colReal (nativeSeats (fun e=>seat e) (fun e=>seat e))=realSlot seat := by
  funext z
  by_cases h : ∃ e : U×Bool, seat e=z <;> simp [colReal,nativeSeats,realSlot,h]

noncomputable def genericKept {N : Network (U×Bool) A U} (P : PhysicalPacking N a G) (t : ℤ) : Finset U :=
  untouched Finset.univ (vertexOwner P.seat)
    (matchedColumns Finset.univ (realSlot P.seat) (realSlot P.seat) t)

noncomputable def guardReseat {N : Network (U×Bool) A U} (P : PhysicalPacking N a G)
    (seat : U×Bool↪Physical a P.copies G)
    (label : ∀ w, physicalCell (balancedMask a P.copies G) (seat w)=
      declaredCell N P.rowLabel P.colLabel w) : PhysicalPacking N a G :=
  ⟨P.rowLabel,P.colLabel,P.copies,balancedMask a P.copies G,seat,label,P.paddedBudget⟩

theorem reseat_kept {N : Network (U×Bool) A U} (P : PhysicalPacking N a G)
    (seat : U×Bool↪Physical a P.copies G)
    (label : ∀ w, physicalCell (balancedMask a P.copies G) (seat w)=
      declaredCell N P.rowLabel P.colLabel w) (t : ℤ) :
    genericKept (guardReseat P seat label) t=
      untouched Finset.univ (vertexOwner seat)
        (matchedColumns Finset.univ (realSlot seat) (realSlot seat) t) := rfl

theorem guarded_same_cells {N : Network (U×Bool) A U} (P : PhysicalPacking N a G)
    (ha : 0<a)
    (cap : ∀ c, Nat.card (RealFiber (declaredCell N P.rowLabel P.colLabel) c)≤P.copies*2^a) :
    ∃ Q : PhysicalPacking N a G,
      Q.rowLabel=P.rowLabel ∧ Q.colLabel=P.colLabel ∧ Q.copies=P.copies ∧
      ∀ (t : ℤ), t≠0 →
      (Fintype.card U:ℝ)/((2^a:ℕ):ℝ)≤
        ((genericKept Q t).card:ℝ)+Real.sqrt (5*(2*(Fintype.card U:ℝ))/((2^a:ℕ):ℝ))+
          Real.sqrt ((Fintype.card (Cell (Fin a) G):ℝ)*(5*(2*(Fintype.card U:ℝ))/((2^a:ℕ):ℝ))) := by
  obtain ⟨seat,labels,h⟩ := guarded_real_layout (b:=P.copies) ha
    (fun (u : U) (x : Bool) => declaredCell N P.rowLabel P.colLabel (u,x)) cap
  refine ⟨guardReseat P seat labels,rfl,rfl,rfl,?_⟩
  intro t ht
  rw [reseat_kept]
  exact h Finset.univ t ht
end Generic

variable {W : Type} [Fintype W] [DecidableEq W]
variable {F : Finset (W×W)} {reg : ∀ v,GraphCutMoments.degree F v=3}
variable {a : ℕ} [Nonempty (MainClonedCNF.Port F)]
local notation "C" => (MainClonedCNF.Port F)
local notation "Pack" => (PhysicalPacking (dNetwork F reg) a (Fin 64))

theorem real_kept_eq (P : Pack) (t : ℤ) :
    genericKept P t=actualKept P t := by
  unfold genericKept actualKept kept
  rw [row_real_is_seat P.seat,col_real_is_seat P.seat]
  ext c
  simp only [untouched,Finset.mem_sdiff,Finset.mem_image]

theorem all_shift_guarded_packing (ha : 0<a) (P : Pack) :
    ∃ Q : Pack,
      Q.rowLabel=P.rowLabel ∧ Q.colLabel=P.colLabel ∧ Q.copies=P.copies ∧
      ∀ (t : ℤ), t≠0 →
        (Fintype.card C:ℝ)/((2^a:ℕ):ℝ) ≤ ((actualKept Q t).card:ℝ)+errBudget F a := by
  obtain ⟨Q,hr,hc,hb,hg⟩ := guarded_same_cells P ha (actual_cell_cap P)
  refine ⟨Q,hr,hc,hb,?_⟩
  intro t ht
  have h := hg t ht
  rw [real_kept_eq] at h
  unfold errBudget
  linarith only [h]

#print axioms row_real_is_seat
#print axioms col_real_is_seat
#print axioms guarded_same_cells
#print axioms real_kept_eq
#print axioms all_shift_guarded_packing
end
end J2R43LiteralWholeMenu