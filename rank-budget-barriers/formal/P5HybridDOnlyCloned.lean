import P5HybridDOnlyLayout
import P5HybridDOnlyGeometry

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 9500000

/-! The two specified coordinates are on one physical four-clone
Appendix D root. Triangle tags attach only to real unary wires; the
other old tables and the subdivision labels remain independent. -/
namespace Paper5.HybridDOnly
open scoped Classical BigOperators
open Paper5.HybridClosure J1MainSourceCollision DiagonalAbundance
open J6R10Repack J6R11CollisionReindex P11FullPacking EmpiricalCutMoments ProductVariance

section Original

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable (E : Finset (V×V)) (cubic : ∀v,GraphCutMoments.degree E v=3)
variable (loopless : ∀v,(v,v)∉E)
local notation "F" => replacedEdges E cubic
local notation "reg" => replaced_cubic E cubic loopless
local notation "N" => dNetwork F reg
local notation "ν" => Fintype.card (TriVertex V)

theorem on_same_cloned_D_packing {a : ℕ} (exterior triangle : Fin a) (distinct : exterior≠triangle)
    (kept : Finset (Fin a)) (Δ : ℕ) (hΔ : 3≤Δ)
    (hcollision : 2*(J9PrintedSchedule.arrayCard a)^2*Δ≤24*ν)
    (hslots : 2^a*J9PrintedSchedule.arrayCard a≤24*ν) :
    ∃ (P : PhysicalPacking N a (Fin 64)) (cT : V→Fin 64) (cE : E→Fin 64),
      (∀ p, P.rowLabel (.inr (.inl p)) exterior = dPinColor E cubic cE p) ∧
      (∀ p, P.rowLabel (.inr (.inl p)) triangle = mainPinColor cT p) ∧
      P.copies=ceilCopies (2^a) (maxFiber (declaredCell N P.rowLabel P.colLabel)) ∧
      varianceScore (declaredCell N P.rowLabel P.colLabel)≤4*(24*(ν:ℚ))+3*ν ∧
      varianceScore (declaredCell N P.rowLabel P.colLabel)≤2*(24*(ν:ℚ))*Δ ∧
      (∀ c, load (J6R11Collision.edgeCell (N).row (N).col (P.rowLabel,P.colLabel)) c ≤
        2*(24*(ν:ℚ))/(Fintype.card (Draw (Fin a) (Fin 64)):ℚ)) ∧
      Nat.card (Page a P.copies (Fin 64))*2^a≤3*(24*ν) ∧
      (∀ j g, Nat.card (rowsIn N (declaredGroup P.rowLabel P.colLabel j) g)≤3*(24*ν)/64 ∧
        Nat.card (colsIn N (declaredGroup P.rowLabel P.colLabel j) g)≤3*(24*ν)/64) ∧
      (∀ x,empiricalLaw (DPinLabels E cubic loopless P kept) x≤48*uniformWeight (kept→Fin 64)) := by
  let dV : DecidableEq V := ‹DecidableEq V›
  let dW : DecidableEq (TriVertex V) := @instDecidableEqProd V (Fin 3) dV (instDecidableEqFin 3)
  let dClone : DecidableEq (Clone (TriVertex V)) :=
    @instDecidableEqProd (TriVertex V) (Fin 4) dW (instDecidableEqFin 4)
  let dF : DecidableEq (↥F) := @Subtype.instDecidableEq (TriVertex V×TriVertex V) _
    (@instDecidableEqProd _ _ dW dW)
  let dRow : DecidableEq (DOld F) :=
    @instDecidableEqSum (Clone (TriVertex V)) (ClauseIndex F) dClone
      (@instDecidableEqSum (TriVertex V) (↥F⊕Clone (TriVertex V)) dW
        (@instDecidableEqSum (↥F) (Clone (TriVertex V)) dF dClone))
  let dCol : DecidableEq (MainClonedCNF.Port F) :=
    @instDecidableEqSum (TriVertex V) ((↥F×Bool)⊕(TriVertex V×Fin 4×Bool)) dW
      (@instDecidableEqSum _ _
        (@instDecidableEqProd _ _ dF instDecidableEqBool)
        (@instDecidableEqProd _ _ dW
          (@instDecidableEqProd _ _ (instDecidableEqFin 4) instDecidableEqBool)))
  let dExterior : DecidableEq (↥E) := @Subtype.instDecidableEq (V×V) _
    (@instDecidableEqProd _ _ dV dV)
  have hm : Nat.card (DWire F)=24*ν := by
    rw [Nat.card_eq_fintype_card,d_physical_wire_count F reg]
  obtain ⟨cfg,P,pr,_pc,pp,pex,pΦ,pn,pg⟩ :=
    @same_packing_with_both_ties (DWire F) (DOld F) (MainClonedCNF.Port F) V (↥E)
      inferInstance (Classical.decEq _) inferInstance dRow inferInstance dCol inferInstance dV
      inferInstance dExterior a N exterior triangle
    (innerTie E cubic) (exteriorTie E cubic) ν Δ
    (fun q=>(d_subdivision_degree F reg q).le) (d_old_degree F reg)
    (fun v=>(cloned_inner_fibre E cubic loopless v).le) (d_tied_fibre E cubic loopless)
    (cloned_inner_slots E cubic loopless).le (d_tied_slots E cubic loopless).le
    (by rw [hm]; omega) hΔ (by rwa [hm]) (by rwa [hm])
  let cT : V→Fin 64 := fun v=>cfg (.inl (.inr (.inl v)),triangle)
  let cE : E→Fin 64 := fun e=>cfg (.inl (.inr (.inr e)),exterior)
  have dLoad := native_ordered_cell_load N P Δ pΦ (by rwa [hm])
  have hm' : (Nat.card (DWire F):ℚ)=24*(ν:ℚ) := by exact_mod_cast hm
  have hf' : (Fintype.card (DWire F):ℚ)=24*(ν:ℚ) := by exact_mod_cast d_physical_wire_count F reg
  have hw : 2*Fintype.card (DWire F)≤48*ν := by rw [d_physical_wire_count F reg]; omega
  refine ⟨P,cT,cE,?_,?_,pp,?_,?_,?_,?_,?_,?_⟩
  · intro v
    rw [pr]
    simp [rowWord,tiedAtom,twoTags_at_exterior,exteriorTie,cE,dPinColor]
  · intro v
    rw [pr]
    simp [rowWord,tiedAtom,twoTags_at_triangle distinct,innerTie,cT,mainPinColor]
  · simpa only [hm'] using pex
  · simpa only [hm'] using pΦ
  · intro c
    simpa only [hf'] using dLoad c
  · simpa only [hm] using pn
  · simpa only [hm] using pg
  · exact retained_pin_domination (⟨pinWire E cubic,pinWire_injective E cubic⟩)
      (J6R11Collision.edgeCell (N).row (N).col (P.rowLabel,P.colLabel)) 48 hw kept dLoad

end Original

#print axioms on_same_cloned_D_packing
end Paper5.HybridDOnly
