import P5HybridDUnclonedRoot
import P5HybridDUnclonedPacking
import P5D1LiteralRoot

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 27000000
set_option maxRecDepth 2400

/-! The uncloned completion of Paper 5 §8. The same graph-only packing
supplies both actual retained coordinates of the original source root,
with exact count proved for its own tensor file for every sign word. -/
namespace Paper5.HybridDUncloned
open scoped Classical BigOperators Polynomial
open Polynomial J6R10Repack J6R9Recursive J6R11Blueprint J6ActiveRun J6R12Blueprint
  J1PPrinted P11FullPacking Paper5.HybridClosure Paper5.D1Literal

noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]
variable (E : Finset (V×V)) (baseCubic : ∀v,GraphCutMoments.degree E v=3)
variable (loopless : ∀v,(v,v)∉E)
variable (f : ℤ[X])
local notation "F" => replacedEdges E baseCubic
local notation "reg" => replaced_cubic E baseCubic loopless
local notation "n" => Fintype.card (TriVertex V)
local notation "N" => network F reg
local notation "S" => sourceSize F
local notation "a" => rootBits S
local notation "Delta" => sourceDelta S
local notation "SP" => printedParams (f:=f) (ell:=1) S
local notation "M" => Nat.card (Wire F)

theorem printed_uncloned_two_D_coordinates
    (positive : 0<n) (width : 2≤rootWidth S)
    (large : (2*epsDen)^30*(3:ℕ)^10≤Nat.clog 2 S)
    (degree : f.natDegree=4*Nat.clog 2 S) :
    ∃ (P : PhysicalPacking N a (Fin 64)) (exterior triangle : Fin a)
      (monoT : ∀e∈innerEdges V,realPinGroup F reg P triangle e.1=realPinGroup F reg P triangle e.2)
      (monoE : ∀e∈outerEdges E baseCubic,
        realPinGroup F reg P exterior e.1=realPinGroup F reg P exterior e.2),
      exterior.val=1 ∧ triangle.val=0 ∧ exterior≠triangle ∧
      P.copies=ceilCopies (2^a) (maxFiber (declaredCell N P.rowLabel P.colLabel)) ∧
      varianceScore (declaredCell N P.rowLabel P.colLabel)≤4*(M:ℚ)+3*n ∧
      varianceScore (declaredCell N P.rowLabel P.colLabel)≤2*(M:ℚ)*Delta ∧
      Nat.card (Page a P.copies (Fin 64))*2^a≤3*M ∧
      (∀ j g,Nat.card (rowsIn N (declaredGroup P.rowLabel P.colLabel j) g)≤3*M/64 ∧
             Nat.card (colsIn N (declaredGroup P.rowLabel P.colLabel j) g)≤3*M/64) ∧
      ∀ (σ : TriVertex V→Bool) (hf : f.Monic),
        let r := root F reg f σ
        let value :=
          (∏ g : Fin 64,groupOperand (innerEdges V) (realPinGroup F reg P triangle) monoT g
            (σ∘Subtype.val)) *
          (∏ g : Fin 64,groupOperand (outerEdges E baseCubic) (realPinGroup F reg P exterior) monoE g
            (σ∘Subtype.val))
        ∃ (d : Ready SP Delta r) (tT tE : Center SP r),
          centerIndex d tT=triangle ∧ centerIndex d tE=exterior ∧
          packing (sameRootSelector SP Delta r P) d=P ∧
          PinnedCNF.modelCount (PinnedCNF.formula F σ)=value ∧
          reduce r.prec f 1 (r.host.contract hf)=(value:Residue f 1 r.prec) := by
  have tune := source_actual_tune F reg positive width
  have hA : a=2*rootWidth S := (printed_dimension_words S).1
  let ext : Fin a := ⟨1,by omega⟩
  let tri : Fin a := ⟨0,by omega⟩
  have neq : ext≠tri := by
    intro eq
    have h := congrArg Fin.val eq
    change 1=0 at h
    omega
  have hCell : 2*(J9PrintedSchedule.arrayCard a)^2*Delta≤M := by
    simpa only [Nat.card_eq_fintype_card] using tune.collision
  have hSlot : 2^a*J9PrintedSchedule.arrayCard a≤M := by
    simpa only [Nat.card_eq_fintype_card] using tune.slots
  obtain ⟨P,cT,cE,hT,hE,hRound,hScore,hPhi,hPages,hGroups⟩ :=
    on_same_uncloned_D_packing E baseCubic loopless ext tri neq Delta tune.degree hCell hSlot
  have monoT : ∀e∈innerEdges V,realPinGroup F reg P tri e.1=realPinGroup F reg P tri e.2 := by
    intro e he
    exact (hT e.1).trans ((main_inner_monochromatic cT e he).trans (hT e.2).symm)
  have monoE : ∀e∈outerEdges E baseCubic,
      realPinGroup F reg P ext e.1=realPinGroup F reg P ext e.2 := by
    intro e he
    exact (hE e.1).trans ((d_outer_monochromatic E baseCubic cE e he).trans (hE e.2).symm)
  refine ⟨P,ext,tri,monoT,monoE,rfl,rfl,neq,hRound,hScore,hPhi,hPages,hGroups,?_⟩
  intro σ hf
  let r := root F reg f σ
  let d := root_ready F reg σ degree large tune
  obtain ⟨tT,htT⟩ := root_literal_center_at_level F reg σ d ⟨0,by omega⟩
  obtain ⟨tE,htE⟩ := root_literal_center_at_level F reg σ d ⟨1,by omega⟩
  have exactNat := true_uncloned_bucket_count E baseCubic loopless _ _ monoT monoE σ
  refine ⟨d,tT,tE,Fin.ext htT,Fin.ext htE,sameRootSelector_pins SP Delta r P d,exactNat,?_⟩
  have eq := root_literal_count F reg f hf σ
  dsimp only at eq
  rw [exactNat] at eq
  exact eq

#print axioms printed_uncloned_two_D_coordinates
end
end Paper5.HybridDUncloned
