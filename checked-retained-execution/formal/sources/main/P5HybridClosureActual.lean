import P5HybridClosureDPack
import P5HybridClosureDensity
import P5HybridClosureScan
import P5HybridClosureMainSeats

/-! The two graph-only choices on exactly the same cloned clause list.
The returned pin labels are literal factor/subdivided-network labels;
the nonlinear operands receive only the indicated sign groups. -/
namespace Paper5.HybridClosure
open scoped BigOperators Classical
open J1MainSourceLabels J1MainSourceCollision J6R10Repack J6R11CollisionReindex P11FullPacking
open DiagonalAbundance (Draw)
open EmpiricalCutMoments ProductVariance

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable (E : Finset (V×V)) (cubic : ∀v,GraphCutMoments.degree E v=3)
variable (loopless : ∀v,(v,v)∉E)

local notation "F" => replacedEdges E cubic
local notation "reg" => replaced_cubic E cubic loopless
local notation "N" => dNetwork F reg

noncomputable abbrev MainPinLabels {Q r : ℕ} (t : Fin Q) (z : MainPrimitives F (Fin Q)→Fin r)
    (p : TriVertex V) : Fin Q→Fin r :=
  factorWord t triangleTie z (.inl p)

noncomputable abbrev DPinLabels {a : ℕ} (P : PhysicalPacking N a (Fin 64)) (kept : Finset (Fin a))
    (p : TriVertex V) : kept→Fin 64 := fun j=>P.rowLabel (.inr (.inl p)) j.1

set_option maxHeartbeats 4000000 in
theorem actual_joint_tied_layouts (Q r a Δ : ℕ) (t : Fin Q) (hr : 0<r)
    (kept : Finset (Fin a)) (i : kept) (hΔ : 3≤Δ)
    (hMcell : 2*5*(r^(2*Q))^2≤12*Fintype.card (TriVertex V))
    (hMgrp : 2*Q*r^2≤4*Fintype.card (TriVertex V))
    (hDcell : 2*(J9PrintedSchedule.arrayCard a)^2*Δ≤Nat.card (DWire F))
    (hDslot : 2^a*J9PrintedSchedule.arrayCard a≤Nat.card (DWire F)) :
    ∃ (z : MainPrimitives F (Fin Q)→Fin r) (zd : DPrimitives E cubic a→Fin 64)
      (P : PhysicalPacking N a (Fin 64)),
      let cM := fun v : V => z (.inr (.inr v))
      let cD := fun e : E => zd (.inr (.inr e))
      (∀p,MainPinLabels E cubic t z p t = mainPinColor cM p) ∧
      (∀p,DPinLabels E cubic loopless P kept p i = dPinColor E cubic cD p) ∧
      (∀ x,empiricalLaw (MainPinLabels E cubic t z) x≤24*uniformWeight (Fin Q→Fin r)) ∧
      (∀ x,empiricalLaw (DPinLabels E cubic loopless P kept) x≤48*uniformWeight (kept→Fin 64)) ∧
      MainSeatCertificate F reg t z (2*(12*(Fintype.card (TriVertex V):ℚ))/
        (Fintype.card (Draw (Fin Q) (Fin r)):ℚ)) ∧
      (∀ j g,load (fun p : Clone (TriVertex V) => variableWord z p j) g≤
        2*(4*(Fintype.card (TriVertex V):ℚ))/(r:ℚ)) ∧
      Nat.card (Page a P.copies (Fin 64))*2^a≤3*Nat.card (DWire F) ∧
      (∀ j g,
        Nat.card (rowsIn N (declaredGroup P.rowLabel P.colLabel j) g)≤3*Nat.card (DWire F)/64 ∧
        Nat.card (colsIn N (declaredGroup P.rowLabel P.colLabel j) g)≤3*Nat.card (DWire F)/64) ∧
      (∀σ,
        boolAsNat (twoMethodScan E cubic cM cD σ).1=
          PinnedCNF.modelCount (MainClonedCNF.formula F (MainClonedCNF.leftSlot F reg)
            (MainClonedCNF.rightSlot F reg) σ) ∧
        (twoMethodScan E cubic cM cD σ).2=6*Fintype.card (TriVertex V)+r+64+1) := by
  letI : Nonempty (Fin Q) := ⟨t⟩
  letI : Nonempty (Fin r) := ⟨⟨0,hr⟩⟩
  have hMC : (Fintype.card (Draw (Fin Q) (Fin r)))=r^(2*Q) := J6R11Collision.source_word_cells r Q
  have hMc : 2*5*(Fintype.card (Draw (Fin Q) (Fin r)):ℚ)^2 ≤
      12*(Fintype.card (TriVertex V):ℚ) := by
    rw [hMC]
    -- The source condition tests D_M², where D_M is the word-cell count.
    exact_mod_cast hMcell
  have hMg : 2*(Fintype.card (Fin Q):ℚ)*(Fintype.card (Fin r):ℚ)^2 ≤
      4*(Fintype.card (TriVertex V):ℚ) := by
    simp only [Fintype.card_fin]
    exact_mod_cast hMgrp
  obtain ⟨z,ztied,zCell,zGrp⟩ := main_actual_tied_placement (I:=Fin Q) (S:=Fin r) F reg t hMc hMg
  obtain ⟨zd,P,dtied,_dcopy,dDev⟩ := d_actual_tied_packing E cubic loopless i.1 Δ hΔ hDcell hDslot
  let pin : TriVertex V↪DWire F := ⟨pinWire E cubic,pinWire_injective E cubic⟩
  let dCell := J6R11Collision.edgeCell (N).row (N).col (P.rowLabel,P.colLabel)
  have dvar : deviation dCell≤2*(Fintype.card (DWire F):ℚ)*Δ := by
    rw [declared_variance_eq N (P.rowLabel,P.colLabel)] at dDev
    rw [Nat.card_eq_fintype_card] at dDev
    exact dDev
  have dNum : 2*(Δ:ℚ)*(Fintype.card ((Fin a→Fin 64)×(Fin a→Fin 64)):ℚ)^2≤
      (Fintype.card (DWire F):ℚ) := by
    rw [J6R11Collision.source_word_cells 64 a]
    have hD : 2*(64^(2*a))^2*Δ≤Fintype.card (DWire F) := by
      simpa [J9PrintedSchedule.arrayCard,Nat.card_eq_fintype_card,pow_mul,mul_comm,mul_left_comm] using hDcell
    have hD' : 2*Δ*(64^(2*a))^2≤Fintype.card (DWire F) := by
      calc
        _ = 2*(64^(2*a))^2*Δ := by ac_rfl
        _ ≤ _ := hD
    exact_mod_cast hD'
  have dLoad (c : (Fin a→Fin 64)×(Fin a→Fin 64)) :=
    deviation_load_bound dCell Δ dvar dNum c
  have dSize : 2*Fintype.card (DWire F)≤48*Fintype.card (TriVertex V) := by
    rw [d_physical_wire_count F reg]
    omega
  have mSize : 2*Fintype.card (MainClonedCNF.Port F)≤24*Fintype.card (TriVertex V) := by
    rw [MainClonedCNF.port_card F reg]
    omega
  let mCell := literalCell t triangleTie (cloneOwner F reg) (cloneFactor F) z
  have mLoad (c : Draw (Fin Q) (Fin r)) : load mCell c≤
      2*(Fintype.card (MainClonedCNF.Port F):ℚ)/(Fintype.card (Draw (Fin Q) (Fin r)):ℚ) := by
    have h : (Fintype.card (MainClonedCNF.Port F):ℚ)=12*(Fintype.card (TriVertex V):ℚ) := by
      exact_mod_cast MainClonedCNF.port_card F reg
    rw [h]
    exact zCell c
  refine ⟨z,zd,P,ztied,dtied,?_,?_,actual_main_seats F reg t z _ zCell,?_,physical_packet_count P,?_,?_⟩
  · exact main_pin_domination (MainClonedCNF.pinPort F) mCell 24 mSize mLoad
  · exact retained_pin_domination pin dCell 48 dSize kept dLoad
  · intro j g
    simpa only [Fintype.card_fin] using zGrp j g
  · exact physical_group_caps P (by simp)
  · intro σ
    simpa only [Fintype.card_fin] using twoMethodScan_exact E cubic loopless
      (fun v=>z (.inr (.inr v))) (fun e=>zd (.inr (.inr e))) (MainClonedCNF.leftSlot F reg)
      (MainClonedCNF.rightSlot F reg) σ

#print axioms actual_joint_tied_layouts
end Paper5.HybridClosure