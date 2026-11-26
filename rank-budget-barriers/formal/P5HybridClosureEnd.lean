import P5HybridClosureActual
import P5HybridClosureAffineLayout
import P5HybridClosureLiteral

/-! §8 joint finite certificate. The same literal group coordinates are
used in the cheap product and in the allowed affine term family. This
does not claim the two operands are native Taylor/child readouts. -/
namespace Paper5.HybridClosure
open scoped BigOperators Classical
open J1MainSourceLabels J6R10Repack
open DiagonalAbundance (Draw)
open GraphCutMoments EmpiricalCutMoments CommonMatchingSelection GroupProducts SeparatedRank

section Literal
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {TM TD R S K : Type*} [Fintype TM] [Fintype TD]
  [CommRing R] [CommRing S] [Nontrivial S] [Field K]
variable (E : Finset (V×V)) (cubic : ∀v,degree E v=3)
variable (loopless : ∀v,(v,v)∉E)

local notation "F" => replacedEdges E cubic
local notation "reg" => replaced_cubic E cubic loopless
local notation "N" => dNetwork F reg

noncomputable abbrev clonedCount (σ : TriVertex V→Bool) : ℕ :=
  PinnedCNF.modelCount (MainClonedCNF.formula F (MainClonedCNF.leftSlot F reg)
    (MainClonedCNF.rightSlot F reg) σ)

set_option maxHeartbeats 8000000 in
theorem checked_finite_E1 (γ : ℚ) (hγ : 0<γ) (hγ₃ : γ≤3)
    (expand : ∀ U : Finset V, γ*(min U.card (Fintype.card V-U.card):ℕ)≤
      ((boundary E U).card:ℚ))
    (Q r a Δ : ℕ) (t : Fin Q) (hr : 32≤r) (kept : Finset (Fin a)) (i : kept) (hΔ : 3≤Δ)
    (hMcell : 2*5*(r^(2*Q))^2≤12*Fintype.card (TriVertex V))
    (hMgrp : 2*Q*r^2≤4*Fintype.card (TriVertex V))
    (hDcell : 2*(J9PrintedSchedule.arrayCard a)^2*Δ≤Nat.card (DWire F))
    (hDslot : 2^a*J9PrintedSchedule.arrayCard a≤Nat.card (DWire F))
    (hbudget : 31104*((Q:ℚ)^2+(kept.card:ℚ)^2)<
      (matchingCoeff (γ/3))^2*(Fintype.card (TriVertex V):ℚ)) :
    ∃ (z : MainPrimitives F (Fin Q)→Fin r) (P : PhysicalPacking N a (Fin 64))
      (cM : V→Fin r) (cD : E→Fin 64),
      let L_M := MainPinLabels E cubic t z
      let L_D := DPinLabels E cubic loopless P kept
      let dM := routeDepth (γ/3) (Fintype.card (TriVertex V)) Q
      let dD := routeDepth (γ/3) (Fintype.card (TriVertex V)) kept.card
      (∀p,L_M p t=mainPinColor cM p) ∧
      (∀p,L_D p i=dPinColor E cubic cD p) ∧
      MainSeatCertificate F reg t z (2*(12*(Fintype.card (TriVertex V):ℚ))/
        (Fintype.card (Draw (Fin Q) (Fin r)):ℚ)) ∧
      (∃ (monoM : ∀e∈innerEdges V,L_M e.1 t=L_M e.2 t)
        (monoD : ∀e∈outerEdges E cubic,L_D e.1 i=L_D e.2 i),
        ∀σ,clonedCount E cubic loopless σ =
          (∏g : Fin r, groupOperand (innerEdges V) (fun p=>L_M p t) monoM g (σ ∘ Subtype.val))*
          (∏h : Fin 64,groupOperand (outerEdges E cubic) (fun p=>L_D p i) monoD h (σ ∘ Subtype.val))) ∧
      (∀σ,boolAsNat (twoMethodScan E cubic cM cD σ).1=clonedCount E cubic loopless σ ∧
        (twoMethodScan E cubic cM cD σ).2≤7*Fintype.card (TriVertex V)+65) ∧
      (∃ (sM : Fin Q→Finset (Fin r)) (sD : kept→Finset (Fin 64)) (mark orientation : F→Bool),
        let matching := MatchingThinning.matching F (replaced_loopless E cubic loopless) mark orientation
        (∀j,dM≤endpointImbalance matching.endpoint (labelCut L_M id sM j)) ∧
        (∀j,dD≤endpointImbalance matching.endpoint (labelCut L_D id sD j)) ∧
        ∀ (terms_M : TM→GroupTerm L_M K) (terms_D : TD→GroupTerm L_D K)
          (embed : R→+*K) (residue : R→+*S) (_hinj : Function.Injective embed)
          (output : (TriVertex V→Bool)→R),
        (∀σ,embed (output σ)=(∑t,(terms_M t).value σ)+∑t,(terms_D t).value σ) →
        (∀σ,residue (output σ)=(clonedCount E cubic loopless σ:S)) →
        ((1:ℚ)≤(Fintype.card TM:ℚ)/(2:ℚ)^dM+(Fintype.card TD:ℚ)/(2:ℚ)^dD) ∧
          2^(min dM dD)≤Fintype.card TM+Fintype.card TD) := by
  letI : Nonempty (Fin Q) := ⟨t⟩
  letI : Nonempty (Fin r) := ⟨⟨0,by omega⟩⟩
  letI : Nonempty kept := ⟨i⟩
  obtain ⟨z,zd,P,h_tieM,h_tieD,h_domM,h_domD,h_seats,_groups,_packets,_ports,h_count⟩ :=
    actual_joint_tied_layouts E cubic loopless Q r a Δ t (by omega) kept i hΔ hMcell hMgrp hDcell hDslot
  let cM := fun v : V=>z (.inr (.inr v))
  let cD := fun e : E=>zd (.inr (.inr e))
  refine ⟨z,P,cM,cD,h_tieM,h_tieD,h_seats,?_,?_,?_⟩
  · exact literal_source_group_factorization E cubic loopless cM cD _ _ h_tieM h_tieD
  · intro σ
    obtain ⟨h,hcost⟩ := h_count σ
    refine ⟨h,?_⟩
    rw [hcost]
    exact word_time_linear_of_source_feasible _ Q r Fintype.card_pos (Nat.zero_lt_of_lt t.isLt) hMgrp
  · have hlb := fixed_affine_after_layout_choice (TM:=TM) (TD:=TD) (R:=R) (S:=S) (K:=K)
      F (replaced_loopless E cubic loopless) reg (MainPinLabels E cubic t z)
      (DPinLabels E cubic loopless P kept) (γ/3) (by positivity) (by linarith only [hγ₃])
      (replacement_expansion E cubic loopless γ hγ.le hγ₃ expand) h_domM h_domD
      (by simpa only [Fintype.card_fin] using hr) (by simp)
      (by simpa only [Fintype.card_fin,Fintype.card_coe] using hbudget)
    simpa only [Fintype.card_fin,Fintype.card_coe] using hlb
end Literal

#print axioms checked_finite_E1
end Paper5.HybridClosure