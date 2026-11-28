import P5D1LiteralTrace
import P5HybridClosureAffineLayout

/-! The official joint layout selector may first choose P, after which
the real D1 slot carrier is instantiated. The concrete count and cost
do not quantify a fixed menu type in advance of the packing. -/
namespace Paper5.D1Literal
open scoped Classical Polynomial BigOperators
open Polynomial J6R10Repack J6R11Repack J6R11Blueprint J6ActiveRun
  J6R12Blueprint J6R10Reachable J6R9Recursive J6R9PacketScopes
  P11FullPacking Paper5.HybridClosure J1PPrinted J6R12Integral
  GroupProducts SeparatedRank GraphCutMoments EmpiricalCutMoments

variable {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
variable (E : Finset (V × V)) (reg₀ : ∀ v,degree E v = 3)
variable (loop₀ : ∀ v,(v,v)∉E)
variable (f : ℤ[X])
local notation "F" => replacedEdges E reg₀
local notation "reg" => replaced_cubic E reg₀ loop₀
local notation "Ws" => Fintype.card (TriVertex V)
local notation "SP" => (printedParams (f:=f) (ell:=1) (oldRowSize F))
local notation "Δ" => sourceDelta (oldRowSize F)
local notation "r*" => (oldRowRoot F reg f (fun _ => false))
local notation "J" => rootKept F f

set_option maxHeartbeats 20000000 in
/-- On the very same graph-only jointly certified packing and the original
24N-wire orientation, all root slots incur the conditional materialized
cost. Unconditional content is only the number of legal root products. -/
theorem oldRow_joint_E1_exact_menu
    (cfg : RootBounds (oldRowSize F) 3 f) (hΔ : 3 ≤ Δ) (ha : (SP).cutoff < Fintype.card (DWire F))
    (hf : f.Monic) (hF : 0 < f.natDegree) [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (γ : ℚ) (hγ : 0<γ) (hγ₃ : γ≤3)
    (expand : ∀ U : Finset V, γ*(min U.card (Fintype.card V-U.card):ℕ)≤
      ((boundary E U).card:ℚ))
    (Q r : ℕ) (t : Fin Q) (hr : 32≤r) (i : J)
    (hMcell : 2*5*(r^(2*Q))^2≤12*Ws) (hMgrp : 2*Q*r^2≤4*Ws)
    (hDcell : 2*(J9PrintedSchedule.arrayCard ((SP).levelBits 0))^2*Δ≤Nat.card (DWire F))
    (hDslot : 2^((SP).levelBits 0)*J9PrintedSchedule.arrayCard ((SP).levelBits 0)≤Nat.card (DWire F))
    (hbudget : 31104*((Q:ℚ)^2+((J).card:ℚ)^2)<
      (matchingCoeff (γ/3))^2*(Ws:ℚ)) :
    ∃ (z : MainPrimitives F (Fin Q)→Fin r)
      (zd : DPrimitives E reg₀ ((SP).levelBits 0)→Fin 64)
      (P : RootPacking F reg f),
      let d : Ready SP Δ r* := getReady cfg (oldRowRoot_stable F reg f _ hΔ) ha
      let D := routeDepth (γ/3) Ws (J).card
      (∀ v, MainPinLabels E reg₀ t z v t = mainPinColor (fun w => z (.inr (.inr w))) v) ∧
      (∀ v, rootLabels F reg f P v i = dPinColor E reg₀ (fun w => zd (.inr (.inr w))) v) ∧
      2^D ≤ Fintype.card (PublicSlot F reg f P d) ∧
      ∀ trace : FixedSchedule.Execution (PublicSlot F reg f P d), 2^D ≤ trace.cost := by
  classical
  letI : Nonempty (Fin Q) := ⟨t⟩
  letI : Nonempty (Fin r) := ⟨⟨0,by omega⟩⟩
  letI : Nonempty ↥(J) := ⟨i⟩
  letI : Fact (Irreducible (ratPoly f)) := ⟨source_rat_irreducible f hf Fact.out⟩
  let d : Ready SP Δ r* := getReady cfg (oldRowRoot_stable F reg f _ hΔ) ha
  obtain ⟨z,zd,P,mt,dt,dm,dd,_⟩ :=
    actual_joint_tied_layouts E reg₀ loop₀ Q r ((SP).levelBits 0) Δ t (by omega) J i
      hΔ hMcell hMgrp hDcell hDslot
  obtain ⟨s_M,s_D,mark,orientation,_,hD,_⟩ :=
    fixed_affine_after_layout_choice (TM:=Fin 0) (TD:=Fin 0) (R:=IntRing f 1)
      (S:=NativeProbeRing.Residue f) (K:=RatScalar f) F (replaced_loopless E reg₀ loop₀) reg
      (MainPinLabels E reg₀ t z) (rootLabels F reg f P) (γ/3)
      (by positivity) (by linarith only [hγ₃])
      (replacement_expansion E reg₀ loop₀ γ hγ.le hγ₃ expand)
      dm dd (by simpa only [Fintype.card_fin] using hr) (by simp)
      (by simpa only [Fintype.card_fin,Fintype.card_coe] using hbudget)
  let matching := MatchingThinning.matching F (replaced_loopless E reg₀ loop₀) mark orientation
  let D := routeDepth (γ/3) Ws (J).card
  have hgap : ∀ j, D ≤ endpointImbalance matching.endpoint
      (labelCut (rootLabels F reg f P) id s_D j) := by
    simpa only [D,Fintype.card_coe] using hD
  have hsmall : D ≤ Fintype.card (MatchingThinning.Kept F mark) :=
    (hgap i).trans (endpoint_imbalance_le matching.endpoint _)
  have hcard : 2^D ≤ Fintype.card (PublicSlot F reg f P d) :=
    literal_menu_card_from_matching F reg f P cfg hΔ hf hF d matching s_D D hsmall hgap
  exact ⟨z,zd,P,mt,dt,hcard,fun trace => hcard.trans (FixedSchedule.card_le_cost trace)⟩

#print axioms oldRow_joint_E1_exact_menu
end Paper5.D1Literal
