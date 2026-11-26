import P5D1LiteralLedgerLower
import P5D1LiteralEventual

namespace Paper5.D1Literal
open scoped Classical Polynomial BigOperators
open Polynomial J6R10Repack J6R11Repack J6R11Blueprint J6ActiveRun
  J6R12Blueprint J6R10Reachable J6R9Recursive J6R9PacketScopes
  P11FullPacking Paper5.HybridClosure J1PPrinted J6R12Integral
  GroupProducts SeparatedRank GraphCutMoments EmpiricalCutMoments
open ProductVariance J1MainSourceCollision
open Paper5.HybridClosure.Printed (dLambda dU printedExponent printed_exp_term_count mainQ)

variable {W : Type} [Fintype W] [DecidableEq W] [Nonempty W]
variable (F : Finset (W × W)) (reg : ∀ v,degree F v=3)
variable (f : ℤ[X])
local notation "N" => Fintype.card W
local notation "S" => (printedParams (f:=f) (ell:=1) (oldRowSize F))
local notation "Δ" => sourceDelta (oldRowSize F)
local notation "r*" => (oldRowRoot F reg f (fun _ => false))
local notation "J" => rootKept F f

/-- Squared deviations of the actual source row and column word cells. -/
def CollisionBound (P : RootPacking F reg f) : Prop :=
  deviation (J6R11Collision.edgeCell (dNetwork F reg).row (dNetwork F reg).col
    (P.rowLabel,P.colLabel)) ≤ 2*(Fintype.card (DWire F):ℚ)*Δ

theorem every_packing_pin_domination (P : RootPacking F reg f)
    (h : CollisionBound F reg f P)
    (hcell : 2*(J9PrintedSchedule.arrayCard ((S).levelBits 0))^2*Δ≤Nat.card (DWire F)) :
    ∀ x,empiricalLaw (rootLabels F reg f P) x≤48*uniformWeight (↥J→Fin 64) := by
  classical
  let a := (S).levelBits 0
  let cell := J6R11Collision.edgeCell (dNetwork F reg).row (dNetwork F reg).col
    (P.rowLabel,P.colLabel)
  let pin : W ↪ DWire F := ⟨fun v => (.inl v,true),
    fun _ _ he => Sum.inl.inj (congrArg Prod.fst he)⟩
  have hn : 2*(Δ:ℚ)*(Fintype.card ((Fin a→Fin 64)×(Fin a→Fin 64)):ℚ)^2≤
      (Fintype.card (DWire F):ℚ) := by
    rw [J6R11Collision.source_word_cells 64 a]
    have hD : 2*(64^(2*a))^2*Δ≤Fintype.card (DWire F) := by
      simpa [a,J9PrintedSchedule.arrayCard,Nat.card_eq_fintype_card,pow_mul,mul_comm,mul_left_comm] using hcell
    have hh : 2*Δ*(64^(2*a))^2≤Fintype.card (DWire F) := by
      calc
        _ = 2*(64^(2*a))^2*Δ := by ac_rfl
        _ ≤ _ := hD
    exact_mod_cast hh
  have hs : 2*Fintype.card (DWire F)≤48*N := by rw [d_physical_wire_count F reg]; omega
  exact retained_pin_domination pin cell 48 hs J (deviation_load_bound cell Δ h hn)

/-- A single quarter-balanced cut supplies a harmless auxiliary layout for the
two-layout matching theorem. Its only coordinate is used solely for selection. -/
private theorem auxiliary_layout (U : Finset W)
    (hU : (1/4:ℚ)*N ≤ (min U.card (N-U.card):ℕ)) :
    ∃ L : W → Fin 1 → Fin 32, ∀ x,empiricalLaw L x ≤ 24*uniformWeight (Fin 1→Fin 32) := by
  classical
  let L : W → Fin 1 → Fin 32 := fun v _ => if v∈U then 0 else 1
  refine ⟨L,fun x => ?_⟩
  have ha := le_trans hU (Nat.cast_le.mpr (min_le_left _ _))
  have hb := le_trans hU (Nat.cast_le.mpr (min_le_right _ _))
  have hsub : U.card≤N := Finset.card_le_univ U
  rw [Nat.cast_sub hsub] at hb
  have hn : 0<(N:ℚ) := by exact_mod_cast Fintype.card_pos
  have hc : (Fintype.card (Fin 1 → Fin 32):ℚ)=32 := by simp
  unfold empiricalLaw uniformWeight
  rw [hc]
  apply (div_le_iff₀ hn).2
  by_cases hx : x 0=0
  · have hle : (Finset.univ.filter (fun v => L v=x)) ⊆ U := by
      intro v hv
      have e := congrFun (Finset.mem_filter.mp hv).2 (0 : Fin 1)
      by_contra h
      simp [L,h,hx] at e
    have hc' : (((Finset.univ.filter (fun v => L v=x)).card):ℚ)≤U.card := by
      exact_mod_cast Finset.card_le_card hle
    linarith
  · have hle : (Finset.univ.filter (fun v => L v=x)) ⊆ Finset.univ \ U := by
      intro v hv
      have e := congrFun (Finset.mem_filter.mp hv).2 (0 : Fin 1)
      have h : v∉U := by intro hm; exact hx (by simpa [L,hm] using e.symm)
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,h⟩
    have hs := Finset.card_le_card hle
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ U),Finset.card_univ] at hs
    have hc' : (((Finset.univ.filter (fun v => L v=x)).card):ℚ)≤(N:ℚ)-U.card := by
      rw [←Nat.cast_sub hsub]
      exact_mod_cast hs
    linarith

set_option maxHeartbeats 12000000 in
theorem every_collision_packing_visits
    (loopless : ∀ v,(v,v)∉F)
    (γ : ℚ) (hg : 0<γ) (hg₃ : γ≤3)
    (expand : ∀ U : Finset W, (γ/3)*(min U.card (N-U.card):ℕ)≤((boundary F U).card:ℚ))
    (hr : Paper5.HybridClosure.Printed.Ready γ N)
    (hsize : (2*epsDen)^30*(3:ℕ)^10 ≤ dLambda N)
    (hdeg : f.natDegree=4*dLambda N) (hf : f.Monic)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (P : RootPacking F reg f) (hP : CollisionBound F reg f P) :
    ∃ d : Ready S Δ r*, 2^(printedExponent γ N) ≤ Fintype.card (PublicSlot F reg f P d) ∧
      ∀ σ : W→Bool, 2^(printedExponent γ N) ≤ (rootVisitLedger F reg f P d hf σ).length := by
  classical
  letI : Fact (Irreducible (ratPoly f)) := ⟨source_rat_irreducible f hf Fact.out⟩
  have sz := oldRowSize_eq_dSize F reg
  have widths := oldRow_widths_printed F reg f
  have hΔ : 3 ≤ Δ := by rw [sz]; exact hr.dDegree
  have hactive : (S).cutoff < Fintype.card (DWire F) := by
    change J9PrintedSchedule.leafThreshold (oldRowSize F) (Nat.clog 2 (oldRowSize F)) < _
    rw [sz,d_physical_wire_count F reg]
    exact hr.dActive
  have hDC : 2*(J9PrintedSchedule.arrayCard ((S).levelBits 0))^2*Δ≤Nat.card (DWire F) := by
    rw [widths.1,sz,Nat.card_eq_fintype_card,d_physical_wire_count F reg]
    exact hr.dCollision
  have hF : 0 < f.natDegree := by
    have ho : 0 < J9PrintedSchedule.rootU (dLambda N) := hr.dNodes
    unfold J9PrintedSchedule.rootU at ho
    omega
  let cfg := creating_source_config F reg f hdeg hsize
  let d : Ready S Δ r* := getReady cfg (oldRowRoot_stable F reg f _ hΔ) hactive
  have keq : (J).card = dU N := (rootKept_card_exact F reg f d).trans widths.2
  have k0 : (J).Nonempty := Finset.card_pos.mp (keq.symm ▸ hr.dNodes)
  obtain ⟨i,hi⟩ := k0
  letI : Nonempty ↥J := ⟨⟨i,hi⟩⟩
  have dd := every_packing_pin_domination F reg f P hP hDC
  obtain ⟨cut,hcut⟩ := choose_balanced_symbols (rootLabels F reg f P) 48 dd (by norm_num)
  obtain ⟨aux,haux⟩ := auxiliary_layout _ (hcut ⟨i,hi⟩)
  have budget := hr.unionBudget
  rw [←keq] at budget
  have hQ : (1:ℚ) ≤ mainQ N := by exact_mod_cast hr.mainNodes
  have budget' : 31104*(1+((J).card:ℚ)^2)<(matchingCoeff (γ/3))^2*(N:ℚ) := by
    nlinarith only [budget,hQ,sq_nonneg ((mainQ N:ℚ)-1)]
  obtain ⟨_,s_D,mark,orientation,_,hD,_⟩ :=
    fixed_affine_after_layout_choice (TM:=Fin 0) (TD:=Fin 0) (R:=IntRing f 1)
      («S»:=NativeProbeRing.Residue f) (K:=RatScalar f) F loopless reg aux (rootLabels F reg f P)
      (γ/3) (by positivity) (by linarith only [hg₃]) expand haux dd (by simp) (by simp)
      (by simpa using budget')
  let matching := MatchingThinning.matching F loopless mark orientation
  let D := routeDepth (γ/3) N (J).card
  have gap : ∀ j, D ≤ endpointImbalance matching.endpoint
      (labelCut (rootLabels F reg f P) id s_D j) := by
    simpa only [D,Fintype.card_coe] using hD
  have small := (gap ⟨i,hi⟩).trans (endpoint_imbalance_le matching.endpoint _)
  have card := literal_menu_card_from_matching F reg f P cfg hΔ hf hF d matching s_D D small gap
  have lower : 2^(min (routeDepth (γ/3) N (mainQ N)) (routeDepth (γ/3) N (dU N))) ≤
      0+Fintype.card (PublicSlot F reg f P d) := by
    rw [zero_add,←keq]
    exact (Nat.pow_le_pow_right (by decide) (min_le_right _ _)).trans card
  have hc := printed_exp_term_count hr lower
  rw [zero_add] at hc
  exact ⟨d,hc,fun σ => hc.trans (FixedSchedule.card_le_trace_length
    (literalRootProductTrace F reg f P d hf σ))⟩

#print axioms every_packing_pin_domination
#print axioms every_collision_packing_visits
end Paper5.D1Literal
