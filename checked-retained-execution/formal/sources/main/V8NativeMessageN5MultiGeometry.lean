import V8NativeMessageN4PhysicalCut
import V8NativeMessageN4Local
import P5HybridMultiMatching
import P5D1LiteralPrinted

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
set_option maxRecDepth 5000

/-! One shared induced matching for the original retained D
coordinate menu of a single fixed four-copy root packing. The word
law uses the old pin-row side of the actual physical wires. -/
namespace V8NativeMessage.N5
open scoped Classical BigOperators Polynomial
open Paper5.D1Literal Paper5.HybridClosure Paper5.HybridMulti J6R9Recursive
  J6R10Repack J6R11Collision J6R11CollisionReindex P11FullPacking J1PPrinted J6R12Blueprint J6ActiveRun
  EmpiricalCutMoments GraphCutMoments N4 ProductVariance SeparatedRank J1MainSourceCollision
noncomputable section

variable {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]
  {F : Finset (X×X)} {reg : ∀ v,GraphCutMoments.degree F v=3} {f : ℤ[X]}

local notation "s₀" => (oldRowSize F)
local notation "Δ" => sourceDelta s₀
local notation "S₀" => (printedParams (f:=f) (ell:=1) s₀)
local notation "N" => Fintype.card X

def pinPort : X↪DWire F where
  toFun := realPinWire
  inj' := fun v w e => Sum.inl.inj (congrArg (fun q : DWire F => q.1) (show realPinWire v=realPinWire w from e))

theorem true_word_domination (P : RootPacking F reg f) (d : LayoutReady F reg f)
    (hv : varianceScore (actualCell P)≤2*(Nat.card (DWire F):ℚ)*Δ) :
    ∀ x,empiricalLaw (rootLabels F reg f P) x≤48*uniformWeight (rootKept F f→Fin 64) := by
  let a := (S₀).levelBits 0
  let cell := edgeCell (dNetwork F reg).row (dNetwork F reg).col (P.rowLabel,P.colLabel)
  have hd : deviation cell≤2*(Fintype.card (DWire F):ℚ)*Δ := by
    rw [Nat.card_eq_fintype_card] at hv
    change varianceScore (declaredCell (dNetwork F reg) P.rowLabel P.colLabel)≤_ at hv
    rw [declared_variance_eq (dNetwork F reg) (P.rowLabel,P.colLabel)] at hv
    exact hv
  have hc : 2*(Δ:ℚ)*(Fintype.card ((Fin a→Fin 64)×(Fin a→Fin 64)):ℚ)^2≤
      (Fintype.card (DWire F):ℚ) := by
    rw [source_word_cells 64 a]
    have he : 2*(64^(2*a))^2*Δ≤Fintype.card (DWire F) := by
      exact d.collision
    have hh : 2*Δ*(64^(2*a))^2≤Fintype.card (DWire F) := by
      calc
        _ = 2*(64^(2*a))^2*Δ := by ac_rfl
        _ ≤ _ := he
    exact_mod_cast hh
  have hp : 2*Fintype.card (DWire F)≤48*N := by
    rw [d_physical_wire_count F reg]
    omega
  exact retained_pin_domination (pinPort (F:=F)) cell 48 hp (rootKept F f)
    (deviation_load_bound cell Δ hd hc)

omit [Nonempty X] in
theorem native_coordinate_count (d : LayoutReady F reg f) :
    Fintype.card (rootKept F f)=Paper5.HybridClosure.Printed.dU N := by
  rw [Fintype.card_coe,rootKept_card_exact F reg f d,(oldRow_widths_printed F reg f).2]

/-- Finite N4 mixed-coordinate selection, with the same graph-fixed
physical packing for every coordinate and actual parameter u. The
explicit strict union guard is sufficient, not a lower bound on N. -/
theorem one_native_common_matching
    (P : RootPacking F reg f) (d : LayoutReady F reg f)
    (hv : varianceScore (actualCell P)≤2*(Nat.card (DWire F):ℚ)*Δ)
    (hloop : ∀ v,(v,v)∉F) (γ : ℚ) (hγ : 0<γ) (hγ₁ : γ≤1)
    (expand : ∀ U : Finset X, γ*(min U.card (N-U.card):ℕ)≤((boundary F U).card:ℚ))
    (hu : 0<Paper5.HybridClosure.Printed.dU N)
    (hUnion : 31104*(Paper5.HybridClosure.Printed.dU N:ℚ)^2<(matchingCoeff γ)^2*(N:ℚ)) :
    ∃ symbols : rootKept F f→Finset (Fin 64), ∃ mark orientation : F→Bool,
      ∀ i,routeDepth γ N (Paper5.HybridClosure.Printed.dU N)≤endpointImbalance
        (MatchingThinning.matching F hloop mark orientation).endpoint
        (labelCut (rootLabels F reg f P) id symbols i) := by
  let u := Paper5.HybridClosure.Printed.dU N
  have hc : Fintype.card (rootKept F f)=u := native_coordinate_count d
  have hne : Nonempty (rootKept F f) := Fintype.card_pos_iff.mp (hc.symm ▸ hu)
  letI := hne
  let w := routeWeight u
  have hw : 0<w := routeWeight_pos u
  have hN : 0<N := Fintype.card_pos
  let L : Unit → X → rootKept F f → Fin 64 := fun _=>rootLabels F reg f P
  obtain ⟨symbols,hs⟩ := choose_balanced_symbols (rootLabels F reg f P) 48
    (true_word_domination P d hv) (by norm_num)
  have hmargin : familyMargin X γ (1/4) 12 w=matchingCoeff γ*(N:ℚ)*w := by
    unfold familyMargin boundaryDensity matchingCoeff
    ring
  have hNorm : w^2*(48:ℚ)*(Fintype.card (rootKept F f):ℚ)≤(12:ℚ)^2 := by
    rw [hc]
    have he := mul_le_mul_of_nonneg_left (routeWeight_square_scale u) (by norm_num : (0:ℚ)≤48)
    change (48:ℚ)*(w^2*u)≤48*1 at he
    nlinarith only [he]
  have hEn : ((u:ℚ)*(7776*(N:ℚ)))/(matchingCoeff γ*(N:ℚ)*w)^2<1 := by
    have h := one_route_union_test (matchingCoeff γ) (matchingCoeff_pos γ hγ) N u hN hu
    apply h.trans_lt
    have hpos : (0:ℚ)<matchingCoeff γ^2*(N:ℚ) :=
      mul_pos (pow_pos (matchingCoeff_pos γ hγ) _) (by exact_mod_cast hN)
    apply (div_lt_iff₀ hpos).mpr
    simpa only [one_mul] using hUnion
  obtain ⟨mark,o,hFinal⟩ := arbitrary_family_common_matching_exact
    (S:=Unit) F hloop reg L (fun _=>symbols) (fun _=>48) (fun _=>w) (fun _=>12)
    γ (1/4) hγ hγ₁ (by norm_num) (by norm_num) expand (fun _=>hs)
    (fun _=>true_word_domination P d hv) (fun _=>hw) (fun _=>by norm_num)
    (fun _=>hNorm) (fun _=>routeDepth γ N u)
    (fun _=>by simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_unit,one_nsmul,hmargin]
      using (routeDepth_margin γ hγ N u).1)
    (by simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_unit,one_nsmul,hc,hmargin] using hEn)
  exact ⟨symbols,mark,o,hFinal Unit.unit⟩

#print axioms true_word_domination
#print axioms native_coordinate_count
#print axioms one_native_common_matching
end
end V8NativeMessage.N5