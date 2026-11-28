import V8NativeMessageN5Native
import V8NativeMessageN5MultiGeometry
import V8NativeMessageN5MultiLift

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8500000
set_option maxRecDepth 4500

/-! The original full D coordinate menu, a single physically fixed
four-copy root, and one fixed metered zero-bypass representation.
The same induced matching is used by every term. -/
namespace V8NativeMessage.N5
open scoped Classical BigOperators Polynomial
open Paper5.D1Literal Paper5.HybridClosure J6R9Recursive J6R10Repack J1PPrinted
  N4 GraphCutMoments SeparatedRank
noncomputable section

variable {X : Type} [Fintype X] [DecidableEq X] {F : Finset (X×X)}
  {reg : ∀ v,GraphCutMoments.degree F v=3} {f : ℤ[X]}
  {P : RootPacking F reg f} {d : LayoutReady F reg f}
  [Fact (Irreducible (ratPoly f))] [Fact (Irreducible (NativeProbeRing.residuePoly f))]

variable {H L : Type*} [Fintype H] {width : ℕ} {coordinate : H → rootKept F f}
  (Qs : ∀ h,OrdinaryQuery P d (coordinate h)) (hf : f.Monic) (σ : X→Bool)

structure MultiReceipts (t : Trace L (NativePayload f) width) where
  cross : Roster H t
  cross_correct : ∀ h,cross.value h=crossPayload (Qs h) hf σ
  privatePoints : ∀ h g,Roster (Fin ((Qs h).pointList.count g)) t
  point_correct : ∀ h g j,(privatePoints h g).value j=privatePayload (Qs h) σ g j

theorem paid_multi_given_matching {I : Type*} [Fintype I]
    (M : PinnedCNF.InducedMatching F I) (symbols : rootKept F f→Finset (Fin 64)) (gap : ℕ)
    (fit : gap≤Fintype.card I)
    (simultaneous : ∀ h,gap≤endpointImbalance M.endpoint
      (EmpiricalCutMoments.labelCut (rootLabels F reg f P) id symbols (coordinate h)))
    {t : Trace L (NativePayload f) width} (actual : MultiReceipts Qs hf σ t)
    (correct : RightMultiTerminal Qs hf)
    {κmax rmax : ℕ} (hk : ∀ h,(Qs h).order≤κmax) (hr : ∀ h,(Qs h).groups≤rmax) :
    2^gap≤κmax*(width*time t)^(rmax+1) := by
  have rank : 2^gap≤∑ h,(Qs h).order*∏ g,(Qs h).pointList.count g :=
    original_multi_coordinate_N4 Qs hf M correct symbols gap fit simultaneous
  exact paid_explicit (r:=fun h=>(Qs h).groups) (κ:=fun h=>(Qs h).order)
    (b:=fun h g=>(Qs h).pointList.count g) rank actual.cross actual.privatePoints hk hr

variable [Nonempty X]

local notation "N" => Fintype.card X
local notation "Δ" => sourceDelta (oldRowSize F)
local notation "u" => Paper5.HybridClosure.Printed.dU N

theorem original_full_menu_work_power
    (hv : varianceScore (actualCell P)≤2*(Nat.card (DWire F):ℚ)*Δ)
    (hloop : ∀ v,(v,v)∉F) (γ : ℚ) (hγ : 0<γ) (hγ₁ : γ≤1)
    (expand : ∀ U : Finset X,γ*(min U.card (N-U.card):ℕ)≤((boundary F U).card:ℚ))
    (hu : 0<u) (hUnion : 31104*(u:ℚ)^2<(matchingCoeff γ)^2*(N:ℚ))
    {t : Trace L (NativePayload f) width} (actual : MultiReceipts Qs hf σ t)
    (correct : RightMultiTerminal Qs hf)
    {κmax rmax : ℕ} (hk : ∀ h,(Qs h).order≤κmax) (hr : ∀ h,(Qs h).groups≤rmax) :
    2^(routeDepth γ N u)≤κmax*(width*time t)^(rmax+1) := by
  obtain ⟨symbols,mark,orientation,simultaneous⟩ :=
    one_native_common_matching P d hv hloop γ hγ hγ₁ expand hu hUnion
  have hU := native_coordinate_count d
  have hCard : 0<Fintype.card (rootKept F f) := hU.symm ▸ hu
  obtain ⟨i₀⟩ := Fintype.card_pos_iff.mp hCard
  let M := MatchingThinning.matching F hloop mark orientation
  have fit := (simultaneous i₀).trans (imbalance_le_word M _)
  exact paid_multi_given_matching Qs hf σ M symbols _ fit (fun h => simultaneous (coordinate h))
    actual correct hk hr

theorem original_full_menu_N5_log
    (hv : varianceScore (actualCell P)≤2*(Nat.card (DWire F):ℚ)*Δ)
    (hloop : ∀ v,(v,v)∉F) (γ : ℚ) (hγ : 0<γ) (hγ₁ : γ≤1)
    (expand : ∀ U : Finset X,γ*(min U.card (N-U.card):ℕ)≤((boundary F U).card:ℚ))
    (hu : 0<u) (hUnion : 31104*(u:ℚ)^2<(matchingCoeff γ)^2*(N:ℚ))
    {t : Trace L (NativePayload f) width} (actual : MultiReceipts Qs hf σ t)
    (correct : RightMultiTerminal Qs hf)
    {κmax rmax : ℕ} (hk : ∀ h,(Qs h).order≤κmax) (hr : ∀ h,(Qs h).groups≤rmax) :
    ((routeDepth γ N u:ℝ)-Real.logb 2 κmax)/(rmax+1)-
      Real.logb 2 width≤Real.logb 2 (time t) := by
  exact_mod_cast log_of_work_power (routeDepth γ N u) width (time t) κmax (rmax+1)
    (Nat.succ_pos _) (original_full_menu_work_power Qs hf σ hv hloop γ hγ hγ₁ expand hu hUnion actual correct hk hr)

#print axioms paid_multi_given_matching
#print axioms original_full_menu_work_power
#print axioms original_full_menu_N5_log
end
end V8NativeMessage.N5