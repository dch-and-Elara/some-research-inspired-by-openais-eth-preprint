import V8NativeMessageN5Power
import V8NativeMessageN4OrdinaryEnd

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option maxRecDepth 3500

/-! N5 on the literal N4 one-coordinate four-copy family. The tape
has actual signed values: a particular whole native cross product
and the bare N1 group jets evaluated at particular eligible points,
not just integers named K and b. -/
namespace V8NativeMessage.N5
open scoped Classical BigOperators Polynomial
open Paper5.D1Literal J6R9Recursive J6R10Repack N4 V8NativeMessage.C3.NativeAssembly.MainScan
noncomputable section

variable {X : Type} [Fintype X] [DecidableEq X] {F : Finset (X×X)}
  {reg : ∀ v,GraphCutMoments.degree F v=3} {f : ℤ[X]}
  {P : RootPacking F reg f} {d : LayoutReady F reg f} {i : rootKept F f}
  [Fact (Irreducible (ratPoly f))]

abbrev NativePayload (f : ℤ[X]) := RatRing f 1 ⊕ (Σ j : ℕ,Jet j)

/-- The fixed N1 multiplier is not part of this payload, so a cache
entry of the same bare point can be delivered to differently weighted
lists without re-evaluating its signed native jet. -/
def privatePayload (Q : OrdinaryQuery P d i) (σ : X→Bool)
    (g : Fin Q.groups) (j : Fin (Q.pointList.count g)) : NativePayload f :=
  Sum.inr ⟨Q.order,nativeGroup F reg Q.tuple σ g
    (N6.fullPoint Q.tuple Q.accepted Q.pointList g j)⟩

def crossPayload (Q : OrdinaryQuery P d i) (hf : f.Monic) (σ : X→Bool) : NativePayload f :=
  Sum.inl (ordinaryM Q σ*embed f 1 (rawWhole d hf Q.slot σ))

omit [Fact (Irreducible (ratPoly f))] in
@[simp] theorem whole_weighted_from_cross (Q : OrdinaryQuery P d i)
    (hf : f.Monic) (σ : X→Bool) :
    weightedWhole Q hf σ=ordinaryD Q*(ordinaryM Q σ*embed f 1 (rawWhole d hf Q.slot σ)) := by
  rw [weightedWhole,mul_assoc]

variable {L H : Type*} [Fintype H] {width : ℕ}
    (Qs : H→OrdinaryQuery P d i) (hf : f.Monic) (σ : X→Bool)

structure PointReceipts (t : Trace L (NativePayload f) width) where
  key : ∀ h g,Fin ((Qs h).pointList.count g)→L
  distinct : ∀ h g,Function.Injective (key h g)
  done : ∀ h g j,Provides t (key h g j) (privatePayload (Qs h) σ g j)

def PointReceipts.roster {t : Trace L (NativePayload f) width}
    (B : PointReceipts Qs σ t) (h : H) (g : Fin (Qs h).groups) :
    Roster (Fin ((Qs h).pointList.count g)) t where
  key := B.key h g
  unique := B.distinct h g
  value := privatePayload (Qs h) σ g
  delivered := B.done h g

structure ExplicitReceipts (t : Trace L (NativePayload f) width)
    extends PointReceipts Qs σ t where
  crossKey : H→L
  crossDistinct : Function.Injective crossKey
  crossDone : ∀ h,Provides t (crossKey h) (crossPayload (Qs h) hf σ)

def ExplicitReceipts.roster {t : Trace L (NativePayload f) width}
    (B : ExplicitReceipts Qs hf σ t) : Roster H t where
  key := B.crossKey
  unique := B.crossDistinct
  value := fun h => crossPayload (Qs h) hf σ
  delivered := B.crossDone

omit [Fact (Irreducible (ratPoly f))] in
theorem true_order_bound (Q : OrdinaryQuery P d i) :
    Q.order≤12*Fintype.card X+1 := by
  have h := printed_J_prev (Fintype.card X) Q.degree Q.nodes Q.order
    (Nat.zero_lt_of_lt Q.tuple.node.isLt) (by have h:=Q.separation; omega) Q.printedOrder
  omega

variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable {γ : ℝ} (C : FourCut P i γ)

def RightTerminal : Prop := ∀ τ : X→Bool,∃ total : IntRing f 1,
  (∑ h, weightedWhole (Qs h) hf τ)=embed f 1 total ∧
  reduce (4*Fintype.card X+1) f 1 total=(nativeCount F reg τ:Residue f 1 (4*Fintype.card X+1))

theorem original_work_power {t : Trace L (NativePayload f) width}
    (actual : ExplicitReceipts Qs hf σ t) (correct : RightTerminal Qs hf)
    {κmax rmax : ℕ} (hk : ∀ h,(Qs h).order≤κmax) (hr : ∀ h,(Qs h).groups≤rmax) :
    2^C.m≤κmax*(width*time t)^(rmax+1) := by
  have rank : 2^C.m≤∑ h,(Qs h).order*∏ g,(Qs h).pointList.count g :=
    original_whole_slot_N4 hf C Qs correct
  have products : Fintype.card H≤width*time t := (ExplicitReceipts.roster Qs hf σ actual).card_le
  have points (h : H) (g : Fin (Qs h).groups) : (Qs h).pointList.count g≤width*time t := by
    simpa only [Fintype.card_fin] using
      (PointReceipts.roster Qs σ actual.toPointReceipts h g).card_le
  exact work_power (r:=fun h=>(Qs h).groups) (κ:=fun h=>(Qs h).order)
    (b:=fun h g=>(Qs h).pointList.count g) rank (by simpa only [pow_one] using products) points hk hr Nat.one_pos

theorem from_match_log {m width T κmax r : ℕ} (hr : 0<r)
    (a : ℝ) (ha : a≤m) (hp : 2^m≤κmax*(width*T)^r) :
    (a-Real.logb 2 κmax)/r-Real.logb 2 width≤Real.logb 2 T := by
  apply le_trans _ (log_of_work_power m width T κmax r hr hp)
  apply sub_le_sub_right
  exact div_le_div_of_nonneg_right (sub_le_sub_right ha _) (by positivity)

include C in
theorem original_N5_log {t : Trace L (NativePayload f) width}
    (actual : ExplicitReceipts Qs hf σ t) (correct : RightTerminal Qs hf)
    {κmax rmax : ℕ} (hk : ∀ h,(Qs h).order≤κmax) (hr : ∀ h,(Qs h).groups≤rmax) :
    (γ*(Fintype.card X:ℝ)/68-Real.logb 2 κmax)/(rmax+1)-
      Real.logb 2 width≤Real.logb 2 (time t) := by
  have he : γ*(Fintype.card X:ℝ)/68≤(C.m:ℝ) := by
    apply (div_le_iff₀ (by norm_num : 0<(68:ℝ))).mpr
    simpa only [mul_comm (C.m:ℝ)] using C.match_budget
  simpa only [Nat.cast_succ] using from_match_log (Nat.succ_pos rmax) _ he
    (original_work_power (Qs:=Qs) (hf:=hf) (σ:=σ) (C:=C) actual correct hk hr)

#print axioms whole_weighted_from_cross
#print axioms true_order_bound
#print axioms original_work_power
#print axioms from_match_log
#print axioms original_N5_log
end
end V8NativeMessage.N5