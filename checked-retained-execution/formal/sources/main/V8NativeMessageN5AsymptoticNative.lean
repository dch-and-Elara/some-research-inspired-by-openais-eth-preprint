import V8NativeMessageN5AsymptoticCutoff
import V8NativeMessageN5MultiWork

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 7600000
set_option maxRecDepth 4500

/-! Strict source specialization of the two eventual N5 conclusions.
The threshold is uniform across native feasible fixed representations
and actual metered traces of polynomial width, at fixed expansion
and width-polynomial constants. All semantics/coverage premises of
the original finite result remain present. -/
namespace V8NativeMessage.N5
open scoped Classical BigOperators Topology Polynomial
open Filter Paper5.D1Literal Paper5.HybridClosure Paper5.HybridClosure.Printed
  J6R9Recursive J6R10Repack J1PPrinted N4 GraphCutMoments
noncomputable section

universe u v

theorem actual_single_coordinate_log_bigOmega (γ : ℝ) (hγ : 0<γ) (coeff e : ℕ) :
    ∃ cutoff : ℕ, 0<oneCoefficient γ ∧
      ∀ {X : Type} [Fintype X] [DecidableEq X]
      {F : Finset (X×X)} {reg : ∀ v,GraphCutMoments.degree F v=3} {f : ℤ[X]}
      {P : RootPacking F reg f} {d : LayoutReady F reg f} {i : rootKept F f}
      [Fact (Irreducible (ratPoly f))] [Fact (Irreducible (NativeProbeRing.residuePoly f))]
      {H : Type u} [Fintype H] {L : Type v} {width : ℕ} {t : Trace L (NativePayload f) width}
      (_ : FourCut P i γ) (Qs : H→OrdinaryQuery P d i) (hf : f.Monic) (σ : X→Bool),
      cutoff≤Fintype.card X →
      width≤coeff*(Fintype.card X+1)^e →
      (∀ h,(Qs h).groups≤mainR (Fintype.card X)) →
      ExplicitReceipts Qs hf σ t → RightTerminal Qs hf →
      oneCoefficient γ*oneScale (Fintype.card X)≤Real.logb 2 (time t) := by
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.1 (original_single_scale_eventually γ hγ coeff e)
  refine ⟨n₀,one_coefficient_positive γ hγ,?_⟩
  intro X Xf Xd F reg f P d i rf zf H hH L width t cut Qs hf σ hN hwpoly hg actual correct
  let n := Fintype.card X
  have horder : ∀ h,(Qs h).order≤12*n+1 := fun h=>true_order_bound (Qs h)
  have hp : 2^cut.m≤(12*n+1)*(width*time t)^(mainR n+1) :=
    original_work_power (C:=cut) (Qs:=Qs) (hf:=hf) (σ:=σ) actual correct horder hg
  have hw : 0<width := positive_width_of_paid_power (Nat.succ_pos _) hp
  exact hn₀ n hN width (time t) hw hwpoly
    (original_printed_N5 (C:=cut) (Qs:=Qs) (hf:=hf) (σ:=σ) actual correct hg)

theorem actual_full_native_menu_log_bigOmega (γ : ℚ) (hγ : 0<γ) (coeff e : ℕ) :
    ∃ c : ℝ, 0<c ∧ ∃ cutoff : ℕ,
      ∀ {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]
      {F : Finset (X×X)} {reg : ∀ v,GraphCutMoments.degree F v=3} {f : ℤ[X]}
      {P : RootPacking F reg f} {d : LayoutReady F reg f}
      [Fact (Irreducible (ratPoly f))] [Fact (Irreducible (NativeProbeRing.residuePoly f))]
      {H : Type u} [Fintype H] {L : Type v}
      {coordinate : H → rootKept F f} {width : ℕ} {t : Trace L (NativePayload f) width}
      (Qs : ∀ h,OrdinaryQuery P d (coordinate h)) (hf : f.Monic) (σ : X→Bool),
      cutoff≤Fintype.card X →
      varianceScore (actualCell P)≤2*(Nat.card (DWire F):ℚ)*sourceDelta (oldRowSize F) →
      (∀ v,(v,v)∉F) →
      (∀ U : Finset X,γ*(min U.card (Fintype.card X-U.card):ℕ)≤((boundary F U).card:ℚ)) →
      width≤coeff*(Fintype.card X+1)^e →
      (∀ h,(Qs h).groups≤mainR (Fintype.card X)) →
      MultiReceipts Qs hf σ t → RightMultiTerminal Qs hf →
      c*menuScale (Fintype.card X)≤Real.logb 2 (time t) := by
  let g : ℚ := min γ 1
  have gpos : 0<g := lt_min hγ (by norm_num)
  have g1 : g≤1 := min_le_right _ _
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.1 (original_menu_scale_eventually g gpos coeff e)
  refine ⟨menuCoefficient g,menu_coefficient_positive g gpos,n₀,?_⟩
  intro X Xf Xd Xne F reg f P d rf zf H hH L coords width t
    Qs hf σ hN hv hloop exp hwpoly hg actual correct
  let n := Fintype.card X
  have exp' (U : Finset X) : g*(min U.card (n-U.card):ℕ)≤((boundary F U).card:ℚ) :=
    (mul_le_mul_of_nonneg_right (show g≤γ from min_le_left _ _) (by positivity)).trans (exp U)
  obtain ⟨hu,hUnion,hBound⟩ := hn₀ n hN
  have horder : ∀ h,(Qs h).order≤12*n+1 := fun h=>true_order_bound (Qs h)
  have hp : 2^(routeDepth g n (dU n))≤(12*n+1)*(width*time t)^(mainR n+1) :=
    original_full_menu_work_power Qs hf σ hv hloop g gpos g1 exp' hu hUnion actual correct horder hg
  have hw : 0<width := positive_width_of_paid_power (Nat.succ_pos _) hp
  exact hBound width (time t) hw hwpoly
    (original_full_menu_N5_log Qs hf σ hv hloop g gpos g1 exp' hu hUnion actual correct horder hg)

#print axioms actual_single_coordinate_log_bigOmega
#print axioms actual_full_native_menu_log_bigOmega
end
end V8NativeMessage.N5