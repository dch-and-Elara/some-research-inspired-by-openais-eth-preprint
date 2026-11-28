import J6R49CostActiveAddress
import J6R49CostNativeScope
import J6R49CostScopePublish
import J6R49DFSRun

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 23000000
set_option maxRecDepth 3000

/-! Path recurrence of the same all-depth R49 streamer. The local
tariff includes actual scoped publication and exposed retirement.
No comparison of two different machines' step counts is used. -/
namespace J6R49Cost
open scoped Polynomial Classical BigOperators
open AOracleMachineTime A1R10 A1R12 J6R22Active
open J1PPrinted J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R16ModeCost J6R24MeteredRecursion J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R48DFS J6R49DFS

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (@Plan f ell s sel)
local notation "L" => PageBank f ell key prec tw bw page
local notation "J" => PageJob f ell key prec tw bw page

noncomputable def actualStreamTotal (R : StreamingResident T key prec tw bw page q)
    (retire : J → ℕ) (initial : L) (z : Sigma (Path sel r)) : ℕ :=
  (nativeStream R retire z.1 z.2 (stackBank R.births initial z.2)).steps

noncomputable def actualStreamOwn (R : StreamingResident T key prec tw bw page q)
    (retire : J → ℕ) (initial : L) (z : Sigma (Path sel r)) : ℕ :=
  if stop : z.1.edges ≤ (S).cutoff then
    (R.leaf z.2 stop (stackBank R.births initial z.2)).steps
  else
    let F := R.active z.2 (Nat.lt_of_not_ge stop)
    letI : Fintype ((P).Slot z.1) := (P).finiteSlot z.1
    streamActiveTariff F (reachable_positive T z.2.reached) T.vPositive+
      ∑ w : (P).Slot z.1,scopedPublishCharge R.births initial z.2 w retire

variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

theorem actual_stream_runtime_step (R : StreamingResident T key prec tw bw page q)
    (retire : J → ℕ) (initial : L) (legal : ReadyOnStack R.births initial)
    (z₀ : Sigma (Path sel r)) :
    actualStreamTotal R retire initial z₀ ≤ actualStreamOwn R retire initial z₀+
      ((childList (@nativeScopedPlan f ell s sel r) z₀).map (actualStreamTotal R retire initial)).sum := by
  rcases z₀ with ⟨c,p⟩
  by_cases stop : c.edges ≤ (S).cutoff
  · unfold actualStreamTotal actualStreamOwn
    dsimp only
    rw [nativeStream,dif_pos stop,dif_pos stop]
    exact Nat.le_add_right _ _
  · let a := Nat.lt_of_not_ge stop
    let d := ready_reachable cfg sel p.reached T.rootStable a
    let F := R.active p a
    let bank := stackBank R.births initial p
    let hp := reachable_positive T p.reached
    let read : ActiveChild (sel:=sel) (d:=d) T.bank := fun t z β g =>
      let w := addressed (sel:=sel) d t z β g
      project (withScope retire (R.births p w).job
        (nativeStream R retire ((P).child c w) (.step p w))
        (zeroM (T.bank (registerPrecision S c t) (register_positive d t)).hp) bank)
    let input := fun w : (P).Slot c=>actualStreamTotal R retire initial ⟨(P).child c w,.step p w⟩
    let publish := fun w : (P).Slot c=>scopedPublishCharge R.births initial p w retire
    letI : Fintype ((P).Slot c) := (P).finiteSlot c
    have hs := (stable_reachable cfg sel p.reached T.rootStable).sizeByDepth
    obtain ⟨hu,_,huM⟩ := printed_taper_legal s c.edges C c.depth cfg.widthPos cfg.constPos cfg.size a hs
    have bm := actual_stream_active_word_meter F R.modeWidth hp T.vPositive hf hu huM read
    have br : streamActiveChildBill F read = (∑ w : (P).Slot c, (publish w + input w)) := by
      apply stream_active_child_bill_matches_slots F T.vPositive read (fun w=>publish w+input w)
      intro t z β g
      let w := addressed (sel:=sel) d t z β g
      let low := T.bank (registerPrecision S c t) (register_positive d t)
      let child := nativeStream R retire ((P).child c w) (.step p w)
      exact actual_ready_scope_edge_steps R.births initial p w legal retire child (zeroM low.hp)
    have hsum := (childList_bill_as_sum (@nativeScopedPlan f ell s sel r) ⟨c,p⟩
      (actualStreamTotal R retire initial)).symm
    change (∑ w : (P).Slot c,input w) =
      ((childList (@nativeScopedPlan f ell s sel r) ⟨c,p⟩).map (actualStreamTotal R retire initial)).sum at hsum
    rw [br,Finset.sum_add_distrib,hsum] at bm
    unfold actualStreamTotal actualStreamOwn
    try dsimp only
    rw [nativeStream,dif_neg stop,dif_neg stop]
    change (F.eval R.modeWidth hp T.vPositive hf read).steps ≤ streamActiveTariff F hp T.vPositive+
        (∑ w : (P).Slot c,publish w)+_
    exact bm.trans (le_of_eq (by ac_rfl))

theorem actual_stream_under_local_bit_tariffs (R : StreamingResident T key prec tw bw page q)
    (retire : J → ℕ) (initial : L) (legal : ReadyOnStack R.births initial)
    (hzero : r.depth=0) (hroot : r.prec ≤ C*s)
    (fixed address : ℕ)
    (bound : ∀ z₀ : Sigma (Path sel r),
      actualStreamOwn R retire initial z₀ ≤ fixed+address*Nat.card ((P).Slot z₀.1)) :
    (nativeStream R retire r .root initial).steps ≤ (pathLimit s C+1)*(fixed+address)*
      2^(branchBits (Nat.clog 2 s)*(pathLimit s C+1)+24*depthScale s C (Nat.clog 2 s) (siteConstant C)) :=
  printed_path_scoped_budget cfg sel r T.rootStable hzero hroot
    (actualStreamTotal R retire initial) (actualStreamOwn R retire initial) fixed address
    (actual_stream_runtime_step R retire initial legal) bound


omit [Fact (Irreducible (NativeProbeRing.residuePoly f))] in
theorem actual_local_tariff_from_phase_caps (R : StreamingResident T key prec tw bw page q)
    (retire : J → ℕ) (initial : L) (fixed arithmetic publication : ℕ)
    (leaf : ∀ (z : Sigma (Path sel r)) (stop : z.1.edges ≤ (S).cutoff),
      (R.leaf z.2 stop (stackBank R.births initial z.2)).steps ≤ fixed)
    (active : ∀ (z : Sigma (Path sel r)) (ha : (S).cutoff < z.1.edges),
      streamActiveTariff (R.active z.2 ha) (reachable_positive T z.2.reached) T.vPositive ≤
        fixed+arithmetic*Nat.card ((P).Slot z.1))
    (publish : ∀ (z : Sigma (Path sel r)) (w : (P).Slot z.1),
      scopedPublishCharge R.births initial z.2 w retire ≤ publication) :
    ∀ z : Sigma (Path sel r),
      actualStreamOwn R retire initial z ≤ fixed+(arithmetic+publication)*Nat.card ((P).Slot z.1) := by
  intro z
  by_cases stop : z.1.edges ≤ (S).cutoff
  · rw [actualStreamOwn,dif_pos stop]
    exact (leaf z stop).trans (Nat.le_add_right _ _)
  · letI : Fintype ((P).Slot z.1) := (P).finiteSlot z.1
    have hp : (∑ w : (P).Slot z.1,scopedPublishCharge R.births initial z.2 w retire) ≤
        publication*Nat.card ((P).Slot z.1) := by
      calc
        _ ≤ ∑ _ : (P).Slot z.1,publication := Finset.sum_le_sum (fun w _ => publish z w)
        _ = _ := by rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card,Nat.mul_comm]; rfl
    rw [actualStreamOwn,dif_neg stop]
    exact (Nat.add_le_add (active z (Nat.lt_of_not_ge stop)) hp).trans (le_of_eq (by ring))

#print axioms actual_local_tariff_from_phase_caps
#print axioms actualStreamTotal
#print axioms actualStreamOwn
#print axioms actual_stream_runtime_step
#print axioms actual_stream_under_local_bit_tariffs
end J6R49Cost

