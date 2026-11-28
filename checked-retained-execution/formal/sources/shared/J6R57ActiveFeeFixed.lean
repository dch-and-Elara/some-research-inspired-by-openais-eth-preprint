import J6R57ActiveFeeCentre
import J6R57ActiveFeePhase

/-! Uniform bound for the real per-node fixed arithmetic (including
all distinct centres, coefficient terms, interpolation, and strip).
Only actual preparation, tape and mask read meters and optional
excess precision remain as independent implementation guards. -/
namespace J6R57ActiveFee
open scoped Polynomial Classical BigOperators
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active
open J1PPrinted J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R24MeteredRecursion J6R23ScheduleWeight J6R48BitCost J6R49DFS J6R49Cost J6R50Peak
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R51Online J6R55CachedLedger
open J6R56PrintedExponent J6R16ModeCost

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 16000000
set_option maxRecDepth 3800
set_option linter.unusedSectionVars false
set_option Elab.async false

def stripPx (K : ℕ) := 6+K*(10+K*(8*(K+1)+K+8)+K*K)
def fixedArithmeticPx (K tape mask : ℕ) :=
  K*fixedCentrePx K tape mask+uvPx K+K*(addPx K+2)+stripPx K+4+uvPx K+2

theorem actual_strip_bound {e ell p B K : ℕ} (he : e ≤ K) (hℓ : ell ≤ K)
    (hP : p+B ≤ K) : stripFee e ell p B ≤ stripPx K := by
  have p0 := (Nat.le_add_right p B).trans hP
  unfold stripFee stripPx
  gcongr

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}

structure PrintedCentreScale (s C K : ℕ) : Prop where
  edges : 4*(C*s) ≤ K
  probes : (C*s)*(2*2^(Nat.clog 2 s))+1 ≤ K
  centreSlots : 2^(Nat.clog 2 s+1)+1 ≤ K

theorem fixed_arithmetic_of_actual_prepared_machine
    (M : OnlineMachine T key prec tw bw page q) (p : Path sel r c)
    (a : (printedParams (f:=f) (ell:=ell) s).cutoff<c.edges)
    (K tape mask : ℕ)
    (ws : ActiveWidthScale (ell:=ell) (s:=s) (C:=C) (q:=q) (r:=r) K)
    (cs : PrintedCentreScale s C K)
    (high : c.prec+(preparedActive M p a).result.extraPrecision ≤ K)
    (allTapes : ∀ t,((preparedActive M p a).result.tape t).tape.steps ≤ tape)
    (allMasks : ∀ t z,(((preparedActive M p a).result.tape t).masks z).steps ≤ mask) :
    fixedActive (preparedActive M p a).result (reachable_positive T p.reached) T.vPositive ≤
      fixedArithmeticPx K tape mask := by
  let A := (preparedActive M p a).result
  let hp := reachable_positive T p.reached
  let HV := A.high hp
  let LV := T.bank c.prec hp
  let B := A.extraPrecision
  have a0 : (@centreA f ell s c) ≤ Nat.clog 2 s := bits_le_lam _ _
  have aK : (@centreA f ell s c) ≤ K := a0.trans (by have := ws.field; omega)
  have bK : B ≤ K := (Nat.le_add_left _ _).trans high
  have pK : c.prec ≤ K := (Nat.le_add_right _ _).trans high
  have field : f.natDegree ≤ K := by simpa only [cfg.coefficient] using ws.field
  have allCentres : A.centres.length ≤ K :=
    (retained_centre_count_le_grid A).trans
      ((Nat.pow_le_pow_right (by decide) (Nat.succ_le_succ a0)).trans
        ((Nat.le_add_right _ 1).trans cs.centreSlots))
  obtain ⟨uPos,uFit⟩ := (J6R12Integral.printedGuards cfg sel r T.rootStable).taper _ p.reached a
  have orderFit : 4*c.edges ≤ K :=
    (Nat.mul_le_mul_left _ (physical_edges_at_most_root_scale (cfg:=cfg) p T.rootStable)).trans cs.edges
  have centreBound (t : Center (printedParams (f:=f) (ell:=ell) s) c) :
      fixedCentre (A.tape t) T.vPositive HV B ≤ fixedCentrePx K tape mask := by
    let J := A.tape t
    have qty := actual_centre_dimension_fields (cfg:=cfg) p T.rootStable a t
    have n : @probeCount f ell s c ≤ K := qty.2.2.1.trans cs.probes
    have win : J.window ≤ K := qty.2.2.2.1.trans cs.edges
    have pLow : registerPrecision (printedParams (f:=f) (ell:=ell) s) c t ≤ K :=
      qty.2.2.2.2.2.1.trans ws.register
    have cnt : J.roster.rows.length+1 ≤ K :=
      (Nat.add_le_add_right (J.roster.length_le_grid.trans
        (Nat.pow_le_pow_right (by decide) (Nat.succ_le_succ a0))) 1).trans cs.centreSlots
    have weightTape : J.tape.result.words.length ≤ K :=
      (actual_weight_words_at_absolute_scale (cfg:=cfg) p T.rootStable J.tape.result).trans ws.weightTape
    exact actual_fixed_centre_physical_envelope J T.vPositive hf HV B field ws.baseV pLow high
      aK bK n win cnt uPos uFit orderFit ws.modeWord weightTape (allTapes t) (allMasks t)
  have total := (actual_list_charges A.centres (fun t=>fixedCentre (A.tape t) T.vPositive HV B)
      (fixedCentrePx K tape mask) (fun t _=>centreBound t)).trans
      (Nat.mul_le_mul_right _ allCentres)
  have ht : BitCaps HV.words.length ell (c.prec+B) K :=
    ⟨(HV.natDegree hf).le.trans field,ws.baseV,high⟩
  have hlow : BitCaps LV.words.length ell c.prec K :=
    ⟨(LV.natDegree hf).le.trans field,ws.baseV,pK⟩
  have hiUv := uv_word_cap ht
  have loUv := uv_word_cap hlow
  have hiAdd := addition_cap ht HV.hp
  have endFee := actual_strip_bound ht.degree ws.baseV high
  unfold fixedActive fixedArithmeticPx
  dsimp only
  gcongr

theorem actual_active_node_affine_with_paid_suppliers
    (M : OnlineMachine T key prec tw bw page q) (p : Path sel r c)
    (a : (printedParams (f:=f) (ell:=ell) s).cutoff<c.edges)
    (K tape mask setup mounted : ℕ)
    (ws : ActiveWidthScale (ell:=ell) (s:=s) (C:=C) (q:=q) (r:=r) K)
    (cs : PrintedCentreScale s C K)
    (high : c.prec+(preparedActive M p a).result.extraPrecision ≤ K)
    (allTapes : ∀ t,((preparedActive M p a).result.tape t).tape.steps ≤ tape)
    (allMasks : ∀ t z,(((preparedActive M p a).result.tape t).masks z).steps ≤ mask)
    (readyArithmetic : (preparedActive M p a).steps ≤ setup)
    (realMount : cacheMountFee M p ≤ mounted) :
    let A := preparedActive M p a
    cacheMountFee M p+A.steps+streamActiveTariff A.result (reachable_positive T p.reached) T.vPositive ≤
      (mounted+setup+fixedArithmeticPx K tape mask)+physicalAddressUnit K*Nat.card ((Plan sel).Slot c) := by
  apply real_active_phase_with_printed_fields M p a K _ ws
  exact Nat.add_le_add (Nat.add_le_add realMount readyArithmetic)
    (fixed_arithmetic_of_actual_prepared_machine M p a K tape mask ws cs high allTapes allMasks)

#print axioms actual_strip_bound
#print axioms fixed_arithmetic_of_actual_prepared_machine
#print axioms actual_active_node_affine_with_paid_suppliers
end
end J6R57ActiveFee
