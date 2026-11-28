import J6R57ActiveFeeAffine
import J6R57ActiveFeeArithmetic
import J6R57ActiveFeeGeometry
import J6R56PrintedExponentPhases

/-! Instantiate the active field of the exact R56 phase contract.
The arithmetic per native address is derived from the real width
tape and physical precision. Only the fixed preparation/interpolation
bill and the other two phases remain explicit. -/
namespace J6R57ActiveFee
open scoped Polynomial Classical BigOperators
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active
open J1PPrinted J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R24MeteredRecursion J6R49DFS J6R49Cost J6R50Peak
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R51Online J6R55CachedLedger
open J6R56PrintedExponent

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 14500000
set_option maxRecDepth 3550
set_option linter.unusedSectionVars false
set_option Elab.async false

def physicalAddressUnit (K : ℕ) : ℕ := (250000*(K+1)^6)/64+1

theorem actual_unit_paid_by_shared_groups (K : ℕ) :
    250000*(K+1)^6 ≤ 64*physicalAddressUnit K := by
  let m := 250000*(K+1)^6
  have h := Nat.mod_add_div m 64
  have gt := Nat.mod_lt m (by decide : 0<(64:ℕ))
  unfold physicalAddressUnit
  change m ≤ 64*(m/64+1)
  omega

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}

structure ActiveWidthScale (K : ℕ) : Prop where
  field : 4*Nat.clog 2 s ≤ K
  baseV : ell ≤ K
  modeWord : q ≤ K
  register : absolutePrecision s r.edges r.prec ≤ K
  weightTape : 6*(C*s)*absolutePrecision s r.edges r.prec ≤ K

theorem real_active_phase_with_printed_fields
    (M : OnlineMachine T key prec tw bw page q) (p : Path sel r c)
    (a : (printedParams (f:=f) (ell:=ell) s).cutoff<c.edges)
    (K fixed : ℕ) (ws : ActiveWidthScale (ell:=ell) (s:=s) (C:=C) (q:=q) (r:=r) K)
    (once :
      let A := preparedActive M p a
      cacheMountFee M p + A.steps + fixedActive A.result (reachable_positive T p.reached) T.vPositive ≤ fixed) :
    let A := preparedActive M p a
    cacheMountFee M p+A.steps+streamActiveTariff A.result (reachable_positive T p.reached) T.vPositive ≤ fixed+physicalAddressUnit K*Nat.card ((Plan sel).Slot c) := by
  apply actual_active_phase_from_its_split_bill M p a fixed (physicalAddressUnit K) once
  dsimp only
  intro t _
  let A := preparedActive M p a
  let J := A.result.tape t
  have e : J.low.words.length ≤ K := (J.low.natDegree hf).le.trans (by simpa only [cfg.coefficient] using ws.field)
  have reg := (absolute_register_precision_cap cfg sel T.rootStable p a t).trans ws.register
  have count := (actual_weight_words_at_absolute_scale (cfg:=cfg) p T.rootStable J.tape.result).trans ws.weightTape
  exact (mode_phase_physical_poly J.low.hp e ws.baseV reg ws.modeWord count).trans
    (actual_unit_paid_by_shared_groups K)

theorem active_source_caps_fit_exact_r56
    (M : OnlineMachine T key prec tw bw page q)
    (retire : PageJob f ell key prec tw bw page→ℕ) (initial : PageBank f ell key prec tw bw page)
    (K fixed scope : ℕ) (ws : ActiveWidthScale (ell:=ell) (s:=s) (C:=C) (q:=q) (r:=r) K)
    (leaf : ∀ (z : Sigma (Path sel r)) (stop : z.1.edges ≤ (printedParams (f:=f) (ell:=ell) s).cutoff),
      (readLeaf M initial z.2 stop).steps ≤ fixed)
    (once : ∀ (z : Sigma (Path sel r))
      (a : (printedParams (f:=f) (ell:=ell) s).cutoff<z.1.edges),
      let A := preparedActive M z.2 a
      cacheMountFee M z.2 + A.steps + fixedActive A.result (reachable_positive T z.2.reached) T.vPositive ≤ fixed)
    (visits : ∀ (z : Sigma (Path sel r)) (w : (Plan sel).Slot z.1),
      cachedScopeOwn M retire initial z.2 w ≤ scope) :
    CachedThreePhaseCaps M retire initial fixed (physicalAddressUnit K) scope :=
  ⟨leaf,(fun z a=>real_active_phase_with_printed_fields M z.2 a K fixed ws (once z a)),visits⟩

#print axioms actual_unit_paid_by_shared_groups
#print axioms real_active_phase_with_printed_fields
#print axioms active_source_caps_fit_exact_r56
end
end J6R57ActiveFee
