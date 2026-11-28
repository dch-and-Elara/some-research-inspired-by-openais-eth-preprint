import J6R55PublicDemand
import J6R68RateJointShell
import J6R102NativeCodeMeterDemand

/-! Exact producer accounting for the selected R55 request followed by
R102's actual mode-code measurement. There is no unidentified local load
fee and no inference of demand time from its answer. -/
namespace J6R110ScopeWordRates
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R26DescriptorTree J6R48RawRoute
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R49SourceLayout J6R50SourceProducer J6R51Online
open J6R52Dispatch J6R53Dispatch J6R54Dispatch J6R55Dispatch J6R55Public J6R54PublicFamily
open J6R57ScopeFee J6R68RateJoint J6R88ScopeCode J6R92NativeWidth J6R102NativeCodeMeter

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 12500000
set_option maxRecDepth 4900
set_option maxSynthPendingDepth 12
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page rate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
variable {v : Ticket sel r} {X : StoredSite T v key prec tw bw page} {w : (Plan sel).Slot v.child}

/-- The selected raw dispatcher pays its own search separately. The old
source word part below charges its concrete increment, copies, and replay. -/
theorem R55_selected_source_words_use_the_literal_shell_tariff
    (I : Meter (FixedRequest X w)) (K : ℕ)
    (keyPos : 0<key) (keyRoom : X.birth.job.identifier.val+1<2^key)
    (keyW : key≤K) (depthW : I.result.shell.dep≤K) (precW : prec≤K) (timeW : tw≤K)
    (codeW : bw≤K) (lamW : Nat.clog 2 s≤K) :
    measuredWordProducers (meteredSelectedDemand I).result.advance.next.input ≤
      nextPortWordsTariff (X:=X) I.result.q+
        selectedResidentWordsTariff (X:=X) (w:=w) I.result.emitted+(40*K+45) := by
  let Q := I.result
  let chosen := (Q.find Q.raw Q.group).result.get Q.hit
  let shell := usingParentIssuer Q.replay Q.shell
  let dir := usingParentIssuerDirectory Q.replay Q.shell Q.directory
  let paid := chosen.val.dispatch
  let evidence := chosen.val.dispatch_checked.1
  let words := paid.result.get (checker_returns_available Q.replay evidence)
  let law := actual_checked_bytes Q.replay evidence
  have cap := actual_shell_source_words_from_finite_copy_widths Q.replay shell dir
    words.centre words.probe words.mode words.group law.centre law.probe law.mode law.group
    words.exponents law.exponents rfl keyPos keyRoom K keyW depthW precW timeW codeW lamW
  exact cap

/-- The new code means an additional actual ordinal write. Its exact
cost is charged to the same newly created occurrence; the mode-count scan
stays in the measured demand, where its own proof places it. -/
theorem R102_selected_source_words_include_new_code_and_keep_shell_prices
    (I : Meter (FixedRequest X w)) (K : ℕ)
    (keyPos : 0<key) (keyRoom : X.birth.job.identifier.val+1<2^key)
    (keyW : key≤K) (depthW : I.result.shell.dep≤K) (precW : prec≤K) (timeW : tw≤K)
    (codeW : bw≤K) (lamW : Nat.clog 2 s≤K) :
    let original := (meteredSelectedDemand I).result
    let actual := (measureLocalLoad original).result
    let code := leastRosterCode original.replay.resident.raw.roster.modes.length
    measuredWordProducers actual.advance.next.input ≤
      nextPortWordsTariff (X:=X) I.result.q+selectedResidentWordsTariff (X:=X) (w:=w) I.result.emitted+
        (40*K+45)+ordinalFee bw code+3 := by
  let original := (meteredSelectedDemand I).result
  have same := (actual_measured_load_retains_r92_and_pays_count original).1
  dsimp only
  rw [same, minimal_loaded_word_is_charged_in_native_issuance]
  exact Nat.add_le_add_right (Nat.add_le_add_right
    (R55_selected_source_words_use_the_literal_shell_tariff I K keyPos keyRoom keyW depthW precW timeW codeW lamW) _) _

end
#print axioms R55_selected_source_words_use_the_literal_shell_tariff
#print axioms R102_selected_source_words_include_new_code_and_keep_shell_prices
end J6R110ScopeWordRates