import J6R116RetainedExteriorPeakActive
import J6R116RetainedFirstTariff
import J6R57ActiveFeeAffine
import J6R49CostActiveAddress

/-! Add the local first charges and true retained subtrees over exactly the
printed exterior slots, using the execution's original setup and sweep. -/
namespace J6R117RetainedExteriorClock
open scoped Polynomial Classical BigOperators
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R21Ancestor J6OrientedHost J6R34RootAtlas
open J6Mesh J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R28GeneratedRootFrame J6R34ChildPath J6R37StructuredRoot J6R41StructuredAllPaths
open J6R54TerminalBoot J6R53OldOwner J6R53OldOwnerRoot J6R26DescriptorTree J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion J6R52CacheSource
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS J6R10Repack J6ActiveSchedule
open J6R50SourceProducer J6R51Online J6R51ParentFrames J6R52CacheWhole J6R64Active J6R66Active
open J6R59Public J6R94HeldOwnerProvider J6R54PeakInput J6R48RawRoute J6R49SourceLayout
open J6R58RequestSource J6R52Dispatch J6R53Dispatch J6R27OriginalGate J6R36ChildFramedRoute
open J6R62ActivePrep J6R82LayoutDebit V8NativeMessage.N2DLabels J6R68ActiveInputs J6R68ActiveInputs.Sweep
open J6R9Recursive J6R22Active J6R49DFS J6R10Reachable
open J6R111KeptOwnerFlow J6R114RetainedPeak J6R115RetainedPeakPath
open J6R52Peak J6R53PeakAddon J6R55SelectedPeak J6R75RawPeak J6R66.BootPeak J6R16ModeCost
open J6R116RetainedExteriorPeak J6R116RetainedFirstTariff J6R49Cost J6R57ActiveFee J6R55CachedLedger

set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 6500000
set_option maxRecDepth 4900
set_option maxSynthPendingDepth 12
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C rate rank : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (initial : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
variable (boot : FirstSource X M) (E : ExteriorLabels X M boot rank)
variable (on : (printedParams (f:=f) (ell:=ell) s).cutoff<(exteriorChild G ell X.centre X.sample X.group).edges)

local notation "RootCall" => (exteriorChild G ell X.centre X.sample X.group)
local notation "RootPath" => (Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group)
  (exteriorChild G ell X.centre X.sample X.group))

local instance exteriorClockEdges : Fintype (RootCall).host.Edge := (RootCall).host.finiteEdge

variable (head : OwnsHeader X.header.result initial)
variable (D : KeptDrivers X M rank)
variable (retire : PageJob f ell key prec tw bw (pageKeyWidth m+pad)→ℕ)


/-- The actual exterior schedule. Its packed layout is not rebuilt
inside `exteriorRead`. -/
def exteriorSchedule :=
  let packed := exteriorPackedAtFirstScope X M boot E on
  let taper := actual_path_taper T RootPath on
  prepare (bank:=T.bank) M.modeWidth (D.fit RootPath on) taper.1 taper.2 X.hf
    D.masks.table (D.masks.covers RootPath on) (readExterior X initial head)
    ⟨packed.result.receipt,packed.steps⟩

def exteriorRead : ActiveChild (sel:=sel) (d:=readyAtPath T RootPath on) T.bank := fun t z β g=>
  let d := readyAtPath T RootPath on
  let u := addressed (sel:=sel) d t z β g
  let packed := exteriorPackedAtFirstScope X M boot E on
  project (firstCallbackFromActualPackedResult X M initial boot E on u D retire packed.result rfl
    (zeroM (T.bank (registerPrecision (printedParams (f:=f) (ell:=ell) s) RootCall t)
      (register_positive d t)).hp))

/-- The local setup and the exact current child's execution are distinct
charges for each real issued address. -/
def firstSlotBill (w : (Plan sel).Slot RootCall) : ℕ :=
  firstCarrierDebit X M initial boot w retire+
    (runRetained X M D retire (firstInvocation X M initial boot E on w)).steps

local notation "ScheduleAt" => (exteriorSchedule X M initial boot E on head D)
local notation "ReadAt" => (exteriorRead X M initial boot E on D retire)
local notation "Paid" => (runRetainedExterior X M initial head boot D E retire)

private theorem each_exterior_read_pays_the_actual_first_slot
    (valid : ReadyOnStack (borns M) initial)
    (t : Center (printedParams (f:=f) (ell:=ell) s) RootCall)
    (z : Probe (printedParams (f:=f) (ell:=ell) s) RootCall)
    (β : NativeMenu (N sel) RootCall t) (g : Fin 64) :
    let d := readyAtPath T RootPath on
    (ReadAt t z β g).steps=
      firstSlotBill X M initial boot E on D retire (addressed (sel:=sel) d t z β g) := by
  let d := readyAtPath T RootPath on
  let w := addressed (sel:=sel) d t z β g
  let packed := exteriorPackedAtFirstScope X M boot E on
  let low := T.bank (registerPrecision (printedParams (f:=f) (ell:=ell) s) RootCall t)
    (register_positive d t)
  let bad : Meter (Block low ell) := zeroM low.hp
  have borrowed := the_borrowed_first_callback_is_the_observed_native_stage X M initial boot E on w
    D retire packed.result rfl bad
  have paid := the_actual_first_scope_resumes_this_same_observed_invocation X M initial boot E on w
    D retire valid bad
  let child := runRetained X M D retire (firstInvocation X M initial boot E on w)
  let next := (boot.make w).result.site
  let j := next.birth.job
  let a := (boot.make w).steps
  let b := publishFee initial j.entry j.offset j.built
  let c := (installResidentBank next).steps
  let dFee := retire j
  change (firstCallbackFromActualPackedResult X M initial boot E on w D retire packed.result rfl bad).steps=_
  calc
    _ = (actualExteriorFirstCallback X M initial boot E on w D retire bad).steps := congrArg Meter.steps borrowed
    _ = a+(b+(c+child.steps)+dFee+4) := congrArg Meter.steps paid
    _ = _ := regroup_actual_first_receipt a b c dFee child.steps

theorem actual_exterior_active_clock_sums_the_issued_first_slots
    (valid : ReadyOnStack (borns M) initial)
    (fixed unit : ℕ)
    (rootPrefixCap : (ScheduleAt).steps+(fixedActive (ScheduleAt).result.proofView
      (reachable_positive T (RootPath).reached) T.vPositive)≤fixed)
    (perMode : ∀ t∈(ScheduleAt).result.proofView.centres,
      unitMode ((ScheduleAt).result.proofView.tape t).low ((ScheduleAt).result.proofView.tape t).tape.result≤64*unit) :
    letI : Fintype ((Plan sel).Slot RootCall) := (Plan sel).finiteSlot RootCall
    (Paid).steps ≤ fixed+unit*Nat.card ((Plan sel).Slot RootCall)+
      ∑ w : (Plan sel).Slot RootCall, firstSlotBill X M initial boot E on D retire w := by
  let A := ScheduleAt
  let read := ReadAt
  let hp := reachable_positive T (RootPath).reached
  let fee := firstSlotBill X M initial boot E on D retire
  letI : Fintype ((Plan sel).Slot RootCall) := (Plan sel).finiteSlot RootCall
  have same : (Paid).steps=A.steps+(A.result.eval M.modeWidth hp T.vPositive X.hf read).steps :=
    congrArg Meter.steps (original_exterior_runs_the_first_scopes_with_one_shared_packed_output
      X M initial boot E on head D retire)
  have taper := actual_path_taper T RootPath on
  have sweep : (A.result.eval M.modeWidth hp T.vPositive X.hf read).steps≤
      streamActiveChildBill A.result.proofView read+streamActiveTariff A.result.proofView hp T.vPositive := by
    rw [Schedule.exact_sweep_matches_its_own_proof_view]
    exact actual_stream_active_word_meter A.result.proofView M.modeWidth hp T.vPositive X.hf taper.1 taper.2 read
  have census : streamActiveChildBill A.result.proofView read=∑ w : (Plan sel).Slot RootCall,fee w :=
    stream_active_child_bill_matches_slots A.result.proofView T.vPositive read fee
      (each_exterior_read_pays_the_actual_first_slot X M initial boot E on D retire valid)
  have arith := active_arithmetic_charged_against_actual_slots A.result.proofView hp T.vPositive unit perMode
  change (Paid).steps≤fixed+unit*Nat.card ((Plan sel).Slot RootCall)+∑ w : (Plan sel).Slot RootCall,fee w
  rw [same]
  change A.steps+fixedActive A.result.proofView hp T.vPositive≤fixed at rootPrefixCap
  rw [census] at sweep
  omega

#print axioms exteriorSchedule
#print axioms exteriorRead
#print axioms actual_exterior_active_clock_sums_the_issued_first_slots
end
end J6R117RetainedExteriorClock
