import J6R102NativeCodeMeterSource

/-! Demand on the actual current StoredSite. Use the input supplier once,
then the scan, then the new ordinal word from that scan. The returned
LocalLoad agrees with R92; its outer debit is strictly a new receipt. -/
namespace J6R102NativeCodeMeter
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R26DescriptorTree
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R34RootAtlas
open J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun
open J6R24MeteredRecursion J6R51Online J6R50SourceProducer J6R49SourceLayout
open J6R30ProducedGateRegistry J6R54PublicFamily J6R57ScopeFee J6R88ScopeCode
open J6R33GeneratedChildSite J6R92NativeWidth J6R17ModeTape J6R14LayoutCost
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxRecDepth 5000
set_option maxHeartbeats 22000000
set_option maxSynthPendingDepth 12

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page rate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
variable {v : Ticket sel r} {X : StoredSite T v key prec tw bw page} {w : (Plan sel).Slot v.child}
variable {rank : ℕ} {U : ExplicitSelectedWords X.site w rank} {R : Replayed X.site w rank U}

def putEvent (E : NativeEventOnly (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) (page:=page) R)
    (k : ℕ) (W : Meter (Word bw)) (value : W.result.val=k) (pos : 0<k)
    (fit : 1+R.certificate.modes.length<2^k) :
    NativeEventOnly (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) (page:=page) R :=
  { E with
      code := k
      words := ⟨{ E.words.result with context := { E.words.result.context with codeWidth := W.result } },
        E.words.steps+W.steps+3⟩
      group := E.group
      clock := E.clock
      centre := E.centre
      codeExact := value
      codePos := pos
      codeFit := fit
      acted := E.acted
      probe := E.probe }

def putLoad (K : LocalLoad X w) (k : ℕ) (W : Meter (Word bw))
    (value : W.result.val=k) (pos : 0<k) (fit : 1+K.replay.certificate.modes.length<2^k) :
    LocalLoad X w :=
  let E := putEvent K.event k W value pos fit
  let D := K.directory
  ⟨K.rankWidth,K.selectedWords,K.replay,E,
    ⟨D.k1,D.k2,D.ow,D.oldKey,D.owners,D.seats,D.queries,D.fallback,D.valid⟩⟩

theorem put_load_matches_old_when_word_matches
    (K : LocalLoad X w) (k : ℕ) (W : Meter (Word bw))
    (value : W.result.val=k) (pos : 0<k) (fit : 1+K.replay.certificate.modes.length<2^k)
    (hk : k=leastRosterCode K.replay.resident.raw.roster.modes.length)
    (hw : W=emitOrdinal bw (leastRosterCode K.replay.resident.raw.roster.modes.length)) :
    putLoad K k W value pos fit=minimalLocalLoad K := by
  subst hk
  subst hw
  rfl

def measureLocalLoad (K : LocalLoad X w) : Meter (LocalLoad X w) :=
  let xs := K.replay.resident.raw.roster.modes
  let C := selectCode bw xs
  have law := selected_native_code_is_legal xs (raw_roster_clock K.replay.certificate)
    K.event.codePos (K.event.codeExact ▸ val_lt K.event.words.result.context.codeWidth) K.event.codeFit
  ⟨putLoad K C.result.k C.result.write law.2.2.1 law.2.2.2.1 law.2.2.2.2,C.steps⟩

theorem actual_measured_load_retains_r92_and_pays_count (K : LocalLoad X w) :
    let E := measureLocalLoad K
    E.result=minimalLocalLoad K ∧ E.steps=(countModes K.replay.resident.raw.roster.modes).steps := by
  let xs := K.replay.resident.raw.roster.modes
  have law := selected_native_code_is_legal xs (raw_roster_clock K.replay.certificate)
    K.event.codePos (K.event.codeExact ▸ val_lt K.event.words.result.context.codeWidth) K.event.codeFit
  exact ⟨put_load_matches_old_when_word_matches K _ _ _ _ _ law.1 law.2.1,rfl⟩

def withPaidDemand (M : OnlineMachine T key prec tw bw page rate) :
    OnlineMachine T key prec tw bw page rate :=
  { M with demand := fun X w => (M.demand X w).bind measureLocalLoad }

theorem real_demand_returns_r92_and_bills_the_actual_count_once
    (M : OnlineMachine T key prec tw bw page rate) (X : StoredSite T v key prec tw bw page)
    (w : (Plan sel).Slot v.child) :
    let K := M.demand X w
    let D := (withPaidDemand M).demand X w
    D.result=((withMinimalDemand M).demand X w).result ∧
      D.steps=K.steps+(countModes K.result.replay.resident.raw.roster.modes).steps := by
  obtain ⟨hr,hc⟩ := actual_measured_load_retains_r92_and_pays_count (M.demand X w).result
  exact ⟨hr,congrArg ((M.demand X w).steps+·) hc⟩

#print axioms putEvent
#print axioms putLoad
#print axioms put_load_matches_old_when_word_matches
#print axioms measureLocalLoad
#print axioms actual_measured_load_retains_r92_and_pays_count
#print axioms real_demand_returns_r92_and_bills_the_actual_count_once
end
end J6R102NativeCodeMeter
