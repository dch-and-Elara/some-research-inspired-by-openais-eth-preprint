import J6R88ScopeCodeChoice

/-! One actual downstream creation on the stock R51 API. The new
mode-code word is selected before advance; no already installed parent
or older record is replaced. The source loader is executed once. -/
namespace J6R92NativeWidth
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R26DescriptorTree
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R34RootAtlas
open J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun
open J6R24MeteredRecursion J6R51Online J6R50SourceProducer J6R49SourceLayout
open J6R30ProducedGateRegistry J6R54PublicFamily J6R57ScopeFee J6R88ScopeCode J6R33GeneratedChildSite

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxRecDepth 4300
set_option maxHeartbeats 19000000

theorem smallest_code_fits_current_word {bw n old : ℕ}
    (oldPos : 0<old) (bound : old<2^bw) (fit : 1+n<2^old) :
    0<bw ∧ leastRosterCode n<2^bw ∧ 0<leastRosterCode n ∧ 1+n<2^leastRosterCode n := by
  have bwPos : 0<bw := by
    by_contra hn
    have e : bw=0 := by omega
    simp only [e,pow_zero] at bound
    omega
  exact ⟨bwPos,((exact_roster_code_fit _ _).1 fit).trans_lt bound,
    least_roster_code_positive _,(exact_roster_code_fit _ _).2 (Nat.le_refl _)⟩

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page rate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
variable {v : Ticket sel r} {X : StoredSite T v key prec tw bw page} {w : (Plan sel).Slot v.child}
variable {rank : ℕ} {U : ExplicitSelectedWords X.site w rank} {R : Replayed X.site w rank U}
local notation "Pg" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)

def minimalNativeEvent (E : NativeEventOnly (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) (page:=page) R) :
    NativeEventOnly (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) (page:=page) R :=
  let b := leastRosterCode R.resident.raw.roster.modes.length
  have count := raw_roster_clock R.certificate
  have oldFit : 1+R.resident.raw.roster.modes.length<2^E.code := by rw [count]; exact E.codeFit
  have room : E.code<2^bw := E.codeExact ▸ val_lt E.words.result.context.codeWidth
  let proof := smallest_code_fits_current_word E.codePos room oldFit
  let k := emitOrdinal bw b
  { E with
      code := b
      words := ⟨{ E.words.result with
        context := { E.words.result.context with codeWidth := k.result } },E.words.steps+k.steps+3⟩
      group := E.group
      clock := E.clock
      centre := E.centre
      codeExact := (emitted_ordinal_exact bw b proof.1 proof.2.1).1
      codePos := proof.2.2.1
      codeFit := by rw [← count]; exact proof.2.2.2
      acted := E.acted
      probe := E.probe }

def minimalLocalLoad (K : LocalLoad X w) : LocalLoad X w :=
  let E := minimalNativeEvent K.event
  let D := K.directory
  ⟨K.rankWidth,K.selectedWords,K.replay,E,
    ⟨D.k1,D.k2,D.ow,D.oldKey,D.owners,D.seats,D.queries,D.fallback,D.valid⟩⟩

theorem selected_local_load_keeps_exact_directory_and_roster (K : LocalLoad X w) :
    let next := minimalLocalLoad K
    next.directory.owners=K.directory.owners ∧ next.directory.seats=K.directory.seats ∧
    next.directory.queries=K.directory.queries ∧ next.replay.certificate.modes=K.replay.certificate.modes ∧
    next.event.words.result.exponents=K.event.words.result.exponents ∧
    next.event.words.result.context.center=K.event.words.result.context.center ∧
    next.advance.next.input.code=leastRosterCode next.advance.next.input.geometry.modes.length :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,congrArg leastRosterCode (raw_roster_clock K.replay.certificate)⟩

theorem minimal_loaded_word_is_charged_in_native_issuance (K : LocalLoad X w) :
    let k := leastRosterCode K.replay.resident.raw.roster.modes.length
    measuredWordProducers (minimalLocalLoad K).advance.next.input =
      measuredWordProducers K.advance.next.input+ordinalFee bw k+3 := by
  let E := K.event
  have room : E.code<2^bw := E.codeExact ▸ val_lt E.words.result.context.codeWidth
  have count := raw_roster_clock K.replay.certificate
  have oldFit : 1+K.replay.resident.raw.roster.modes.length<2^E.code := by rw [count]; exact E.codeFit
  have proof := smallest_code_fits_current_word E.codePos room oldFit
  let k := leastRosterCode K.replay.resident.raw.roster.modes.length
  have cost := (emitted_ordinal_exact bw k proof.1 proof.2.1).2
  change E.issued.steps+(E.native.steps+(selectedAdjacent K.replay).generated.steps+4+
    (replayChild X.site w K.rankWidth K.selectedWords).steps+
      (E.words.steps+(emitOrdinal bw k).steps+3)+4)=
    E.issued.steps+(E.native.steps+(selectedAdjacent K.replay).generated.steps+4+
      (replayChild X.site w K.rankWidth K.selectedWords).steps+E.words.steps+4)+ordinalFee bw k+3
  rw [cost]
  omega

def withMinimalDemand (M : OnlineMachine T key prec tw bw page rate) :
    OnlineMachine T key prec tw bw page rate :=
  { M with demand := fun X w =>
    let load := M.demand X w
    ⟨minimalLocalLoad load.result,load.steps⟩ }

theorem actual_minimal_demand_uses_one_existing_source
    (M : OnlineMachine T key prec tw bw page rate) (X : StoredSite T v key prec tw bw page)
    (w : (Plan sel).Slot v.child) :
    let before := M.demand X w
    let after := (withMinimalDemand M).demand X w
    after.steps=before.steps ∧ after.result=minimalLocalLoad before.result ∧
      after.result.event.code=leastRosterCode after.result.replay.resident.raw.roster.modes.length :=
  ⟨rfl,rfl,rfl⟩

theorem newly_coded_scope_does_not_change_its_old_directory {Out : Type}
    (M : OnlineMachine T key prec tw bw page rate) (X : StoredSite T v key prec tw bw page)
    (w : (Plan sel).Slot v.child) (retire : J→ℕ)
    (next : StoredSite T (J6R48RawRoute.successorTicket v w) key prec tw bw page→SM Pg Out)
    (bad : Meter Out) (B : Pg) :
    (openDemand ((withMinimalDemand M).demand X w) retire next bad B).result.2=B :=
  open_demand_restores ((withMinimalDemand M).demand X w) retire next bad B

#print axioms smallest_code_fits_current_word
#print axioms minimalNativeEvent
#print axioms minimalLocalLoad
#print axioms selected_local_load_keeps_exact_directory_and_roster
#print axioms minimal_loaded_word_is_charged_in_native_issuance
#print axioms actual_minimal_demand_uses_one_existing_source
#print axioms newly_coded_scope_does_not_change_its_old_directory
end
end J6R92NativeWidth
