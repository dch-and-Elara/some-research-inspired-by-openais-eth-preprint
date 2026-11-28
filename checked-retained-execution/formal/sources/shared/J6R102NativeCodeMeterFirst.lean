import J6R102NativeCodeMeterSource
import J6R92NativeWidthFirst

/-! Run the same prepublication count on the original first template
and give its exact emitted word to the native compiler. The outer
boot reads/charges the already measured physical writer as before. -/
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
open J6R55BootBodies J6R55TerminalOrigin J6R48GeneratedAddons J6R48RawRoute
open J6Mesh J6OrientedHost J6R24LegalLayout J6R31RootResidentTables
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R32RootGeneratedRegistryInputs
open J6R35RootOrigins J6R55TerminalBootJoined J6R53OldOwnerRoot J6R54TerminalBoot J6R54ExteriorOwner

noncomputable section
section Template
variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
variable {v : Ticket sel r}

def putTemplate (I : OccurrenceInput T v key prec tw bw page) (k : ℕ) (W : Meter (Word bw))
    (value : W.result.val=k) (pos : 0<k) (fit : 1+I.geometry.modes.length<2^k) :
    OccurrenceInput T v key prec tw bw page :=
  { I with
      code := k
      words := ⟨{ I.words.result with context := { I.words.result.context with codeWidth := W.result } },
        I.words.steps+W.steps+3⟩
      group := I.group
      clock := I.clock
      centre := I.centre
      codeExact := value
      codePos := pos
      codeFit := fit
      acted := I.acted
      probe := I.probe }

theorem put_template_matches_old_when_word_matches
    (I : OccurrenceInput T v key prec tw bw page) (k : ℕ) (W : Meter (Word bw))
    (value : W.result.val=k) (pos : 0<k) (fit : 1+I.geometry.modes.length<2^k)
    (hk : k=leastRosterCode I.physical.result.raw.roster.modes.length)
    (hw : W=emitOrdinal bw (leastRosterCode I.physical.result.raw.roster.modes.length)) :
    putTemplate I k W value pos fit=minimumNewTemplate I := by
  subst hk
  subst hw
  rfl

def measureTemplate (I : OccurrenceInput T v key prec tw bw page) :
    Meter (OccurrenceInput T v key prec tw bw page) :=
  let xs := I.physical.result.raw.roster.modes
  let C := selectCode bw xs
  have law := selected_native_code_is_legal xs (raw_roster_clock I.geometry)
    I.codePos (I.codeExact ▸ val_lt I.words.result.context.codeWidth) I.codeFit
  ⟨putTemplate I C.result.k C.result.write law.2.2.1 law.2.2.2.1 law.2.2.2.2,C.steps⟩

theorem actual_measured_template_retains_r92_and_pays_count (I : OccurrenceInput T v key prec tw bw page) :
    let E := measureTemplate I
    E.result=minimumNewTemplate I ∧ E.steps=(countModes I.physical.result.raw.roster.modes).steps := by
  let xs := I.physical.result.raw.roster.modes
  have law := selected_native_code_is_legal xs (raw_roster_clock I.geometry)
    I.codePos (I.codeExact ▸ val_lt I.words.result.context.codeWidth) I.codeFit
  exact ⟨put_template_matches_old_when_word_matches I _ _ _ _ _ law.1 law.2.1,rfl⟩

end Template

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
variable {s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "Slot" => ((Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group))
local notation "Pg" => (pageKeyWidth m+pad)
local notation "TicketAt" => (fun w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group) =>
  (Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group)
    (exteriorChild G ell X.centre X.sample X.group)).ticket w)
variable (A : FirstBodyProgram X gate pad T)

def measuredFirstProgram : FirstBodyProgram X gate pad T :=
  { A with old := fun w => (A.old w).bind measureTemplate }

theorem measured_first_body_same_and_pays_actual_count (w : Slot) :
    let before := bodyAtActualSlot X gate pad (minimalFirstProgram X gate pad A) w
    let after := bodyAtActualSlot X gate pad (measuredFirstProgram X gate pad A) w
    after.result=before.result ∧ after.steps=before.steps+
      (countModes before.result.physical.result.raw.roster.modes).steps := by
  let I := A.old w
  let P₁ := readFirstPhysical X gate pad A.lanes (A.seats w)
  obtain ⟨hr,hc⟩ := actual_measured_template_retains_r92_and_pays_count I.result
  constructor
  · change replaceOccurrencePhysical (measureTemplate I.result).result ⟨P₁.result,0⟩ =
      replaceOccurrencePhysical (minimumNewTemplate I.result) ⟨P₁.result,0⟩
    rw [hr]
  · change I.steps+(measureTemplate I.result).steps+P₁.steps+4 =
      I.steps+P₁.steps+4+(countModes I.result.physical.result.raw.roster.modes).steps
    rw [hc]
    omega

#print axioms putTemplate
#print axioms put_template_matches_old_when_word_matches
#print axioms measureTemplate
#print axioms actual_measured_template_retains_r92_and_pays_count
#print axioms measured_first_body_same_and_pays_actual_count
end
end J6R102NativeCodeMeter