import J6R92NativeWidthDemand
import J6R55TerminalBootJoinedCore

/-! The stock first-slot publisher still uses the real physical writer
and live owner mount; only a new template's mode-width word is chosen.
Its atlas page-address encoding is independent of that choice, so the
same paid boot port/owner bytes are retained. -/
namespace J6R92NativeWidth
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R26DescriptorTree
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R34RootAtlas
open J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun
open J6R24MeteredRecursion J6R51Online J6R50SourceProducer J6R49SourceLayout
open J6R30ProducedGateRegistry J6R54PublicFamily J6R57ScopeFee J6R88ScopeCode J6R33GeneratedChildSite
open J6R55BootBodies J6R55TerminalOrigin J6R48GeneratedAddons
open J6Mesh J6OrientedHost J6R24LegalLayout J6R31RootResidentTables
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R32RootGeneratedRegistryInputs
open J6R35RootOrigins J6R55TerminalBootJoined J6R53OldOwnerRoot J6R54TerminalBoot J6R54ExteriorOwner

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxRecDepth 4700
set_option maxHeartbeats 22000000
set_option maxSynthPendingDepth 12

noncomputable section
section Template
variable {f : ℤ[X]} {ell s C key prec tw bw page own : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
variable {v : Ticket sel r}

def minimumNewTemplate (I : OccurrenceInput T v key prec tw bw page) :
    OccurrenceInput T v key prec tw bw page :=
  let k := leastRosterCode I.physical.result.raw.roster.modes.length
  have cnt := raw_roster_clock I.geometry
  have oldFit : 1+I.physical.result.raw.roster.modes.length<2^I.code := by rw [cnt]; exact I.codeFit
  have room : I.code<2^bw := I.codeExact ▸ val_lt I.words.result.context.codeWidth
  let D := smallest_code_fits_current_word I.codePos room oldFit
  emitWidthBeforePublication I k D.1 D.2.1 D.2.2.1 (by rw [←cnt]; exact D.2.2.2)

theorem minimum_new_template_word_paid
    (I : OccurrenceInput T v key prec tw bw page) :
    let k := leastRosterCode I.physical.result.raw.roster.modes.length
    (minimumNewTemplate I).words.steps=I.words.steps+ordinalFee bw k+3 := by
  let k := leastRosterCode I.physical.result.raw.roster.modes.length
  have cnt := raw_roster_clock I.geometry
  have oldFit : 1+I.physical.result.raw.roster.modes.length<2^I.code := by rw [cnt]; exact I.codeFit
  have room : I.code<2^bw := I.codeExact ▸ val_lt I.words.result.context.codeWidth
  have F := smallest_code_fits_current_word I.codePos room oldFit
  change I.words.steps+(emitOrdinal bw k).steps+3=I.words.steps+ordinalFee bw k+3
  rw [(emitted_ordinal_exact bw k F.1 F.2.1).2]

theorem template_code_selection_preserves_page_key
    (I : OccurrenceInput T v key prec tw bw page) :
    occurrencePageWord (minimumNewTemplate I)=occurrencePageWord I := rfl

/-- Reindex only the proof fields on the already measured seat/query
words. No actual word or already existing compiled ancestor is edited. -/
def retieBootPorts {I I' : OccurrenceInput T v key prec tw bw page}
    {name : v.parent.host.Row⊕v.parent.host.Col → Word own}
    (D : BootPortWords I name) (samePage : occurrencePageWord I'=occurrencePageWord I) :
    BootPortWords I' name where
  seatWidth := D.seatWidth
  seats := D.seats
  queries := D.queries
  ownerQuery := D.ownerQuery
  sideExact := D.sideExact
  seatHit := fun h=>by rw [samePage]; exact D.seatHit h
  seatUnique := fun h x here eq=>by rw [samePage]; exact D.seatUnique h x here eq
  fallback := D.fallback

theorem retied_ports_use_original_paid_rows {I I' : OccurrenceInput T v key prec tw bw page}
    {name : v.parent.host.Row⊕v.parent.host.Col → Word own}
    (D : BootPortWords I name) (samePage : occurrencePageWord I'=occurrencePageWord I) :
    (retieBootPorts D samePage).seats=D.seats ∧
      (retieBootPorts D samePage).queries=D.queries := ⟨rfl,rfl⟩
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
variable (A : FirstBodyProgram X gate pad T)

def minimalFirstProgram : FirstBodyProgram X gate pad T :=
  { A with old := fun w =>
    let original := A.old w
    ⟨minimumNewTemplate original.result, original.steps⟩ }

theorem literal_first_body_uses_the_new_width_and_same_physical_writer (w : Slot) :
    let N := bodyAtActualSlot X gate pad (minimalFirstProgram X gate pad A) w
    let O := bodyAtActualSlot X gate pad A w
    N.result.code=leastRosterCode N.result.geometry.modes.length ∧
      N.result.native.result.physical.raw=O.result.native.result.physical.raw ∧
      N.result.geometry.modes=O.result.geometry.modes ∧
      occurrencePageWord N.result=occurrencePageWord O.result ∧
      N.steps=O.steps :=
  ⟨congrArg leastRosterCode (raw_roster_clock (A.old w).result.geometry),rfl,rfl,rfl,rfl⟩

theorem first_code_appears_in_its_actually_consumed_word_debit (w : Slot) :
    let W := (bodyAtActualSlot X gate pad (minimalFirstProgram X gate pad A) w).result
    let O := (bodyAtActualSlot X gate pad A w).result
    W.words.steps=O.words.steps+ordinalFee bw (leastRosterCode O.physical.result.raw.roster.modes.length)+3 :=
  minimum_new_template_word_paid (A.old w).result

variable {own rate : ℕ} {rootName : SourceVertex P→Word own}
variable (root : RootRoster (P:=P) gate pad rootName)
variable (D : OwnerWordsAtBodies X gate pad root A)

def minimalFirstOwners : OwnerWordsAtBodies X gate pad root (minimalFirstProgram X gate pad A) where
  width := D.width
  name := D.name
  distinct := D.distinct
  keys := D.keys
  ports := fun w=>retieBootPorts (D.ports w)
    (literal_first_body_uses_the_new_width_and_same_physical_writer X gate pad A w).2.2.2.1

theorem same_paid_first_ports_under_minimum_code (w : Slot) :
    let L := minimalFirstOwners X gate pad A root D
    (L.ports w).seats=(D.ports w).seats ∧ (L.ports w).queries=(D.ports w).queries := ⟨rfl,rfl⟩

#print axioms minimumNewTemplate
#print axioms minimum_new_template_word_paid
#print axioms template_code_selection_preserves_page_key
#print axioms retied_ports_use_original_paid_rows
#print axioms minimalFirstProgram
#print axioms literal_first_body_uses_the_new_width_and_same_physical_writer
#print axioms first_code_appears_in_its_actually_consumed_word_debit
#print axioms minimalFirstOwners
#print axioms same_paid_first_ports_under_minimum_code
end
end J6R92NativeWidth
