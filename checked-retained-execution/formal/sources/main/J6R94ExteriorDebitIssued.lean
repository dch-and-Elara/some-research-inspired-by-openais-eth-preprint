import J6R94ExteriorDebitInput

/-! The stored public issue word is an actual data argument, not a
projection that might rebuild the source seed just to recover its key.
The seed occurs only in proofs certifying the known word and live atlas. -/
namespace J6R94ExteriorDebit
open scoped Classical Polynomial
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R64Active
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R30ProducedGateRegistry
open J6R32RootGeneratedRegistryInputs J6R34RootAtlas J6R31RootResidentTables
open J6R27OriginalGate J6Mesh J6R54ExteriorOwner J6R35RootOrigins
open J6R30GeneratedRootLayout J6R28GeneratedRootFrame J6R26StablePreparedRoot
open J6R32ChildResidentTransfer J6R12CollisionGreedyStep J6R68ActiveInputs
open J6R37StructuredRoot V8NativeMessage.N2DLabels J6OrientedHost J6R24LegalLayout

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 4200000
set_option maxRecDepth 4300
set_option Elab.async false
noncomputable section

variable {V : Type} [Fintype V] {m n base native : ℕ} {P : Plant V m n}
variable {f : ℤ[X]}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co dep edgew tc tj key prec tw bw own : ℕ}
variable (X : StableExterior G ell q ro co dep edgew tc tj key prec tw bw) (pad : ℕ)
variable {name : SourceVertex P→Word own} (S : RootLayoutStock P name)
variable (buf : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local instance issuedEdge : Fintype (Ext).host.Edge := (Ext).host.finiteEdge

def writeTargetsFromIssuedWord (known : Word key) : Meter (List Target) :=
  let old := trueOldKeyScan X S
  let pages := readMountedOwners buf known
  let cmd := writeTargets old.result ((pages.result.map Prod.snd).getD [])
  ⟨cmd.result,old.steps+pages.steps+cmd.steps+5⟩

theorem known_issued_word_reads_same_atlas_meter (known : Word key)
    (same : known=X.issue.result) :
    writeTargetsFromIssuedWord X pad S buf known=writeExteriorTargets X pad S buf := by
  have id : (X.seed pad).identifier=X.issue.result := (stable_exterior_header X).1
  have tag := same.trans id.symm
  unfold writeTargetsFromIssuedWord writeExteriorTargets currentPageKeys
  dsimp only
  rw [tag]

variable (live : IsLive (X.seed pad) buf) (head : OwnsHeader X.header.result buf)

def exteriorIngressFromIssued (known : Word key) (same : known=X.issue.result)
    (rank bits : ℕ) (fit : Fintype.card (Ext).host.Edge<2^rank) :
    Ingress (printedExteriorFull64 X pad S rank bits fit) :=
  let cmds := writeTargetsFromIssuedWord X pad S buf known
  let rows := writeExteriorIncidences X pad S buf
  { paid := ⟨(cmds.result,rows.result.getD []),cmds.steps+rows.steps+4⟩
    commands := (congrArg Meter.result (known_issued_word_reads_same_atlas_meter X pad S buf known same)).trans
      (real_exterior_targets_match_the_same_format X pad S buf live rank bits fit)
    incidences := (exteriorIngress X pad S buf live head rank bits fit).incidences }

theorem actual_issued_word_uses_the_same_checked_ingress (known : Word key)
    (same : known=X.issue.result) (rank bits : ℕ) (fit : Fintype.card (Ext).host.Edge<2^rank) :
    (exteriorIngressFromIssued X pad S buf live head known same rank bits fit).paid=
      (exteriorIngress X pad S buf live head rank bits fit).paid := by
  have H := known_issued_word_reads_same_atlas_meter X pad S buf known same
  unfold exteriorIngressFromIssued exteriorIngress
  dsimp only
  rw [H]

#print axioms known_issued_word_reads_same_atlas_meter
#print axioms exteriorIngressFromIssued
#print axioms actual_issued_word_uses_the_same_checked_ingress
end
end J6R94ExteriorDebit

