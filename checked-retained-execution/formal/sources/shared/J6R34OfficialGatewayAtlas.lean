import J6R34OfficialGatewayCore
import J6R34RootAtlasJoin

/-! Bind the grouped oracle to the actual paged constructor and its
actual stateful execution for the very same exterior physical child.
A job still explicitly supplies metered descendant ingredients,
checked inherited routing, and legal occurrence identifiers. -/
namespace J6R34OfficialGateway
open scoped Classical Polynomial BigOperators
open Polynomial AOracleMachineTime A1R10
open J6Mesh J6OrientedHost P11FullPacking J6R24LegalLayout J6R24MeteredRecursion
open J6R32RootGeneratedRegistryInputs J6R34RootAtlas J6R31RootResidentTables
open J6R26StablePreparedRoot J6R27PrescribedProbe J6R14ZeroMode
open J6R33StatefulArithmeticPage J6R32StatefulArithmetic J6R9Recursive
open J6R10Reachable J6R12Blueprint J6R11Blueprint J6ActiveRun J1PPrinted
open J6R30ProducedGateRegistry J6R21Ancestor
set_option maxHeartbeats 14500000
set_option maxRecDepth 2400
set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q rr cc dd edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q rr cc dd edgew tc tj key prec tw bw)
variable (pad : ℕ)

noncomputable abbrev askedJobChild := exteriorChild G ell X.centre X.sample X.group

noncomputable local instance childDecision :
    DecidableEq (J6R10Reachable.Envelope (N (G.selector ell)) (Childs (G.selector ell)) (askedJobChild X)) :=
  sourceDecision (G.selector ell) (askedJobChild X)

structure AtlasJob where
  tree : Prepared G.bounds (G.selector ell)
    (exteriorChild G ell X.centre X.sample X.group) X.hf
  inputs : InputFamily tree key prec tw bw (pageKeyWidth m+pad)
  inherited : RoutedInputs inputs (X.seed pad)
  bank : PageBank f ell key prec tw bw (pageKeyWidth m+pad)
  ready : JobsReady bank (X.seed pad::
    (pagedLog (compilerResident inputs (X.seed pad) inherited) (exteriorChild G ell X.centre X.sample X.group) .root).jobs)

noncomputable def AtlasJob.run (A : AtlasJob X pad) :
    Meter (Block (A.tree.frame (.reflexive (askedJobChild X))) ell ×
      PageBank f ell key prec tw bw (pageKeyWidth m+pad)) :=
  startFromAtlas (compilerResident A.inputs (X.seed pad) A.inherited) (X.seed pad) A.bank

theorem paid_atlas_child [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (A : AtlasJob X pad) :
    let s := X.seed pad
    let live := compilerResident A.inputs s A.inherited
    let child := askedJobChild X
    let log := Log.enter s (pagedLog live child .root)
    let out := A.run
    (A.tree.frame (.reflexive child)).decode out.result.1=
      reduce child.prec f ell (child.host.contract X.hf) ∧
    out.result.2=afterJobs A.bank log.jobs ∧
    out.steps=(reference A.tree child (.reflexive child)).steps+
      chronologicalBill A.bank log.jobs+log.extras A.bank := by
  letI := childDecision X
  have h := actual_prescribed_atlas_and_child_execution (P:=A.tree) X pad A.inputs A.inherited A.bank A.ready
  exact ⟨h.1,h.2.1,h.2.2.1⟩

noncomputable def receiptFromAtlas [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (A : AtlasJob X pad) : GroupReceipt (ell:=ell) G X.hf X.centre X.sample X.group where
  frame := A.tree.frame (.reflexive (askedJobChild X))
  run := ⟨A.run.result.1,A.run.steps⟩
  truth := (paid_atlas_child X pad A).1

theorem installed_atlas_has_same_raw_probe [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (A : AtlasJob X pad) (k : Page (a m) (K m) (Fin 64)) :
    let expected := writtenProbe (ell:=ell) G X.sample
    let probeBank := buildRootBitBank G ell
    expected=(probeBank.result.read X.sample).result.val ∧
    expected=AOracleMachineTimeTape.encodeBits f.natDegree (X.sample.val+1) ∧
    (locate (widened pad (residentPageKey m k)).result (X.seed pad).immutable.payload.payload.pages).result =
      some (X.chosenFields k) ∧
    J6R22Active.boxTransport X.field.result.exactMod
      (uvRead X.field.result.hp X.field.result.words ell (X.chosenFields k).probe)=
        prescribedNode (rootPreset G ell) (J6SourcePrecision.printed m base) ell X.sample := by
  have head := stable_exterior_header X
  have fresh : ∀ row∈A.bank.headers,row.id≠X.issue.result := by
    intro row row_at
    have no := A.ready.2.2 (X.seed pad) List.mem_cons_self row row_at
    exact fun e=>no (e.trans head.1.symm)
  have h := true_exterior_seed_lookup X pad A.bank A.ready.1 fresh k
  exact ⟨(actual_prefix_bytes (ell:=ell) G X.sample).1,(actual_prefix_bytes (ell:=ell) G X.sample).2,
    h.2.2.2.1,h.2.2.2.2.2⟩

#print axioms paid_atlas_child
#print axioms receiptFromAtlas
#print axioms installed_atlas_has_same_raw_probe
end J6R34OfficialGateway
