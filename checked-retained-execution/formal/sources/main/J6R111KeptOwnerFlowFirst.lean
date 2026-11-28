import J6R111KeptOwnerFlowEntry
import J6R54TerminalBootRetype
import J6R54ExteriorOwnerMount

/-! The literal first R66 slot borrows a complete, metered owner
roster from the one live exterior atlas. The actual boot installer
hands its resident result to that owner's continuation. -/
namespace J6R111KeptOwnerFlow
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6OrientedHost J6R34RootAtlas
open J6Mesh J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R34ChildPath J6R37StructuredRoot J6R41StructuredAllPaths J6R35RootOrigins J6R28GeneratedRootFrame
open J6R55TerminalOrigin J6R54TerminalBoot J6R54ExteriorOwner J6R53OldOwner J6R53OldOwnerRoot
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS J6R26DescriptorTree
open J6R51Online J6R52CacheWhole J6R64Active J6R68.RecursivePeak
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 25000000
set_option maxRecDepth 5500
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C rate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable (w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group))
variable (gate : Stamp key prec) (boot : ExactPrintedBoot X M gate)
variable {rw : ℕ} {name : SourceVertex P→Word rw} (root : RootRoster (P:=P) gate pad name)
variable (initial : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
variable (live : IsLive (X.seed pad) initial)
variable (named : KeyInputs X gate pad root (M.initial w).result.site.oldKey)
variable (inj : Function.Injective name)

def firstPaidOwnerRoster :
    Meter (RosterAt M (bootGates X) (Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group) (exteriorChild G ell X.centre X.sample X.group)) w) :=
  same_meter_first_roster X M gate boot w
    (mountFirstOwners X gate pad root initial live named inj)

theorem first_roster_is_the_actual_mounted_tape_including_isolates :
    let made := mountFirstOwners X gate pad root initial live named inj
    let carried := firstPaidOwnerRoster X M w gate boot root initial live named inj
    carried.result.order=made.result.order ∧ carried.result.raw=made.result.raw ∧
      (∀ u,u ∈ carried.result.order) ∧ carried.steps=made.steps :=
  ⟨rfl,rfl,(firstPaidOwnerRoster X M w gate boot root initial live named inj).result.complete,rfl⟩

variable {Out : Type}
variable (retire : PageJob f ell key prec tw bw (pageKeyWidth m+pad)→ℕ)
variable (labels : LabelWitness X (Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group) (exteriorChild G ell X.centre X.sample X.group)) w (M.initial w).result
  (firstPaidOwnerRoster X M w gate boot root initial live named inj).result)
variable (resume : CapturedEntry X (Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group) (exteriorChild G ell X.centre X.sample X.group)) w (M.initial w).result→Meter (Out×PageBank f ell key prec tw bw (pageKeyWidth m+pad)))
variable (bad : Meter Out)

/-- Expansion of the genuine `bootWithHeader` loop specialized to its
actual producer, with the mounted roster bound before publication. The
outer atlas is already live; there is no second exterior installation. -/
def firstR66OwnerScope : Meter (Out×PageBank f ell key prec tw bw (pageKeyWidth m+pad)) :=
  let source := M.initial w
  let roster := firstPaidOwnerRoster X M w gate boot root initial live named inj
  let Y := source.result
  let out := @withScopeHeader key prec tw bw (PagedEnvelope f ell prec (pageKeyWidth m+pad)) Out
    retire Y.birth.job (fun opened owned=>
      let resident := installResidentBank Y
      let got := resume ⟨resident.result,opened,owned,roster.result,labels⟩
      ⟨got.result,resident.steps+got.steps⟩) bad initial
  ⟨out.result,roster.steps+(source.steps+out.steps)⟩

/-- All terms in the bill are the operations just executed by this
scope. Failure is handled by `withScopeHeader`; on a legal job the
continuation receives its actual live directory and resident handle. -/
theorem first_R66_scope_continues_with_the_real_paid_roster_and_one_resident
    (legal : JobsReady initial [(M.initial w).result.birth.job]) :
    let source := M.initial w
    let roster := firstPaidOwnerRoster X M w gate boot root initial live named inj
    let Y := source.result
    let job := Y.birth.job
    let installed := installResidentBank Y
    let done := resume ⟨installed.result,afterOne initial job,rfl,roster.result,labels⟩
    firstR66OwnerScope X M w gate boot root initial live named inj retire labels resume bad=
      ⟨(done.result.1,initial),roster.steps+(source.steps+
        (publishFee initial job.entry job.offset job.built+(installed.steps+done.steps)+retire job+4))⟩ := by
  unfold firstR66OwnerScope
  dsimp only
  rw [the_actual_header_scope_enters_its_published_head _ _ _ _ _ legal]

#print axioms first_roster_is_the_actual_mounted_tape_including_isolates
#print axioms first_R66_scope_continues_with_the_real_paid_roster_and_one_resident
end
end J6R111KeptOwnerFlow

