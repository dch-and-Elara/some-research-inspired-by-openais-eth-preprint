import J6R111KeptOwnerFlowEntry
import J6R55TerminalOriginExterior
import J6R54TerminalBootBinding

/-! First-slot R55 producer, retaining the exact complete owner table it
already pays to mount. Both consumers borrow the one result. -/
namespace J6R111KeptOwnerFlow
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6OrientedHost J6R34RootAtlas
open J6Mesh J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R34ChildPath J6R37StructuredRoot J6R41StructuredAllPaths J6R35RootOrigins J6R28GeneratedRootFrame
open J6R55TerminalOrigin J6R54TerminalBoot J6R54ExteriorOwner J6R53OldOwner J6R53OldOwnerRoot
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS J6R26DescriptorTree
open J6R50SourceProducer J6R51Online J6R52CacheWhole J6R64Active J6R68.RecursivePeak
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 30000000
set_option maxRecDepth 5500
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group))
variable (gate : Stamp key prec)
variable {own : ℕ} {name : SourceVertex P→Word own} (root : RootRoster (P:=P) gate pad name)
variable (D : LiteralFirstSlot X gate pad root w T)
variable (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
variable (live : IsLive (X.seed pad) B) (rootInj : Function.Injective name)

structure FirstSlotWithOwners where
  site : StoredSite T ((Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group) (exteriorChild G ell X.centre X.sample X.group)).ticket w) key prec tw bw (pageKeyWidth m+pad)
  owners : CompleteRoster site.site.oldKey (parentData site (bootGates X))
  injective : Function.Injective site.site.oldKey

/-- The operation calls the real R54 mount once, just as literal R55
does. R55's raw port emitter and the continuation see the same mounted
data, not separately reproduced lists of the same mathematical owners. -/
def assembleFirstExteriorKeepingOwners : Meter (FirstSlotWithOwners (pad:=pad) (T:=T) X w) :=
  let mounted := mountFirstOwners X gate pad root B live D.keys rootInj
  let source := assembleOriginSite (exterior_data_origin X gate pad) D.injective D.occurrence mounted D.words
  let R := mounted.result
  let carried : CompleteRoster source.result.site.oldKey (parentData source.result (bootGates X)) :=
    ⟨R.order,R.unique,R.complete,R.raw,by
      rw [R.exactRows]
      apply List.map_congr_left
      intro u _
      exact congrArg (fun v=>RefRow.mk (D.name u) v) (physical_first_owner_is_the_boot_source X gate u)⟩
  ⟨⟨source.result,carried,D.injective⟩,source.steps⟩

theorem retaining_first_owners_projects_to_the_whole_literal_R55_meter :
    let A := assembleFirstExteriorKeepingOwners X w gate root D B live rootInj
    (⟨A.result.site,A.steps⟩ : Meter (StoredSite T ((Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group) (exteriorChild G ell X.centre X.sample X.group)).ticket w) key prec tw bw (pageKeyWidth m+pad)))=
      assembleFirstExterior X gate pad root w D B live rootInj := rfl

theorem retained_first_source_keeps_the_identical_full_mounted_raw_spool :
    let A := assembleFirstExteriorKeepingOwners X w gate root D B live rootInj
    let R := mountFirstOwners X gate pad root B live D.keys rootInj
    A.result.owners.raw=R.result.raw ∧ A.result.owners.order=R.result.order ∧
      (∀ u,u ∈ A.result.owners.order) :=
  ⟨rfl,rfl,(assembleFirstExteriorKeepingOwners X w gate root D B live rootInj).result.owners.complete⟩

variable {Out : Type}
variable (retire : PageJob f ell key prec tw bw (pageKeyWidth m+pad)→ℕ)
variable (labels : LabelWitness X
  (Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group)
    (exteriorChild G ell X.centre X.sample X.group))
  w (assembleFirstExteriorKeepingOwners X w gate root D B live rootInj).result.site
    (assembleFirstExteriorKeepingOwners X w gate root D B live rootInj).result.owners)
variable (resume : CapturedEntry X
  (Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group)
    (exteriorChild G ell X.centre X.sample X.group))
  w (assembleFirstExteriorKeepingOwners X w gate root D B live rootInj).result.site →
    Meter (Out×PageBank f ell key prec tw bw (pageKeyWidth m+pad)))
variable (bad : Meter Out)

/-- Same physical R66 boot, specialized to use the measured R55 pair.
There is no additional roster fee, because it is part of R55's honest
initial debit, and the inner resident bank is installed only once. -/
def bootWithRetainedFirstExterior :
    Meter (Out×PageBank f ell key prec tw bw (pageKeyWidth m+pad)) :=
  let ready := assembleFirstExteriorKeepingOwners X w gate root D B live rootInj
  let start := ready.result.site
  let go := withScopeHeader retire start.birth.job (fun fresh owns=>
    let installed := installResidentBank start
    let out := resume ⟨installed.result,fresh,owns,ready.result.owners,labels⟩
    ⟨out.result,installed.steps+out.steps⟩) bad B
  ⟨go.result,ready.steps+go.steps⟩

theorem first_literal_owner_handoff_publishes_installs_and_reads_once
    (legal : JobsReady B [(assembleFirstExteriorKeepingOwners X w gate root D B live rootInj).result.site.birth.job]) :
    let ready := assembleFirstExteriorKeepingOwners X w gate root D B live rootInj
    let start := ready.result.site
    let j := start.birth.job
    let installed := installResidentBank start
    let terminal := resume ⟨installed.result,afterOne B j,rfl,ready.result.owners,labels⟩
    bootWithRetainedFirstExterior X w gate root D B live rootInj retire labels resume bad=
      ⟨(terminal.result.1,B),(assembleFirstExterior X gate pad root w D B live rootInj).steps+
        (publishFee B j.entry j.offset j.built+(installed.steps+terminal.steps)+retire j+4)⟩ := by
  unfold bootWithRetainedFirstExterior
  dsimp only
  rw [the_actual_header_scope_enters_its_published_head _ _ _ _ _ legal]
  rfl

#print axioms retaining_first_owners_projects_to_the_whole_literal_R55_meter
#print axioms retained_first_source_keeps_the_identical_full_mounted_raw_spool
#print axioms first_literal_owner_handoff_publishes_installs_and_reads_once
end
end J6R111KeptOwnerFlow

