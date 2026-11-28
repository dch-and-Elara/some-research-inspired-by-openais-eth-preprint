import J6R55TerminalBootJoinedCore

/-! The joined first-slot debit contains the actual physical writer
exactly once, then the read-only mount and the actual addon emission.
Issuance carries the copied result, not another physical-writer fee.
These are the local boot charges, not a billed whole DFS. -/
namespace J6R55TerminalBootJoined
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6R27OriginalGate J6OrientedHost
open J6Mesh J6R35RootOrigins J6R37StructuredRoot J6R34RootAtlas J6R31RootResidentTables
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R32RootGeneratedRegistryInputs
open J6R26DescriptorTree J6R34ChildPath J6R36ChildFramedRoute J6R50SourceProducer
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R22Active J6R24MeteredRecursion
open J6R9Recursive J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R49SourceLayout
open J6R53OldOwner J6R53OldOwnerRoot J6R54ExteriorOwner J6R41StructuredAllPaths J6R51Online J6R55TerminalOrigin J6R54TerminalBoot J6R55BootBodies
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 33000000
set_option maxRecDepth 6100
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw own rate : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
variable {s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable {rootName : SourceVertex P→Word own}
variable (root : RootRoster (P:=P) gate pad rootName)



variable (M : (OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate))

variable (A : FirstBodyProgram X gate pad T)

variable (D : OwnerWordsAtBodies X gate pad root A)
variable (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
variable (live : IsLive (X.seed pad) B) (rootInj : Function.Injective rootName)

theorem joined_initial_body_and_mount_charged_once (w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group)) :
    let Y := (joinedSlots X gate pad root A D) w
    let writer := readFirstPhysical X gate pad A.lanes (A.seats w)
    let mounted := mountFirstOwners X gate pad root B live (D.keys w) rootInj
    let out := (withJoinedBoot X gate pad root M A D B live rootInj).initial w
    let add := J6R48GeneratedAddons.emit (readBootAddon Y.words mounted.result)
      (compileOccurrence Y.occurrence.result).native.physical.order
    out.steps=((A.old w).steps+writer.steps+4)+mounted.steps+Y.words.seats.steps+
      (projectOriginTape mounted.result.raw).steps+add.steps ∧
    out.result.birth.issuance.steps=(A.old w).result.issued.steps+
      ((A.old w).result.native.steps+4+(A.old w).result.physical.steps+(A.old w).result.words.steps+4) := by
  refine ⟨rfl,?_⟩
  exact (actual_boot_occurrence_charges_raw_writer_once X gate pad w
    (A.old w) A.lanes (A.seats w)).2.2.2.2

end
#print axioms joined_initial_body_and_mount_charged_once
end J6R55TerminalBootJoined
