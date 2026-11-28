import J6R55TerminalBootJoinedCore
import J6R54TerminalBootLiteralMounted

/-! The R54 terminal is at exactly the generated machine and the
mounted owners of the same actual slot names; neither an external
roster chart nor an unrelated root seed appears. A call to this
terminal path owns its own mount debit, not a credit on a DFS trace. -/
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

abbrev JoinedRekeys :=
  ∀ {c : Call (PhysicalHost f ell)} (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c) (w : (Plan sel).Slot c)
    (incoming : RosterAt (withJoinedBoot X gate pad root M A D B live rootInj) (bootGates X) p w) (u : (Plan sel).Slot (p.ticket w).child),
    ActualOwnerWords (withJoinedBoot X gate pad root M A D B live rootInj) (bootGates X) p w incoming u

variable (nextWords : (JoinedRekeys X gate pad root M A D B live rootInj))

def joinedInstalledOwnerInputs : InstalledOwnerInputs (rootName:=rootName) X (withJoinedBoot X gate pad root M A D B live rootInj) gate where
  source := root
  keys w := by
    change KeyInputs X gate pad root (D.name w)
    exact D.keys w
  distinct := rootInj
  steps := nextWords

def joinedTerminalProgram : PathRosterProgram (withJoinedBoot X gate pad root M A D B live rootInj) (bootGates X) :=
  roster_program_from_measured_first X (withJoinedBoot X gate pad root M A D B live rootInj) gate (actual_joined_boot_is_literal X gate pad root M A D B live rootInj)
    (measured_first_from_installed_atlas X (withJoinedBoot X gate pad root M A D B live rootInj) gate (joinedInstalledOwnerInputs X gate pad root M A D B live rootInj nextWords) B live)

theorem joined_terminal_initial_roster_debit (w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group)) :
    let exactMount := mountFirstOwners X gate pad root B live (D.keys w) rootInj
    let measured := runRosterAlong (withJoinedBoot X gate pad root M A D B live rootInj) (bootGates X) (joinedTerminalProgram X gate pad root M A D B live rootInj nextWords) .root w
    measured.result.raw=exactMount.result.raw ∧ measured.steps=exactMount.steps :=
  ⟨rfl,rfl⟩

end
#print axioms joinedInstalledOwnerInputs
#print axioms joinedTerminalProgram
#print axioms joined_terminal_initial_roster_debit
end J6R55TerminalBootJoined
