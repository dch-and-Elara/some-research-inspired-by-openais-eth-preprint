import J6R54TerminalBootSeed
import J6R54ExteriorOwnerChart

/-! The actual completed root owner's raw Gate/Page projection and the
proved terminal source tag/word use the same physical code. -/
namespace J6R54TerminalBoot
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6R27OriginalGate J6OrientedHost
open J6Mesh J6R35RootOrigins J6R37StructuredRoot J6R34RootAtlas J6R31RootResidentTables
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R32RootGeneratedRegistryInputs
open J6R26DescriptorTree J6R34ChildPath J6R36ChildFramedRoute J6R50SourceProducer
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R22Active J6R24MeteredRecursion
open J6R9Recursive J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R49SourceLayout
open J6R53TerminalGate J6R41StructuredAllPaths
open J6R53OldOwner J6R53OldOwnerRoot J6R54ExteriorOwner
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 48000000
set_option maxRecDepth 6200
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad : ℕ} (gate : Stamp key prec)
local notation "r" => (exteriorChild G ell X.centre X.sample X.group)

theorem physical_first_owner_is_the_boot_source
    (u : (r).host.Row⊕(r).host.Col) :
    exteriorData X gate pad u=⟨initialOrigin X gate pad u,bootGates X u⟩ := by
  cases u with
  | inl o => rfl
  | inr k => rfl

end
#print axioms physical_first_owner_is_the_boot_source
end J6R54TerminalBoot
