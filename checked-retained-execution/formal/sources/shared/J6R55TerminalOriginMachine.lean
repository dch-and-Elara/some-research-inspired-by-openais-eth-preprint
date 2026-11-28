import J6R55TerminalOriginExterior
import J6R51OnlineCore

/-! Keep the downstream driver but generate its actual first-slot
loader. No relation to the unused old loader is asserted. The
resulting machine is the one consumed by R51 sourceState/runRoot. -/
namespace J6R55TerminalOrigin
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6R27OriginalGate J6OrientedHost
open J6Mesh J6R35RootOrigins J6R37StructuredRoot J6R34RootAtlas J6R31RootResidentTables
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R32RootGeneratedRegistryInputs
open J6R26DescriptorTree J6R34ChildPath J6R36ChildFramedRoute J6R50SourceProducer
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R22Active J6R24MeteredRecursion
open J6R9Recursive J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R49SourceLayout
open J6R53OldOwner J6R53OldOwnerRoot J6R54ExteriorOwner J6R41StructuredAllPaths J6R51Online
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
variable (slots : ∀ w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group), LiteralFirstSlot X gate pad root w T)
variable (B : (PageBank f ell key prec tw bw (pageKeyWidth m+pad))) (live : IsLive (X.seed pad) B) (rootInj : Function.Injective rootName)

def withGeneratedOrigins : (OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate) :=
  { M with initial := fun w=>assembleFirstExterior X gate pad root w (slots w) B live rootInj }

theorem same_generated_machine_has_literal_origins (w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group)) :
    ((withGeneratedOrigins X gate pad root M slots B live rootInj).initial w).result.origins=
      initialOrigin X gate pad := rfl

theorem same_generated_machine_uses_measured_occurrence (w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group)) :
    (sourceState (withGeneratedOrigins X gate pad root M slots B live rootInj) .root w).input=
      (slots w).occurrence.result := rfl

theorem same_generated_machine_pays_the_actual_initial (w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group)) :
    (withGeneratedOrigins X gate pad root M slots B live rootInj).initial w=
      assembleFirstExterior X gate pad root w (slots w) B live rootInj := rfl

end
#print axioms withGeneratedOrigins
#print axioms same_generated_machine_has_literal_origins
#print axioms same_generated_machine_uses_measured_occurrence
#print axioms same_generated_machine_pays_the_actual_initial
end J6R55TerminalOrigin
