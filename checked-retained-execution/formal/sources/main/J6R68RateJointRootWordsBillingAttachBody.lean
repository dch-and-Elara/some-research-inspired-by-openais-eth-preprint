import J6R68RateJointRootWordsOnlineBody
import J6R55BootBodiesMachine

/-! Concrete R55 instance of the first-ingress contract. Unlike the
general receipt it fixes the remaining charge to the same observed
owner mount, seat table, origin projection and addon emission. -/
namespace J6R68RateJoint.RootWords
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6Mesh J6OrientedHost J6R24LegalLayout J6R31RootResidentTables
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R35RootOrigins
open J6R26DescriptorTree J6R33StatefulArithmeticPage J6R34RootAtlas J6R32RootGeneratedRegistryInputs
open J6R55BootBodies J6R30ProducedGateRegistry
open J6R24MeteredRecursion J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun
open J6R32StatefulArithmetic J6R48RawRoute
open J6R50SourceProducer

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 2600
set_option maxHeartbeats 4200000
set_option maxSynthPendingDepth 12
set_option Elab.async false
noncomputable section
attribute [local irreducible] J6R12Blueprint.printedParams

variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw own rate : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
variable {s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
local notation "Pg" => (pageKeyWidth m+pad)
local notation "Slot" => ((Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group))
variable (A : FirstBodyProgram X gate pad T)
variable (make : ∀ w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group),
  Meter (FirstSlotBook (r:=exteriorChild G ell X.centre X.sample X.group) (sel:=sel) T key prec tw bw (pageKeyWidth m+pad) w))
variable (uses : ∀ w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group),A.old w = loadSelectedFirst (T:=T) (w:=w) (make w) X.issue.result)

include uses in
theorem real_joined_body_is_replacement (w : Slot) :
    bodyAtActualSlot X gate pad A w=
      replaceSelectedFirst (T:=T) (w:=w) (make w) X.issue.result (readFirstPhysical X gate pad A.lanes (A.seats w)) := by
  unfold bodyAtActualSlot bootOccurrence replaceSelectedFirst
  rw [uses w]

#print axioms real_joined_body_is_replacement
end
end J6R68RateJoint.RootWords
