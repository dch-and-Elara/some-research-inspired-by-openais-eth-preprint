import J6R114SelectedOperandsHeld

/-! A selected least-mode-code runtime and its actual paid scanner
do not change the first or later issuers. Use only same-result facts
to prove ownership/readiness; the additional R102 fees are untouched. -/
namespace J6R114SelectedOperands
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R26DescriptorTree
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R34RootAtlas
open J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun
open J6R24MeteredRecursion J6R51Online J6R50SourceProducer J6R49SourceLayout
open J6R30ProducedGateRegistry J6R57ScopeFee
open J6R55BootBodies J6R55TerminalOrigin J6R48GeneratedAddons
open J6Mesh J6OrientedHost J6R24LegalLayout J6R31RootResidentTables
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R32RootGeneratedRegistryInputs
open J6R35RootOrigins J6R55TerminalBootJoined J6R53OldOwnerRoot J6R54TerminalBoot J6R54ExteriorOwner
open J6R16ModeCost J6R68RateJoint.RootWords J6R64.BootSeats J6R48RawRoute J6R48GeneratedAddons
open J6R55Public J6R51Online
open J6R53OldOwner J6R55TerminalOrigin J6R32ChildResidentTransfer J6R50SourceProducer

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxRecDepth 4900
set_option maxHeartbeats 8500000
set_option maxSynthPendingDepth 12

noncomputable section
variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X Y : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
variable {s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}

local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "Pg" => (pageKeyWidth m+pad)
local instance transportOperandDecision : DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) (Ext)) :=
  J6R24MeteredRecursion.sourceDecision sel Ext
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]


variable {own rate : ℕ} {rootName : SourceVertex P→Word own}
variable (root : RootRoster (P:=P) gate pad rootName)

def preparedAtOtherSource (e : X=Y)
    (T : Prepared cfg sel (exteriorChild G ell Y.centre Y.sample Y.group) Y.hf) :
    Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf := by
  cases e
  exact T

/-- Retype the already produced value; there is no layout run or
source lookup inside the equality transport. -/
def reindexHeldOperandData (e : X=Y)
    (T : Prepared cfg sel (exteriorChild G ell Y.centre Y.sample Y.group) Y.hf)
    (D : HeldR55Operands X gate pad root (preparedAtOtherSource X Y e T) rate) :
    HeldR55Operands Y gate pad root T rate := by
  cases e
  exact D

def reindexHeldOperandMeter (e : X=Y)
    (T : Prepared cfg sel (exteriorChild G ell Y.centre Y.sample Y.group) Y.hf)
    (D : Meter (HeldR55Operands X gate pad root (preparedAtOtherSource X Y e T) rate)) :
    Meter (HeldR55Operands Y gate pad root T rate) :=
  ⟨reindexHeldOperandData X Y gate pad root e T D.result,D.steps⟩

theorem reindexing_does_not_repeat_acquisition (e : X=Y)
    (T : Prepared cfg sel (exteriorChild G ell Y.centre Y.sample Y.group) Y.hf)
    (D : Meter (HeldR55Operands X gate pad root (preparedAtOtherSource X Y e T) rate)) :
    (reindexHeldOperandMeter X Y gate pad root e T D).steps=D.steps := rfl

#print axioms preparedAtOtherSource
#print axioms reindexHeldOperandData
#print axioms reindexing_does_not_repeat_acquisition
end
end J6R114SelectedOperands

