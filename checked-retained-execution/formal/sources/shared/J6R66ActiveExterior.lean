import J6R66ActiveRun
import J6R64ActiveExteriorStep

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 10500000
set_option maxRecDepth 3700
set_option maxSynthPendingDepth 12
set_option Elab.async false

/-! Specialize the unified runner to the actual marked R34 exterior
occurrence. It consumes a live bank after publication, not a second
call to that publisher. Initial p and M are not taken from later slots. -/
namespace J6R66Active
open scoped Polynomial
open Polynomial AOracleMachineTime J6R21Ancestor J6R63Active J6R64Active J6R62ActivePrep
open J6R51Online J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R24MeteredRecursion J6R49DFS J6ActiveRun J6R9Recursive J6R10Reachable
open J6R11Blueprint J6R12Blueprint J1PPrinted J6R34RootAtlas J6R32RootGeneratedRegistryInputs
open J6Mesh J6OrientedHost J6R24LegalLayout J6R31RootResidentTables J6R26StablePreparedRoot

noncomputable section
variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {plant : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) plant
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell qr ro co e edgew tc tj key prec tw bw page s C q cw : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable (X : StableExterior G ell qr ro co e edgew tc tj key prec tw bw)
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "Here" => (Path.root : Path sel
  (exteriorChild G ell X.centre X.sample X.group) (exteriorChild G ell X.centre X.sample X.group))
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)

abbrev ExteriorLayout :=
  (B : L) → OwnsHeader X.header.result B → (a : (S).cutoff<(Ext).edges) →
    Meter (AtLayout sel (readyAtPath T Here a) cw)

def physicalExteriorInputs (layout : ExteriorLayout (T:=T) (page:=page) (cw:=cw) X) :
    RootInputs T key prec tw bw page cw edgew :=
  ⟨X.header.result,readExterior X,layout⟩

theorem physical_root_setup_uses_exact_dual_entry
    (M : OnlineMachine T key prec tw bw page q) (F : RetainedAfter T key prec tw bw page q cw)
    (layout : ExteriorLayout (T:=T) (page:=page) (cw:=cw) X) (B : L)
    (own : OwnsHeader X.header.result B) (a : (S).cutoff<(Ext).edges) :
    rootSetup M F (physicalExteriorInputs X layout) B own a=
      exteriorActive X M a (F.fit Here a) B own (layout B own a) := rfl

theorem physical_root_setup_exact_fee
    (M : OnlineMachine T key prec tw bw page q) (F : RetainedAfter T key prec tw bw page q cw)
    (layout : ExteriorLayout (T:=T) (page:=page) (cw:=cw) X) (B : L)
    (own : OwnsHeader X.header.result B) (a : (S).cutoff<(Ext).edges) :
    (rootSetup M F (physicalExteriorInputs X layout) B own a).steps=
      (M.activeRoot a).steps+
      (callReadFee prec edgew 1 (externalAddrWidth tc tj 0)+5)+
        (layout B own a).steps+(2*cw+4*q+5)+4 := by
  rw [physical_root_setup_uses_exact_dual_entry]
  exact exterior_active_debits_its_own_input X M a (F.fit Here a) B own (layout B own a)

def runPhysicalExterior
    (M : OnlineMachine T key prec tw bw page q) (F : RetainedAfter T key prec tw bw page q cw)
    (layout : ExteriorLayout (T:=T) (page:=page) (cw:=cw) X)
    (retire : J→ℕ) (B : L) (own : OwnsHeader X.header.result B) :
    Meter (Block (T.frame (Here).reached) ell×L) :=
  J6R66Active.runRoot M F (physicalExteriorInputs X layout) retire B own

#print axioms physical_root_setup_uses_exact_dual_entry
#print axioms physical_root_setup_exact_fee
#print axioms runPhysicalExterior
end
end J6R66Active

