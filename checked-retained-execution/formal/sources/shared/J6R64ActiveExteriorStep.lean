import J6R64ActiveMachine
import J6R64ActiveExterior
import J6R52CacheWholeRun

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000
set_option maxRecDepth 3600
set_option maxSynthPendingDepth 12
set_option Elab.async false

/-! Actual active call at the exterior entrance, with the literal
marked incoming root header and original paid first-child callbacks.
This scope does not claim to replace any deeper active preparer. -/
namespace J6R64Active
open scoped Polynomial
open Polynomial AOracleMachineTime A1R12 J6R22Active
open J6R63Active J6R62ActivePrep
open J6R51Online J6R52CacheWhole J6R48RawRoute
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R50SourceProducer J6R26DescriptorTree J6R24MeteredRecursion J6R49DFS
open J6ActiveRun J6R9Recursive J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R34RootAtlas J6R32RootGeneratedRegistryInputs J6R21Ancestor
open J6Mesh J6OrientedHost J6R24LegalLayout J6R31RootResidentTables J6R26StablePreparedRoot

noncomputable section
variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {plant : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) plant
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell qr ro co e edgew tc tj key prec tw bw page s C q cw : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable (X : StableExterior G ell qr ro co e edgew tc tj key prec tw bw)
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "Here" => (Path.root : Path sel
  (exteriorChild G ell X.centre X.sample X.group) (exteriorChild G ell X.centre X.sample X.group))
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (@Plan f ell s sel)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)
local notation "Machine" => (OnlineMachine T key prec tw bw page q)

def exteriorActive (M : Machine) (a : (S).cutoff<(Ext).edges)
    (fit : InputFits sel (readyAtPath T Here a) q)
    (B : L) (own : OwnsHeader X.header.result B)
    (layout : Meter (AtLayout sel (readyAtPath T Here a) cw)) :
    Meter (ActiveMachine sel (readyAtPath T Here a) T.bank q) :=
  let taper := actual_path_taper T Here a
  sharedMachine M.modeWidth fit taper.1 taper.2
    (readExterior X B own) layout (M.activeRoot a)

theorem exterior_active_debits_its_own_input (M : Machine) (a : (S).cutoff<(Ext).edges)
    (fit : InputFits sel (readyAtPath T Here a) q) (B : L) (own : OwnsHeader X.header.result B)
    (layout : Meter (AtLayout sel (readyAtPath T Here a) cw)) :
    (exteriorActive X M a fit B own layout).steps=
      (M.activeRoot a).steps+
      (callReadFee prec edgew 1 (externalAddrWidth tc tj 0)+5)+layout.steps+(2*cw+4*q+5)+4 := by
  let taper := actual_path_taper T Here a
  change (sharedMachine M.modeWidth fit taper.1 taper.2
    (readExterior X B own) layout (M.activeRoot a)).steps=_
  rw [(shared_setup_has_one_header_and_one_layout M.modeWidth fit taper.1 taper.2
    (readExterior X B own) layout (M.activeRoot a)).1,(paid_actual_exterior_entry X B own).2.2]

def exteriorActiveWithRealChildren (M : Machine) (retire : J→ℕ)
    (a : (S).cutoff<(Ext).edges) (fit : InputFits sel (readyAtPath T Here a) q)
    (B : L) (own : OwnsHeader X.header.result B)
    (layout : Meter (AtLayout sel (readyAtPath T Here a) cw)) :
    Meter (Block (T.frame (Here).reached) ell×L) :=
  let d := readyAtPath T Here a
  let A := exteriorActive X M a fit B own layout
  let out := A.result.eval M.modeWidth (reachable_positive T (Here).reached) T.vPositive X.hf
    (fun t z β g=>
      let w := addressed (sel:=sel) d t z β g
      project (bootBankDemand (M.initial w) retire (runCachedAfter M retire Ext Here w)
        (zeroM (T.bank (registerPrecision S Ext t) (register_positive d t)).hp) B))
  ⟨(out.result,B),A.steps+out.steps⟩

theorem mounted_exterior_keeps_first_real_children (M : Machine) (retire : J→ℕ)
    (a : (S).cutoff<(Ext).edges) (fit : InputFits sel (readyAtPath T Here a) q)
    (B : L) (own : OwnsHeader X.header.result B)
    (layout : Meter (AtLayout sel (readyAtPath T Here a) cw)) :
    (exteriorActiveWithRealChildren X M retire a fit B own layout).result=
      (runCachedRoot M retire B).result := by
  let d := readyAtPath T Here a
  let A := exteriorActive X M a fit B own layout
  let hp := reachable_positive T (Here).reached
  let read : ActiveChild (sel:=sel) (d:=d) T.bank := fun t z β g=>
    let w := addressed (sel:=sel) d t z β g
    project (bootBankDemand (M.initial w) retire (runCachedAfter M retire Ext Here w)
      (zeroM (T.bank (registerPrecision S Ext t) (register_positive d t)).hp) B)
  let taper := actual_path_taper T Here a
  have exactWord := shared_active_value M.modeWidth fit taper.1 taper.2 (readExterior X B own)
    layout (M.activeRoot a) hp T.vPositive X.hf read
  rw [runCachedRoot,dif_neg (Nat.not_le.mpr a)]
  exact congrArg (fun word : Block (T.frame (Here).reached) ell=>(word,B)) exactWord

#print axioms exterior_active_debits_its_own_input
#print axioms mounted_exterior_keeps_first_real_children
end
end J6R64Active

