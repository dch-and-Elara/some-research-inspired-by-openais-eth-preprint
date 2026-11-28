import J6R54ExteriorOwnerRoles
import J6R53OldOwnerRootFresh

/-! Specialize the live exterior bootstrap to the actual guarded
fresh-CNF roster producer. The typed source file is exactly the one
used by the exterior job. We charge the literal roster/role inputs and
new owner key tape explicitly; nothing is filled by an unpriced choice
of the frozen rank or layout. -/
namespace J6R54ExteriorOwner
open scoped Polynomial Classical
open Polynomial Std.Sat AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R26DescriptorTree J6R35RootOrigins J6R36ChildFramedRoute
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R34RootAtlas J6R41StructuredAllPaths
open J6Mesh J6OrientedHost J6R24LegalLayout J6R10Repack J6R12Blueprint
open J6R12Repack J6ActiveRun J6ActiveSchedule J6R32StatefulArithmetic
open J6R32ChildResidentTransfer J6R27OriginalGate J6R33StatefulArithmeticPage
open J6R53OldOwner J6R53OldOwnerRoot J6R49SourceLayout J6R37StructuredRoot
open J6R30GeneratedRootLayout J6R51Ingress J7R9Compiler J7R9Subdivision J7R10Plant
open J6R30ProducedGateRegistry
set_option quotPrecheck false
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 41000000
set_option maxRecDepth 4300
set_option maxSynthPendingDepth 12
set_option Elab.async false
noncomputable section

section Fresh
variable {V : Type} [DecidableEq V] [Fintype V]
variable (F : CNF V) (vars : DeclaredOrder V) (code : V→List Bool)
variable {r c d e key prec own pad : ℕ}
local notation "HF" => (guardedInOrder F vars.roster)
local notation "S" => (guardRoster vars)
local notation "PlantF" => (freshPlant (guardedInOrder F vars.roster) (guardRoster vars))
local notation "Mass" => (nWires (guardedInOrder F vars.roster))
local notation "Src" => (SourceVertex (freshPlant (guardedInOrder F vars.roster) (guardRoster vars)))
variable (gate : Stamp key prec)
structure FreshRosterInputs (gate : Stamp key prec) (pad : ℕ) where
  literal : Meter (LiteralPortFile PlantF r c e)
  axis : List Bool
  clock : axis.length=(oddAxis Mass).val
  inj : Function.Injective code
  hh : ℕ
  jj : ℕ
  hPos : 0<hh
  dPos : 0<d
  jPos : 0<jj
  fitH : (HF).length≤2^hh
  fitD : ∀ row∈HF,row.length≤2^d
  fitJ : ∀ v,(occurrences HF v).length-3≤2^jj
  rank : ℕ
  rankFit : (oldRoster HF S).length≤2^rank
  rootName : Src→Word own
  rootInj : Function.Injective rootName
  order : List Src
  unique : order.Nodup
  all : ∀ v,v∈order
  plans : Meter (List (OwnerPlan own rank (SuffixKeyWidth Mass) key prec (pageKeyWidth Mass+pad)))
  plansExact : plans.result=order.map (rootPlanWord PlantF rootName (gateTag (P:=PlantF) gate pad) (freshHeadChoice HF S rank))
  roles : Meter (List (Word own × BootRole))
  rolesExact : roles.result=order.map (fun v=>(rootName v,trueRootRole v))

variable (D : FreshRosterInputs (r:=r) (c:=c) (d:=d) (e:=e) (own:=own) F vars code gate pad)

def buildCheckedFreshRoot : Meter (RootRoster (P:=PlantF) gate pad D.rootName) :=
  mountFreshRootOwnerRoster (h:=D.hh) (d:=d) (j:=D.jj)
    F vars code D.literal D.axis D.clock D.inj D.hPos D.dPos D.jPos D.fitH D.fitD D.fitJ
    D.rank D.rankFit D.rootName (gateTag (P:=PlantF) gate pad) D.order D.unique D.all D.plans D.plansExact

theorem checked_fresh_root_order :
    (buildCheckedFreshRoot F vars code gate D).result.order=D.order := rfl

end Fresh
#print axioms buildCheckedFreshRoot
#print axioms checked_fresh_root_order
end
end J6R54ExteriorOwner
