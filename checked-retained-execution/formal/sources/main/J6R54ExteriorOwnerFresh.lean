import J6R54ExteriorOwnerPublish
import J6R54ExteriorOwnerFreshInputs

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

section GeneralKeys
variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co d edgew tc tj key prec tw bw own next : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
variable {rootName : SourceVertex P→Word own}
variable (root : RootRoster (P:=P) gate pad rootName)
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "U" => ((Ext).host.Row⊕(Ext).host.Col)

def bindPaidOwnerKeys (name : U→Word next)
    (axis : List Bool) (clock : axis.length=(oddAxis m).val)
    (roles : Meter (List (Word own × BootRole)))
    (aligned : roles.result=root.order.map (fun u=>(rootName u,trueRootRole u)))
    (dest : Meter (List (Word next))) (destGood : dest.result=(stageOwnerOrder X root.order).map name) :
    KeyInputs X gate pad root name :=
  ⟨loadActualRootHeaders axis roles,
    (actual_root_group_headers_and_charge X axis clock rootName root.order roles aligned).1,dest,destGood⟩

theorem bound_owner_keys_reuses_actual_header
    (name : U→Word next)
    (axis : List Bool) (clock : axis.length=(oddAxis m).val)
    (roles : Meter (List (Word own × BootRole)))
    (aligned : roles.result=root.order.map (fun u=>(rootName u,trueRootRole u)))
    (dest : Meter (List (Word next))) (destGood : dest.result=(stageOwnerOrder X root.order).map name) :
    let packed := bindPaidOwnerKeys X gate pad root name axis clock roles aligned dest destGood
    packed.headers=loadActualRootHeaders axis roles ∧ packed.dest=dest := ⟨rfl,rfl⟩
end GeneralKeys

section Fresh
variable {V : Type} [DecidableEq V] [Fintype V]
variable (F : CNF V) (vars : DeclaredOrder V) (code : V→List Bool)
variable {f : ℤ[X]} {base native ell q r c d e edgew tc tj key prec tw bw own next pad : ℕ}
local notation "HF" => (guardedInOrder F vars.roster)
local notation "S" => (guardRoster vars)
local notation "PlantF" => (freshPlant (guardedInOrder F vars.roster) (guardRoster vars))
local notation "m" => (nWires (guardedInOrder F vars.roster))
local notation "n" => (nSubdiv (guardedInOrder F vars.roster))
local notation "Src" => (SourceVertex (freshPlant (guardedInOrder F vars.roster) (guardRoster vars)))

variable {G : RootShape f (nWires (guardedInOrder F vars.roster))
  (printedHalf (nWires (guardedInOrder F vars.roster))) base native
  (printedRankWidth (nWires (guardedInOrder F vars.roster)))
  (freshPlant (guardedInOrder F vars.roster) (guardRoster vars))
  (constantRootWord (nWires (guardedInOrder F vars.roster)))}
variable (X : StableExterior G ell q r c e edgew tc tj key prec tw bw)
variable (gate : Stamp key prec)
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "U" => ((Ext).host.Row⊕(Ext).host.Col)
local notation "Pg" => (pageKeyWidth m+pad)

variable (D : FreshRosterInputs (r:=r) (c:=c) (d:=d) (e:=e) (own:=own) F vars code gate pad)

def publishFreshExteriorOwners (name : U→Word next)
    (dest : Meter (List (Word next))) (destGood : dest.result=(stageOwnerOrder X D.order).map name)
    (_sameLiteral : D.literal.result=X.source)
    (initial : PageBank f ell key prec tw bw Pg) (sync : initial.synced)
    (fresh : ∀ row∈initial.headers,row.id≠X.issue.result) :
    Meter (ExteriorRoster X gate pad name × PageBank f ell key prec tw bw Pg) :=
  let paid := buildCheckedFreshRoot F vars code gate D
  let K := bindPaidOwnerKeys X gate pad paid.result name D.axis D.clock D.roles D.rolesExact dest destGood
  publishThenMount X gate pad paid initial sync fresh K D.rootInj

theorem raw_guarded_CNF_mounts_real_first_owners (name : U→Word next)
    (dest : Meter (List (Word next))) (destGood : dest.result=(stageOwnerOrder X D.order).map name)
    (_sameLiteral : D.literal.result=X.source)
    (initial : PageBank f ell key prec tw bw Pg) (sync : initial.synced)
    (fresh : ∀ row∈initial.headers,row.id≠X.issue.result) (nameInj : Function.Injective name)
    (u : U) :
    let paid := buildCheckedFreshRoot F vars code gate D
    let out := publishFreshExteriorOwners F vars code X gate D name dest destGood _sameLiteral initial sync fresh
    let bank := ((X.seed pad).install initial).result.1
    D.literal.result.raw=X.source.raw ∧
    (locate (name u) out.result.1.raw).result=some (exteriorData X gate pad u) ∧
    out.result.2=bank ∧ IsLive (X.seed pad) out.result.2 ∧
    out.steps=paid.steps+((X.seed pad).install initial).steps+(loadActualRootHeaders D.axis D.roles).steps+
      (mountWords bank (X.seed pad).identifier X.address.group (loadActualRootHeaders D.axis D.roles).result paid.result.raw dest).steps+5 := by
  let paid := buildCheckedFreshRoot F vars code gate D
  let K := bindPaidOwnerKeys X gate pad paid.result name D.axis D.clock D.roles D.rolesExact dest destGood
  exact ⟨congrArg LiteralPortFile.raw _sameLiteral,
    published_first_owner_reuses_one_real_atlas X gate pad paid initial sync fresh K D.rootInj nameInj u⟩

end Fresh
#print axioms bindPaidOwnerKeys
#print axioms bound_owner_keys_reuses_actual_header
#print axioms publishFreshExteriorOwners
#print axioms raw_guarded_CNF_mounts_real_first_owners
end
end J6R54ExteriorOwner
