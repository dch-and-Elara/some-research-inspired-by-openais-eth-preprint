import J6R82LeafTimeStop
import J6R58BootScopeReads
import J6R59PublicResidentStop

/-! Consume the live occurrence resident bank and already produced complete owner data. The only new table emitted at the stop is a copy of its real grouped header words. No page publication or roster rebuild occurs here. -/
namespace J6R94HeldOwnerProvider
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R21Ancestor J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R35RootOrigins J6R26DescriptorTree J6R34ChildPath
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS
open J6R50Leaf J6R50SourceProducer J6R51Leaf J6R51Online J6R49Leaf J6R48Leaf
open J6R57Public J6R58LeafScale J6R62Leaf J6R27OriginalGate J6R36ChildFramedRoute J6R54TerminalBoot
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R37StructuredRoot J6R41StructuredAllPaths
open J6R52Terminal J6R53TerminalGate J6R53OldOwner J6R49SourceLayout J6R66LeafTariff J6R65LeafRate
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 41000000
set_option maxRecDepth 5500
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C rate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable {c : Call (PhysicalHost f ell)}
variable (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c)
variable (w : (Plan sel).Slot c)
local notation "ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "Bank" => (PageBank f ell key prec tw bw (pageKeyWidth m+pad))
local notation "Cmd" => (ReadCmd key (pageKeyWidth m+pad))
local notation "deg" => (4*Nat.clog 2 s)
local notation "ch" => (p.ticket w).child

open J6R52CacheWhole J6R51ParentFrames J6R58BootScope

variable (Y : StoredSite T (p.ticket w) key prec tw bw (pageKeyWidth m+pad))
local notation "OriginalData" => (parentData Y (gateHistory T (bootGates X) p))

/-- Preserve the complete real order, including owners with no port. This
    is a paid raw word copy, not a proof-side enumeration of owner groups. -/
def readActualHeaders (headers : ParentOwnerHeaders Y.site) : Meter (ParentOwnerHeaders Y.site) :=
  let out := copyBootHeaders headers.raw
  ⟨⟨headers.order,headers.unique,headers.all,out.result,
    (congrArg Meter.result (copy_boot_headers_exact headers.raw)).trans headers.same⟩,out.steps⟩

theorem read_actual_headers_exact (headers : ParentOwnerHeaders Y.site) :
    readActualHeaders X p w Y headers=⟨headers,3+(3*Y.site.ownerWidth+26)*headers.raw.length⟩ := by
  cases headers with
  | mk order unique all raw exactRows =>
    unfold readActualHeaders
    simp only [copy_boot_headers_exact]

def paidHeldOwnerInput
    (resident : ResidentBank Y)
    (headers : ParentOwnerHeaders Y.site)
    (owners : CompleteRoster Y.site.oldKey OriginalData)
    (injective : Function.Injective Y.site.oldKey) :
    Meter (OwnerTerminalInput X p w Y) :=
  let F := mountResident Y resident
  let H := readActualHeaders X p w Y headers
  ⟨⟨F.result,H.result,owners,injective⟩,F.steps+H.steps+5⟩

theorem genuine_held_owner_input_keeps_paid_objects_and_exact_fee
    (resident : ResidentBank Y) (headers : ParentOwnerHeaders Y.site)
    (owners : CompleteRoster Y.site.oldKey OriginalData)
    (injective : Function.Injective Y.site.oldKey) :
    let A := paidHeldOwnerInput X p w Y resident headers owners injective
    A.result.saved=(mountResident Y resident).result ∧
    A.result.headers=headers ∧ A.result.roster=owners ∧
    A.steps=(mountResident Y resident).steps+(3+(3*Y.site.ownerWidth+26)*headers.raw.length)+5 := by
  unfold paidHeldOwnerInput
  rw [read_actual_headers_exact]
  exact ⟨rfl,rfl,rfl,rfl⟩

/-- A measured producer may independently reconstruct this exact roster.
    Keep its measured bill visible rather than treating it as resident. -/
def paidBuiltOwnerInput
    (resident : ResidentBank Y) (headers : ParentOwnerHeaders Y.site)
    (owners : Meter (CompleteRoster Y.site.oldKey OriginalData))
    (injective : Function.Injective Y.site.oldKey) :
    Meter (OwnerTerminalInput X p w Y) :=
  let built := paidHeldOwnerInput X p w Y resident headers owners.result injective
  ⟨built.result,owners.steps+built.steps⟩

theorem built_owner_inputs_charge_full_producer_once
    (resident : ResidentBank Y) (headers : ParentOwnerHeaders Y.site)
    (owners : Meter (CompleteRoster Y.site.oldKey OriginalData))
    (injective : Function.Injective Y.site.oldKey) :
    let A := paidBuiltOwnerInput X p w Y resident headers owners injective
    A.result.roster=owners.result ∧
    A.steps=owners.steps+(mountResident Y resident).steps+
      (3+(3*Y.site.ownerWidth+26)*headers.raw.length)+5 := by
  dsimp only [paidBuiltOwnerInput]
  have h := (genuine_held_owner_input_keeps_paid_objects_and_exact_fee X p w Y resident headers
    owners.result injective).2.2.2
  rw [h]
  exact ⟨rfl,by omega⟩

#print axioms read_actual_headers_exact
#print axioms genuine_held_owner_input_keeps_paid_objects_and_exact_fee
#print axioms built_owner_inputs_charge_full_producer_once
end
end J6R94HeldOwnerProvider