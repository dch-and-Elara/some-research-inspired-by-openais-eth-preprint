import J6R54ExteriorOwnerMountRaw

/-! The first exterior occurrence publishes the original full page
atlas once and derives its own complete raw resident owner table.
A subsequent layout may use any honest charged complete owner naming
tape. This binder neither guesses older Fintype ranks nor relies on
a phantom free roster carried along typed ports. -/
namespace J6R54ExteriorOwner
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R26DescriptorTree J6R35RootOrigins J6R36ChildFramedRoute
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R34RootAtlas J6R41StructuredAllPaths
open J6Mesh J6OrientedHost J6R24LegalLayout J6R10Repack J6R12Blueprint
open J6R12Repack J6ActiveRun J6ActiveSchedule J6R32StatefulArithmetic
open J6R32ChildResidentTransfer J6R27OriginalGate J6R33StatefulArithmeticPage
open J6R53OldOwner J6R53OldOwnerRoot J6R49SourceLayout J6R37StructuredRoot
open J6R52CacheSource J6R30ProducedGateRegistry
set_option quotPrecheck false
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 9400000
set_option maxRecDepth 3900
set_option maxSynthPendingDepth 12
set_option Elab.async false
noncomputable section

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co d edgew tc tj key prec tw bw own next : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "Pg" => (pageKeyWidth m+pad)
local notation "Src" => (SourceVertex P)
local notation "U" => ((Ext).host.Row⊕(Ext).host.Col)
local notation "Raw" => (RawRoster next (SuffixWordWidth m) key prec Pg)
local notation "Bnk" => (PageBank f ell key prec tw bw Pg)

variable {rootName : SourceVertex P→Word own} {name : ((exteriorChild G ell X.centre X.sample X.group).host.Row⊕(exteriorChild G ell X.centre X.sample X.group).host.Col)→Word next}
variable (root : RootRoster (P:=P) gate pad rootName)

def mountFirstOwners (B : Bnk) (live : IsLive (X.seed pad) B)
    (K : KeyInputs X gate pad root name) (inj : Function.Injective rootName) :
    Meter (ExteriorRoster X gate pad name) :=
  let emit := chosenFirstRaw X gate pad root B name K
  let order := stageOwnerOrder X root.order
  have mapLaw := local_exterior_raw_rows X gate pad root B live name K inj
  have success : emit.result.isSome := by
    change (chosenFirstRaw X gate pad root B name K).result.isSome
    rw [mapLaw]
    rfl
  let result := unwrapSuccess emit success
  have all := stage_owner_order_exact X root.order root.unique root.complete
  ⟨⟨order,all.1,all.2,result.result,congrArg Meter.result
    (unwrap_success_exact emit success (outputRosterRows X gate pad root name) mapLaw)⟩,
    K.headers.steps+result.steps⟩

theorem actual_first_owner_is_mounted (B : Bnk) (live : IsLive (X.seed pad) B)
    (K : KeyInputs X gate pad root name) (inj : Function.Injective rootName)
    (injLocal : Function.Injective name) (u : U) :
    let M := mountFirstOwners X gate pad root B live K inj
    (locate (name u) M.result.raw).result=some (exteriorData X gate pad u) ∧
    M.steps=K.headers.steps+(chosenFirstRaw X gate pad root B name K).steps :=
  ⟨complete_owner_hit _ injLocal u,rfl⟩

theorem exact_first_owner_at_written_port (B : Bnk) (live : IsLive (X.seed pad) B)
    (K : KeyInputs X gate pad root name) (inj : Function.Injective rootName)
    (injLocal : Function.Injective name) (gateWidth : gate.created.val=base)
    (u : U) (p : PortAt (J6R34ChildPath.point (Ext).host u)) :
    let M := mountFirstOwners X gate pad root B live K inj
    (locate (name u) M.result.raw).result.map OwnerData.origin=some (initialPayload X gate pad p.val).1 := by
  have read := (actual_first_owner_is_mounted X gate pad root B live K inj injLocal u).1
  have fromPort := mounted_owner_matches_first_payload X gate pad gateWidth u p
  exact (congrArg (Option.map OwnerData.origin) read).trans (congrArg some fromPort.symm)

#print axioms mountFirstOwners
#print axioms actual_first_owner_is_mounted
#print axioms exact_first_owner_at_written_port
end
end J6R54ExteriorOwner
