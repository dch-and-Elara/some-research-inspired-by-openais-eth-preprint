import J6R54ExteriorOwnerMount

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

theorem installed_root_is_live (B : Bnk) (sync : B.synced)
    (fresh : ∀ row∈B.headers,row.id≠X.issue.result) :
    ((X.seed pad).install B).result.2=true ∧
    IsLive (X.seed pad) ((X.seed pad).install B).result.1 := by
  let j := X.seed pad
  have js : JobsReady B [j] := by
    refine ⟨sync,by simp,?_⟩
    intro k h row old
    obtain rfl := List.mem_singleton.mp h
    exact fun e=>fresh row old (e.trans (stable_exterior_header X).1)
  have wrote := (next_job_exact B j [] js).1
  change (j.install B).result.2=true ∧ IsLive j (j.install B).result.1
  rw [wrote]
  exact ⟨rfl,new_is_live j B⟩

def publishThenMount (paid : Meter (RootRoster (P:=P) gate pad rootName)) (B : Bnk)
    (sync : B.synced) (fresh : ∀ row∈B.headers,row.id≠X.issue.result)
    (K : KeyInputs X gate pad paid.result name) (inj : Function.Injective rootName) :
    Meter (ExteriorRoster X gate pad name × Bnk) :=
  let start := (X.seed pad).install B
  let out := mountFirstOwners X gate pad paid.result start.result.1
    (installed_root_is_live X pad B sync fresh).2 K inj
  ⟨(out.result,start.result.1),paid.steps+start.steps+out.steps+5⟩

theorem published_first_owner_reuses_one_real_atlas
    (paid : Meter (RootRoster (P:=P) gate pad rootName)) (B : Bnk)
    (sync : B.synced) (fresh : ∀ row∈B.headers,row.id≠X.issue.result)
    (K : KeyInputs X gate pad paid.result name) (inj : Function.Injective rootName)
    (injLocal : Function.Injective name) (u : U) :
    let start := (X.seed pad).install B
    let out := publishThenMount X gate pad paid B sync fresh K inj
    (locate (name u) out.result.1.raw).result=some (exteriorData X gate pad u) ∧
    out.result.2=start.result.1 ∧ IsLive (X.seed pad) out.result.2 ∧
    out.steps=paid.steps+start.steps+K.headers.steps+
      (chosenFirstRaw X gate pad paid.result start.result.1 name K).steps+5 := by
  let start := (X.seed pad).install B
  have live := (installed_root_is_live X pad B sync fresh).2
  have data := actual_first_owner_is_mounted X gate pad paid.result start.result.1 live K inj injLocal u
  refine ⟨data.1,rfl,live,?_⟩
  change paid.steps+start.steps+(mountFirstOwners X gate pad paid.result start.result.1 live K inj).steps+5=_
  rw [data.2]
  exact congrArg (fun k=>k+5) (Nat.add_assoc (paid.steps+start.steps) K.headers.steps
    (chosenFirstRaw X gate pad paid.result start.result.1 name K).steps).symm

#print axioms installed_root_is_live
#print axioms published_first_owner_reuses_one_real_atlas
end
end J6R54ExteriorOwner
