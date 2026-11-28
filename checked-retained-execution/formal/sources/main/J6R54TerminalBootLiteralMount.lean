import J6R54ExteriorOwnerMount
import J6R54ExteriorOwnerLiteral

/-! The public typed first mount is an exact raw read of the original
live atlas. Neither this theorem nor mountFirstOwners installs it.
The certified key packet may have an arbitrary paid legal naming order. -/
namespace J6R54TerminalBoot
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R26DescriptorTree J6R35RootOrigins J6R36ChildFramedRoute
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R34RootAtlas J6R41StructuredAllPaths
open J6Mesh J6OrientedHost J6R24LegalLayout J6R10Repack J6R12Blueprint
open J6R12Repack J6ActiveRun J6ActiveSchedule J6R32StatefulArithmetic
open J6R32ChildResidentTransfer J6R27OriginalGate J6R33StatefulArithmeticPage
open J6R53OldOwner J6R53OldOwnerRoot J6R49SourceLayout J6R37StructuredRoot
open J6R52CacheSource J6R30ProducedGateRegistry J6R54ExteriorOwner
set_option quotPrecheck false
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 18000000
set_option maxRecDepth 4200
set_option Elab.async false
noncomputable section

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co d edgew tc tj key prec tw bw own next : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "U" => ((Ext).host.Row⊕(Ext).host.Col)
local notation "Bnk" => (PageBank f ell key prec tw bw (pageKeyWidth m+pad))

theorem literal_public_mount_reads_the_same_live_atlas
    {rootName : SourceVertex P→Word own}
    (root : RootRoster (P:=P) gate pad rootName)
    (B : Bnk) (live : IsLive (X.seed pad) B)
    (localKey : U→Word next) (K : KeyInputs X gate pad root localKey)
    (inj : Function.Injective rootName) :
    let read := chosenFirstRaw X gate pad root B localKey K
    let loaded := mountFirstOwners X gate pad root B live K inj
    read.result=some loaded.result.raw ∧ loaded.steps=K.headers.steps+read.steps := by
  let lhs : (Ext).host.Row→Word next := localKey ∘ Sum.inl
  let rhs : (Ext).host.Col→Word next := localKey ∘ Sum.inr
  have split : Sum.elim lhs rhs=localKey := by
    funext u
    cases u <;> rfl
  have dest : K.dest.result=(stageOwnerOrder X root.order).map (Sum.elim lhs rhs) :=
    K.destExact.trans (congrArg (List.map · (stageOwnerOrder X root.order)) split.symm)
  have rawExact := literal_exterior_raw_mount X gate pad rootName root inj B live
    K.headers.result K.headerExact lhs rhs K.dest dest
  have kernel : (chosenFirstRaw X gate pad root B localKey K).result=
      some (outputRosterRows X gate pad root localKey) := by
    simpa only [chosenFirstRaw,outputRosterRows,split] using rawExact
  let A := (mountFirstOwners X gate pad root B live K inj).result
  have sameOrder : A.order=stageOwnerOrder X root.order := rfl
  have hRows : A.raw=outputRosterRows X gate pad root localKey := by
    rw [A.exactRows,sameOrder]
    rfl
  refine ⟨?_,rfl⟩
  exact kernel.trans (congrArg some hRows.symm)

#print axioms literal_public_mount_reads_the_same_live_atlas
end
end J6R54TerminalBoot
