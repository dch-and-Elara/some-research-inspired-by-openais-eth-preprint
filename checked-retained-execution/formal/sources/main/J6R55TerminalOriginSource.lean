import J6R55TerminalOriginTape
import J6R54ExteriorOwnerMount

/-! Every original old Gate and every actual exterior Page has its
tag on the paid projection tape of the genuine first mount, whether
or not it owns any port. This theorem does not introduce or install
a second seed. -/
namespace J6R55TerminalOrigin
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


theorem actual_first_mount_delivers_every_origin
    {rootName : SourceVertex P→Word own}
    (root : RootRoster (P:=P) gate pad rootName)
    (B : Bnk) (live : IsLive (X.seed pad) B)
    (localKey : U→Word next) (K : KeyInputs X gate pad root localKey)
    (oldInj : Function.Injective rootName) (newInj : Function.Injective localKey) (u : U) :
    let loaded := mountFirstOwners X gate pad root B live K oldInj
    let projected := projectOriginTape loaded.result.raw
    (locate (localKey u) projected.result).result=some (localKey u,initialOrigin X gate pad u) ∧
      projected.steps=3+(loaded.result.raw.map (fun row=>2*(3*next+1)+
        originFee key prec (pageKeyWidth m+pad) row.payload.origin.pageKey.isSome+6)).sum := by
  let loaded := mountFirstOwners X gate pad root B live K oldInj
  have law := exterior_data_origin X gate pad
  exact ⟨locate_hit _ _ _ (project_roster_exact loaded.result law u)
    (fun row h eq=>project_roster_unique loaded.result law newInj u row h eq),
    congrArg Meter.steps (project_origin_tape_exact loaded.result.raw)⟩

#print axioms actual_first_mount_delivers_every_origin
end
end J6R55TerminalOrigin
