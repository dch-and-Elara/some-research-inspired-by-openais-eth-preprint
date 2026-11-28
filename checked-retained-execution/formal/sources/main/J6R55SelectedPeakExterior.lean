import J6R55SelectedPeakSpace
import J6R54ExteriorOwnerMount

/-! Count the actual old-owner and live-atlas snapshots of the
real read-only exterior mount. The old roster and page list are
not inferred from incident edges. Isolated retained factors and
unincident Page owners are deliberately included. -/
namespace J6R55SelectedPeak
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
set_option maxRecDepth 3900
set_option maxHeartbeats 23500000
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
local notation "Bnk" => (PageBank f ell key prec tw bw Pg)

variable {rootName : SourceVertex P→Word own}
variable {name : ((exteriorChild G ell X.centre X.sample X.group).host.Row⊕(exteriorChild G ell X.centre X.sample X.group).host.Col)→Word next}
variable (rootRows : RootRoster (P:=P) gate pad rootName)

def exteriorOldPayloads : List (OwnerData (SuffixWordWidth m) key prec (pageKeyWidth m+pad)) :=
  (stageOldOrder X rootRows.order).map (fun (u : (exteriorChild G ell X.centre X.sample X.group).host.Row)=>exteriorData X gate pad (.inl u))

def exteriorReadPages : List (Word Pg) :=
  (stagePageOrder X).map (bootPageKey X pad)

theorem real_exterior_owner_mount_yields_named_snapshots_and_output
    (B : Bnk) (live : IsLive (X.seed pad) B)
    (K : KeyInputs X gate pad rootRows name) (inj : Function.Injective rootName) :
    let paid := mountFirstOwners X gate pad rootRows B live K inj
    let sel := (selectOwnerKeys X.address.group K.headers.result).result
    let old := exteriorOldPayloads X gate pad rootRows
    let pages := exteriorReadPages X pad
    let activation := (X.seed pad).immutable.payload.stamp
    (indexedOwnerTape paid.result.raw).length=
      (ownerTape old).length+pages.length*freshPayloadWidth key prec Pg+K.dest.result.length*next ∧
    ∀ i j,ownerMountPrefixBits sel old activation pages K.dest.result paid.result.raw i j≤
      ownerMountLocalReserve sel old pages K.dest.result := by
  let paid := mountFirstOwners X gate pad rootRows B live K inj
  let old := exteriorOldPayloads X gate pad rootRows
  let pages := exteriorReadPages X pad
  let activation := (X.seed pad).immutable.payload.stamp
  let literalOut := outputRosterRows X gate pad rootRows name
  have copied : (gatherOwners rootRows.raw (selectOwnerKeys X.address.group K.headers.result).result).result=some old :=
    read_actual_old_gate_words X gate pad rootName rootRows K.headers.result K.headerExact inj
  have read : (readMountedOwners B (X.seed pad).identifier).result=some (activation,pages) :=
    (read_same_live_exterior_page_words X pad B live).1
  have out : (mountWords B (X.seed pad).identifier X.address.group K.headers.result rootRows.raw K.dest).result=
      some literalOut := local_exterior_raw_rows X gate pad rootRows B live name K inj
  have exactRaw : paid.result.raw=literalOut := paid.result.exactRows
  dsimp only
  change (indexedOwnerTape paid.result.raw).length=_ ∧ ∀ i j,ownerMountPrefixBits _ _ _ _ _ paid.result.raw i j≤_
  rw [exactRaw]
  exact actual_owner_mount_observations_use_the_same_reserve B (X.seed pad).identifier X.address.group
    K.headers.result rootRows.raw K.dest old activation pages literalOut copied read out

theorem actual_exterior_write_needs_only_its_completed_reads
    (B : Bnk) (live : IsLive (X.seed pad) B)
    (K : KeyInputs X gate pad rootRows name) (inj : Function.Injective rootName) :
    let sel := selectOwnerKeys X.address.group K.headers.result
    let debit := sel.steps+(gatherOwners rootRows.raw sel.result).steps+
      (readMountedOwners B (X.seed pad).identifier).steps
    let activation := (X.seed pad).immutable.payload.stamp
    chosenFirstRaw X gate pad rootRows B name K=
      resumeOwnerMountAfterReads debit ⟨activation,exteriorReadPages X pad,exteriorOldPayloads X gate pad rootRows,K.dest⟩ := by
  have copied := read_actual_old_gate_words X gate pad rootName rootRows K.headers.result K.headerExact inj
  have read := (read_same_live_exterior_page_words X pad B live).1
  exact original_owner_mount_uses_exact_bank_free_write_phase B (X.seed pad).identifier X.address.group
    K.headers.result rootRows.raw K.dest (X.seed pad).immutable.payload.stamp
    (exteriorReadPages X pad) (exteriorOldPayloads X gate pad rootRows) copied read

#print axioms real_exterior_owner_mount_yields_named_snapshots_and_output
#print axioms actual_exterior_write_needs_only_its_completed_reads
end
end J6R55SelectedPeak
