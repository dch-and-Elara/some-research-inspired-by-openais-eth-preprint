import J6R54ExteriorOwnerKeyContext
import J6R54ExteriorOwnerLift

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

variable {rootName : SourceVertex P→Word own}
variable (root : RootRoster (P:=P) gate pad rootName)

include root in
def outputRosterRows (localKey : U→Word next) : Raw :=
  (stageOwnerOrder X root.order).map (fun u : U =>
    (⟨localKey u,exteriorData X gate pad u⟩ : RefRow next (OwnerData (SuffixWordWidth m) key prec Pg)))

def chosenFirstRaw (B : Bnk) (localKey : U→Word next)
    (K : KeyInputs X gate pad root localKey) : Meter (Option Raw) :=
  @mountWords f ell key prec tw bw Pg own (SuffixWordWidth m) next
    B (X.seed pad).identifier X.address.group K.headers.result root.raw K.dest

theorem local_exterior_raw_rows (B : Bnk) (live : IsLive (X.seed pad) B)
    (localKey : U→Word next) (K : KeyInputs X gate pad root localKey)
    (inj : Function.Injective rootName) :
    (chosenFirstRaw X gate pad root B localKey K).result=some (outputRosterRows X gate pad root localKey) := by
  have old := read_actual_old_gate_words X gate pad rootName root K.headers.result K.headerExact inj
  have atlas := (read_same_live_exterior_page_words X pad B live).1
  exact checked_mount_words_as_given_data B (X.seed pad).identifier X.address.group
    K.headers.result root.raw K.dest (X.seed pad).immutable.payload.stamp (bootPageKey X pad)
    localKey (exteriorData X gate pad) (stageOldOrder X root.order) (stagePageOrder X)
    (fun _=>rfl) old atlas K.destExact

#print axioms chosenFirstRaw
#print axioms outputRosterRows
#print axioms local_exterior_raw_rows
end
end J6R54ExteriorOwner
