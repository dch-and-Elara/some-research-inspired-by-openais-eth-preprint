import J6R66BootPeakInit
import J6R64BootSeatsChart
import J6R64BootSeatsInstall
import J6R55TerminalOriginExterior
import J6R55SelectedPeakExterior
import J6R55SelectedPeakBootLink

/-! Actual first-slot R55 specialization: the receiving chart agrees by
the R64 paired-order theorem. Use the real R54 owner mount on the live
exterior bank and the real R55 occurrence/body writer and tag assembler.
The independently metered owner words and the original slot template
remain explicit. -/
namespace J6R66.BootPeak
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R26DescriptorTree J6R35RootOrigins J6R36ChildFramedRoute
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R34RootAtlas J6R41StructuredAllPaths
open J6Mesh J6OrientedHost J6R24LegalLayout J6R10Repack J6R12Blueprint
open J6R12Repack J6ActiveRun J6ActiveSchedule J6R32StatefulArithmetic
open J6R32ChildResidentTransfer J6R27OriginalGate J6R33StatefulArithmeticPage
open J6R37StructuredRoot J6R30GeneratedRootLayout J6R25PreparedSupply
open J6R48RawRoute J6R11Blueprint J1PPrinted J6R24MeteredRecursion J6R50SourceProducer
open J6R55BootBodies J6R54ExteriorOwner J6R53OldOwnerRoot J6R55TerminalOrigin
open J6R64.BootSeats J6R55SelectedPeak J6R52CacheWhole J6R54PeakInput
open J6R30ProducedGateRegistry J6R48DFS J6R49SourceLayout
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 22000000
set_option maxRecDepth 5100
set_option Elab.async false

noncomputable section
attribute [local irreducible] J6R12Blueprint.printedParams
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {P₀ : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P₀
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw own next : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
variable {s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group))
variable {b : ℕ}
variable (template : Meter (OccurrenceInput T ((Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group) (exteriorChild G ell X.centre X.sample X.group)).ticket w) key prec tw bw (pageKeyWidth m+pad)))
variable (L : BootLaneTape X gate pad) (S : TerminalSeats X sel (ticketReady T ((Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group) (exteriorChild G ell X.centre X.sample X.group)).ticket w)) (((Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group) (exteriorChild G ell X.centre X.sample X.group)).ticket w)).centerAt b)
variable (agree : template.result.geometry.edges=orderedExteriorEdges X)
variable {rootName : SourceVertex P₀→Word own}
variable (root : RootRoster (P:=P₀) gate pad rootName)
variable {name : ((exteriorChild G ell X.centre X.sample X.group).host.Row⊕
    (exteriorChild G ell X.centre X.sample X.group).host.Col)→Word next}
variable (K : KeyInputs X gate pad root name) (nameInj : Function.Injective name)
variable (ownerTape : Meter (OwnerTape (bootOccurrence X gate pad w template L S).result name))
variable (fallback : Addon next (dim ((Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group) (exteriorChild G ell X.centre X.sample X.group)).ticket w)) key prec (pageKeyWidth m+pad))

def canonicalLiteralFirstSlot : LiteralFirstSlot X gate pad root w T :=
  let input := bootOccurrence X gate pad w template L S
  let paired := paired_order_of_real_boot_occurrence X gate pad w template L S agree
  ⟨input,next,name,nameInj,K,bootProvider input.result name paired ownerTape fallback⟩

variable (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
variable (live : IsLive (X.seed pad) B) (rootInj : Function.Injective rootName)

def canonicalBootAtLiveExterior : Meter (StoredSite T ((Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group) (exteriorChild G ell X.centre X.sample X.group)).ticket w) key prec tw bw (pageKeyWidth m+pad)) :=
  assembleFirstExterior X gate pad root w
    (canonicalLiteralFirstSlot X gate pad w template L S agree root K nameInj ownerTape fallback)
    B live rootInj

theorem actual_first_exterior_has_counted_canonical_buffers
    (originPrefix queryPrefix seatPrefix rawPrefix indexedPrefix : ℕ) :
    let input := bootOccurrence X gate pad w template L S
    let mounted := mountFirstOwners X gate pad root B live K rootInj
    let boot := canonicalBootAtLiveExterior X gate pad w template L S agree root K nameInj ownerTape fallback B live rootInj
    boot.result.input=input.result ∧ boot.result.origins=initialOrigin X gate pad ∧
    canonicalInitCut input mounted ownerTape boot.result originPrefix queryPrefix seatPrefix rawPrefix indexedPrefix≤
      canonicalInitReserve input mounted boot.result.birth.port := by
  refine ⟨rfl,rfl,?_⟩
  let input := bootOccurrence X gate pad w template L S
  let mounted := mountFirstOwners X gate pad root B live K rootInj
  have paired := paired_order_of_real_boot_occurrence X gate pad w template L S agree
  exact canonical_first_boot_buffers_are_bounded input mounted (exterior_data_origin X gate pad) nameInj
    paired ownerTape fallback originPrefix queryPrefix seatPrefix rawPrefix indexedPrefix

theorem actual_post_publication_owner_and_boot_snapshots
    (i j originPrefix queryPrefix seatPrefix rawPrefix indexedPrefix : ℕ) :
    let input := bootOccurrence X gate pad w template L S
    let mounted := mountFirstOwners X gate pad root B live K rootInj
    let boot := canonicalBootAtLiveExterior X gate pad w template L S agree root K nameInj ownerTape fallback B live rootInj
    let chosen := (selectOwnerKeys X.address.group K.headers.result).result
    let old := exteriorOldPayloads X gate pad root
    let pages := exteriorReadPages X pad
    let stamp := (X.seed pad).immutable.payload.stamp
    ownerMountPrefixBits chosen old stamp pages K.dest.result mounted.result.raw i j≤
      ownerMountLocalReserve chosen old pages K.dest.result ∧
    canonicalInitCut input mounted ownerTape boot.result originPrefix queryPrefix seatPrefix rawPrefix indexedPrefix≤
      canonicalInitReserve input mounted boot.result.birth.port := by
  exact ⟨(real_exterior_owner_mount_yields_named_snapshots_and_output X gate pad root
      B live K rootInj).2 i j,
    (actual_first_exterior_has_counted_canonical_buffers X gate pad w template L S agree root K nameInj
      ownerTape fallback B live rootInj originPrefix queryPrefix seatPrefix rawPrefix indexedPrefix).2.2⟩

#print axioms canonicalLiteralFirstSlot
#print axioms canonicalBootAtLiveExterior
#print axioms actual_first_exterior_has_counted_canonical_buffers
#print axioms actual_post_publication_owner_and_boot_snapshots
end
end J6R66.BootPeak
