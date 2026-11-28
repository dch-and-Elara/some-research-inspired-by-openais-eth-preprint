import J6R111KeptOwnerFlowEntry
import J6R94HeldOwnerProviderSameScope
import J6R94HeldOwnerProviderRosterLayout

/-! Keep the real R59 full roster across the one actual R66
successor scope; the continuation also receives that scope's indexed
resident result and its newly published directory head. -/
namespace J6R111KeptOwnerFlow
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6OrientedHost J6R34RootAtlas
open J6Mesh J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R34ChildPath J6R37StructuredRoot J6R41StructuredAllPaths
open J6R54TerminalBoot J6R53OldOwner J6R53OldOwnerRoot J6R26DescriptorTree J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion J6R52CacheSource
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS
open J6R50SourceProducer J6R51Online J6R51ParentFrames J6R52CacheWhole J6R64Active J6R66Active J6R68.RecursivePeak
open J6R59Public J6R94HeldOwnerProvider J6R54PeakInput J6R48RawRoute
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 29000000
set_option maxRecDepth 5700
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
variable {c : Call (PhysicalHost f ell)}
variable (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c)
variable (w : (Plan sel).Slot c)
variable (Y : StoredSite T (p.ticket w) key prec tw bw (pageKeyWidth m+pad))
variable (u : (Plan sel).Slot (p.ticket w).child)
variable (K : Meter (HeldOwnerLoad Y (u:=u) (gateHistory T (bootGates X) p)))
variable (cache : CachedParentFrames Y.site)
variable (keys : NativeCreationOwnerContext Y K.result.load)


/-- This name is for the output of the one real sidecar producer. -/
abbrev producedSuccessor :=
  (produceCacheSidecarOnce K.result.load cache).result.next

theorem sidecar_and_cached_scope_produce_the_same_site :
    (produceCacheSidecarOnce K.result.load cache).result.next=
      (cachedAdvance Y u K.result.load cache).next :=
  (one_emission_is_same_actual_next_site K.result.load cache).trans
    (congrArg Advance.next (cached_advance_exact Y u K.result.load cache)).symm

def carriedRosterAtEmission :
    CompleteRoster
      (produceCacheSidecarOnce K.result.load cache).result.next.site.oldKey
      (parentData (produceCacheSidecarOnce K.result.load cache).result.next
        (gateHistory T (bootGates X) (.step p w))) :=
  moveOwnerRoster (X:=X) (sidecar_and_cached_scope_produce_the_same_site X p w Y u K cache).symm
    (carriedRosterForCachedChild Y (gateHistory T (bootGates X) p) K.result cache keys)

theorem emitted_child_keeps_the_complete_original_roster_in_its_paid_order :
    let carried := carriedRosterAtEmission X p w Y u K cache keys
    carried.order=K.result.held.order ∧ HEq carried.raw K.result.held.raw ∧
      ∀ j,j ∈ carried.order := by
  let original := carriedRosterForCachedChild Y (gateHistory T (bootGates X) p) K.result cache keys
  have castOnly := move_owner_roster_preserves_raw (X:=X)
    (sidecar_and_cached_scope_produce_the_same_site X p w Y u K cache).symm original
  have literal := carried_roster_has_the_actual_raw_payload Y (gateHistory T (bootGates X) p) K.result cache keys
  exact ⟨castOnly.1.trans literal.1,castOnly.2.trans literal.2,
    (carriedRosterAtEmission X p w Y u K cache keys).complete⟩

variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)

theorem made_successor_on_the_exact_selected_load_is_the_next_R66_source
    (here : Y=sourceState M p w)
    (same : HEq K.result.load (M.demand (sourceState M p w) u).result) :
    (produceCacheSidecarOnce K.result.load cache).result.next=sourceState M (.step p w) u := by
  subst Y
  have selected : K.result.load=(M.demand (sourceState M p w) u).result := eq_of_heq same
  rw [one_emission_is_same_actual_next_site K.result.load cache,selected]
  rfl

variable {Out : Type}
variable (retire : PageJob f ell key prec tw bw (pageKeyWidth m+pad)→ℕ)
variable (labels : LabelWitness X (.step p w) u
  (produceCacheSidecarOnce K.result.load cache).result.next (carriedRosterAtEmission X p w Y u K cache keys))
variable (resume : CapturedEntry X (.step p w) u
  (produceCacheSidecarOnce K.result.load cache).result.next→Meter (Out×PageBank f ell key prec tw bw (pageKeyWidth m+pad)))
variable (bad : Meter Out) (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad))

/-- The real R66 continuation with the retained fields. Its code invokes
one R54 sidecar producer, once installs that exact result, then runs the
continuation under the actual published head. The roster's view is an
erased identification of the already-paid R59 words. -/
def nextR66OwnerScope : Meter (Out×PageBank f ell key prec tw bw (pageKeyWidth m+pad)) :=
  let made := produceCacheSidecarOnce K.result.load cache
  let next := made.result.next
  let roster := carriedRosterAtEmission X p w Y u K cache keys
  let installed := installResidentBank next
  let out := @withScopeHeader key prec tw bw (PagedEnvelope f ell prec (pageKeyWidth m+pad)) Out retire next.birth.job
    (fun opened owned=>resume ⟨installed.result,opened,owned,roster,labels⟩) bad B
  ⟨out.result,K.steps+(made.steps+installed.steps)+out.steps⟩

/-- Successful scope calls the supplied active-or-stop continuation on
the actual born state, with one publish/install and the usual retire. -/
theorem next_R66_scope_keeps_the_paid_roster_and_actual_installed_resident
    (legal : JobsReady B [(produceCacheSidecarOnce K.result.load cache).result.next.birth.job]) :
    let made := produceCacheSidecarOnce K.result.load cache
    let next := made.result.next
    let job := next.birth.job
    let installed := installResidentBank next
    let owners := carriedRosterAtEmission X p w Y u K cache keys
    let done := resume ⟨installed.result,afterOne B job,rfl,owners,labels⟩
    nextR66OwnerScope X p w Y u K cache keys retire labels resume bad B =
      ⟨(done.result.1,B),K.steps+(made.steps+installed.steps)+
        (publishFee B job.entry job.offset job.built+done.steps+retire job+4)⟩ := by
  unfold nextR66OwnerScope
  dsimp only
  rw [the_actual_header_scope_enters_its_published_head _ _ _ _ _ legal]

/-- Forgetting only the newly retained fields gives the original R66
`openOnce` with the same incoming producer, not an old tariff rewrite. -/
theorem forgetting_the_new_fields_has_the_same_R66_open_meter
    (child : (next : StoredSite T (successorTicket (p.ticket w) u) key prec tw bw (pageKeyWidth m+pad))→
      WithIncoming next Out) :
    nextR66OwnerScope X p w Y u K cache keys retire labels
      (fun A=>child _ A.resident A.bank A.own) bad B=
      openOnce (⟨K.result.load,K.steps⟩ : Meter (LocalLoad Y u)) cache retire child bad B := rfl

#print axioms emitted_child_keeps_the_complete_original_roster_in_its_paid_order
#print axioms made_successor_on_the_exact_selected_load_is_the_next_R66_source
#print axioms next_R66_scope_keeps_the_paid_roster_and_actual_installed_resident
#print axioms forgetting_the_new_fields_has_the_same_R66_open_meter
end
end J6R111KeptOwnerFlow

