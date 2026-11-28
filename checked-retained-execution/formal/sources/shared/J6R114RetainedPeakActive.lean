import J6R114RetainedPeakEntry
import J6R111KeptOwnerFlowRun

/-! Inspect the actual active callback. This is one paused invocation
of the new retained interpreter, not a cost transfer from the old
R68 whole run. The stored packed result and the newly selected
packed result are distinct named payload roles. -/
namespace J6R114RetainedPeak
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R21Ancestor J6OrientedHost J6R34RootAtlas
open J6Mesh J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R34ChildPath J6R37StructuredRoot J6R41StructuredAllPaths
open J6R54TerminalBoot J6R53OldOwner J6R53OldOwnerRoot J6R26DescriptorTree J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion J6R52CacheSource
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS J6R10Repack J6ActiveSchedule
open J6R50SourceProducer J6R51Online J6R51ParentFrames J6R52CacheWhole J6R64Active J6R66Active
open J6R59Public J6R94HeldOwnerProvider J6R54PeakInput J6R48RawRoute J6R49SourceLayout
open J6R58RequestSource J6R52Dispatch J6R53Dispatch J6R27OriginalGate J6R36ChildFramedRoute
open J6R62ActivePrep J6R82LayoutDebit V8NativeMessage.N2DLabels J6R68ActiveInputs J6R68ActiveInputs.Sweep
open J6R9Recursive J6R22Active J6R49DFS J6R10Reachable
open J6R111KeptOwnerFlow J6R52Peak J6R53PeakAddon J6R55SelectedPeak J6R75RawPeak
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 15000000
set_option maxRecDepth 4900
set_option maxSynthPendingDepth 12
set_option Elab.async false

def oneOwnerHeaderBits {k : ℕ} (head : OwnerGroup k) : ℕ :=
  head.key.bits.length+head.group.bits.length

theorem actual_owner_header_file_width {k : ℕ} (xs : List (OwnerGroup k)) :
    rawLayoutBits oneOwnerHeaderBits xs = (k+6)*xs.length := by
  apply raw_layout_bits_fixed
  intro h _
  unfold oneOwnerHeaderBits
  rw [h.key.size,h.group.size]

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
variable {rank : ℕ} (D : KeptDrivers X M rank)
variable (retire : PageJob f ell key prec tw bw (pageKeyWidth m+pad)→ℕ)
variable (x : KeptInvocation X M)
variable (on : (printedParams (f:=f) (ell:=ell) s).cutoff<x.call.edges)

def incumbentAtActualActive :=
  readGroupHeadersForActive X x.path x.slot x.site x.entry

def layoutAtActualActive :=
  let incumbent := incumbentAtActualActive X M x
  selectedLayoutAndLabels (D.layout x on incumbent.result).setup

def mountedAtActualActive := mountResident x.site x.entry.resident

/-- Conservative named payload occupancy at this stage. It includes
one held encoding of each old and current packed output, and the
actual indexed addon and mounted cache as separate payloads. -/
def activeRetainedBits (shared : ℕ) : ℕ :=
  let h := incumbentAtActualActive X M x
  let pack := layoutAtActualActive X M D x on
  heldWithActualParentCache X x.path x.slot x.site x.entry shared +
    rawLayoutBits oneOwnerHeaderBits h.result.raw + packedKeptBits pack.result

theorem same_retained_active_uses_this_label_header_and_cache_in_its_callback :
    let sp := printedParams (f:=f) (ell:=ell) s
    let c := x.call
    let path := Path.step x.path x.slot
    let checked := readyAtPath T path on
    let incumbent := incumbentAtActualActive X M x
    let W := D.layout x on incumbent.result
    let layout := layoutAtActualActive X M D x on
    let plan := prepareFromKeptLayout X x.path x.slot x.site x.entry M on layout.result
      (D.fit path on) D.masks layout.steps
    let mounted := mountedAtActualActive X M x
    let out := plan.result.eval M.modeWidth (reachable_positive T path.reached) T.vPositive X.hf
      (fun t z β g=>
        let u := addressed (sel:=sel) checked t z β g
        let K := retainActualSelectedDemand X x.path x.slot x.site x.entry M u incumbent.result
        let keys := actual_live_keys_at_the_selected_site X M D x u
        let childLabels := checkedChildLabelWords X x.path x.slot x.site x.entry M on incumbent.result
          W u mounted.result keys layout.result rfl
        let same := selected_load_emits_the_actual_driver_source_after_retention X x.path x.slot x.site
          x.entry M u incumbent.result mounted.result x.actualSite
        project (nextR66OwnerScope X x.path x.slot x.site u K mounted.result keys retire childLabels
          (fun entered=>runRetained X M D retire ⟨c,path,u,_,same,entered⟩)
          (zeroM (T.bank (registerPrecision sp c t) (register_positive checked t)).hp) x.entry.bank))
    runRetained X M D retire x=
      ⟨(out.result,x.entry.bank),incumbent.steps+mounted.steps+plan.steps+out.steps⟩ := by
  rw [run_retained_unfolds_to_the_actual_child_callback]
  simp only [retainedBody,dif_neg (Nat.not_le_of_gt on),incumbentAtActualActive,layoutAtActualActive,mountedAtActualActive]

theorem true_active_reserve_counts_current_headers_without_omitting_any_held_tape
    (shared body : ℕ) (fit : ∀ t,(x.site.birth.native.physical.record t).body.length≤body) :
    let h := incumbentAtActualActive X M x
    let pack := layoutAtActualActive X M D x on
    let v := x.path.ticket x.slot
    activeRetainedBits X M D x on shared≤
      entryKeptBits X x.path x.slot x.site x.entry shared +
      v.child.edges*cachedRowCap x.site.birth.port x.site.site.ownerWidth key prec (pageKeyWidth m+pad)
        (dim v) body +(x.site.site.ownerWidth+6)*h.result.raw.length+packedKeptBits pack.result := by
  dsimp only [activeRetainedBits]
  rw [actual_owner_header_file_width]
  exact Nat.add_le_add_right
    (Nat.add_le_add_right (actual_mount_keeps_the_installed_addon_and_counts_its_frame_cache
      X x.path x.slot x.site x.entry shared body fit).2.2.2 _) _

#print axioms actual_owner_header_file_width
#print axioms activeRetainedBits
#print axioms same_retained_active_uses_this_label_header_and_cache_in_its_callback
#print axioms true_active_reserve_counts_current_headers_without_omitting_any_held_tape
end
end J6R114RetainedPeak

