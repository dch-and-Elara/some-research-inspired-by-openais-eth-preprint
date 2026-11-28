import J6R57PublicNoChartExactRows
import J6R52CacheWholePrep
import J6R53PeakAddonPath

namespace J6R59Public
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6R27OriginalGate J6OrientedHost
open J6Mesh J6R35RootOrigins J6R37StructuredRoot J6R34RootAtlas J6R31RootResidentTables
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R32RootGeneratedRegistryInputs
open J6R26DescriptorTree J6R34ChildPath J6R36ChildFramedRoute J6R50SourceProducer
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R22Active J6R24MeteredRecursion
open J6R9Recursive J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R49SourceLayout
open J6R51ParentFrames J6R51Online J6R52Terminal J6R53TerminalGate J6R53TerminalExterior
open J6R53OldOwner J6R50Leaf J6R41StructuredAllPaths J6R54TerminalBoot J6R51Leaf J6R48DFS
open J6R57Public J6R52CacheWhole J6R52CacheSource J6R53PeakAddon J6R30ProducedGateRegistry
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8500000
set_option maxRecDepth 5500
set_option Elab.async false

noncomputable section
section CacheScope
variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel root hf}
variable {v : Ticket sel root}
variable (Y : StoredSite T v key prec tw bw page)
variable {u : (Plan sel).Slot v.child}
variable (started : Meter (LocalLoad Y u))
variable (cache : CachedParentFrames Y.site)
variable {Out : Type}
variable (retire : PageJob f ell key prec tw bw page→ℕ)
variable (read : ResidentBank (cachedAdvance Y u started.result cache).next→
  PageBank f ell key prec tw bw page→Meter (Out × PageBank f ell key prec tw bw page))
variable (bad : Meter Out) (B : PageBank f ell key prec tw bw page)

def visitCachedBankOnce : Meter (Out × PageBank f ell key prec tw bw page) :=
  let K := started.result
  let next := (cachedAdvance Y u K cache).next
  let made := J6R48GeneratedAddons.emit (K.directory.read Y K.event) next.birth.native.physical.order
  let resident := installResidentBank next
  let scope := J6R48DFS.withScope retire next.birth.job
    (read resident.result) bad B
  ⟨scope.result,(started.steps+(made.steps+resident.steps))+scope.steps⟩

theorem cached_scope_pays_one_install_and_the_actual_terminal
    (valid : JobsReady B [((cachedAdvance Y u started.result cache).next).birth.job]) :
    let K := started.result
    let next := (cachedAdvance Y u K cache).next
    let j := next.birth.job
    let made := J6R48GeneratedAddons.emit (K.directory.read Y K.event) next.birth.native.physical.order
    let resident := installResidentBank next
    let out := read resident.result (afterOne B j)
    visitCachedBankOnce Y started cache retire read bad B=
      ⟨(out.result.1,B),(started.steps+(made.steps+resident.steps))+
        (publishFee B j.entry j.offset j.built+out.steps+retire j+4)⟩ := by
  unfold visitCachedBankOnce
  dsimp only
  rw [J6R48DFS.paid_scope_exact _ _ _ _ _ valid]
end CacheScope

section BankView
variable {f : ℤ[X]} {ell s C key prec tw bw page rate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
variable (M : OnlineMachine T key prec tw bw page rate)
variable (p : J6R32StatefulArithmetic.Path sel r c) (w : (Plan sel).Slot c)
variable (u : (Plan sel).Slot (p.ticket w).child)
variable (K : Meter (LocalLoad (sourceState M p w) u))
variable (cache : CachedParentFrames (sourceState M p w).site)

private theorem resident_install_heq {v : Ticket sel r} {a b : StoredSite T v key prec tw bw page}
    (e : a=b) : HEq (installResidentBank a) (installResidentBank b) := by
  cases e
  rfl

theorem held_scope_uses_the_counted_source_bank
    (load : K.result=(M.demand (sourceState M p w) u).result) :
    HEq (installResidentBank (cachedAdvance (sourceState M p w) u K.result cache).next)
      (sourceBankAt M (.step p w) u) := by
  unfold sourceBankAt
  apply resident_install_heq
  simp only [cached_advance_exact,load,sourceState]
end BankView

section Reader
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C rate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable {c : Call (PhysicalHost f ell)}
variable (p : J6R32StatefulArithmetic.Path sel (exteriorChild G ell X.centre X.sample X.group) c)
variable (w : (Plan sel).Slot c)
variable (Y : StoredSite T (p.ticket w) key prec tw bw (pageKeyWidth m+pad))
variable (res : ResidentBank Y)
variable (held : CompleteRoster Y.site.oldKey (parentData Y (gateHistory T (bootGates X) p)))
variable (inj : Function.Injective Y.site.oldKey)
variable (groups : Meter (List (Word 6)))
variable (align : groups.result=held.order.map (fun x=>(ownerGroupRow Y.site x).group))
variable (F : Frame f (p.ticket w).child.prec)
variable (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad))

/-- The roster is already held and paid in the load. Mount the frame
cache over the actual resident rows; do not call installResidentBank. -/
def readHeldPositiveOwner : Meter (Option (Block F ell) × PageBank f ell key prec tw bw (pageKeyWidth m+pad)) :=
  let cache := mountResident Y res
  let inputs := packMeasuredOwnerInput X p w Y cache ⟨held,0⟩ groups align inj
  let out := executeOwnerTerminal X p w Y inputs F B
  ⟨(out.result,B),out.steps⟩

theorem read_held_terminal_pays_cache_and_reuses_held_roster :
    let cache := mountResident Y res
    let inps := packMeasuredOwnerInput X p w Y cache ⟨held,0⟩ groups align inj
    let out := executeOwnerTerminal X p w Y inps F B
    readHeldPositiveOwner X p w Y res held inj groups align F B=⟨(out.result,B),out.steps⟩ ∧
      ((readHeldPositiveOwner X p w Y res held inj groups align F B).steps=
        inps.steps+
          (meteredTerminalFromOwners Y inps.result.saved inps.result.headers.raw inps.result.roster.raw
            (p.ticket w).child.edges F B).steps+4) := ⟨rfl,rfl⟩

variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable (gate : Stamp key prec)
variable (boot : ExactPrintedBoot X M gate)
include boot in
theorem real_held_terminal_has_exact_positive_source_value
    (same : Y=sourceState M p w)
    (gateWidth : gate.created.val=base) (basePos : 0<base)
    (positive : 0<(p.ticket w).child.edges)
    (outside : IsLive (X.seed pad) B)
    (inside : opened (borns M) (IsLive (X.seed pad)) (.step p w) B) :
    ∃ word,(readHeldPositiveOwner X p w Y res held inj groups align F B).result.1=some word ∧
      F.decode word=reduce (p.ticket w).child.prec f ell ((p.ticket w).child.host.contract X.hf) := by
  subst Y
  let Y := sourceState M p w
  let inps := packMeasuredOwnerInput X p w Y (mountResident Y res) ⟨held,0⟩ groups align inj
  exact actual_owner_terminal_correct_without_legacy_chart X M gate boot p w inps F B gateWidth basePos
    positive (IsLive (X.seed pad)) outside inside
end Reader

#print axioms visitCachedBankOnce
#print axioms cached_scope_pays_one_install_and_the_actual_terminal
#print axioms held_scope_uses_the_counted_source_bank
#print axioms readHeldPositiveOwner
#print axioms read_held_terminal_pays_cache_and_reuses_held_roster
#print axioms real_held_terminal_has_exact_positive_source_value
end
end J6R59Public
