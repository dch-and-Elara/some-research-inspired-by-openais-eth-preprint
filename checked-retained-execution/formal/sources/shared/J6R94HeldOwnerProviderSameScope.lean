import J6R94HeldOwnerProviderLiteral
import J6R94HeldOwnerProviderKept
import J6R94HeldOwnerProviderRetainPair

namespace J6R94HeldOwnerProvider
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R21Ancestor J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R35RootOrigins J6R26DescriptorTree J6R34ChildPath
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS
open J6R50Leaf J6R50SourceProducer J6R51Leaf J6R51Online J6R49Leaf J6R48Leaf
open J6R57Public J6R58LeafScale J6R62Leaf J6R27OriginalGate J6R36ChildFramedRoute J6R54TerminalBoot
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R37StructuredRoot J6R41StructuredAllPaths
open J6R52Terminal J6R53TerminalGate J6R53OldOwner J6R49SourceLayout J6R66LeafTariff J6R65LeafRate
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 41000000
set_option maxRecDepth 5500
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
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable {c : Call (PhysicalHost f ell)}
variable (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c)
variable (w : (Plan sel).Slot c)
local notation "ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "Bank" => (PageBank f ell key prec tw bw (pageKeyWidth m+pad))
local notation "Cmd" => (ReadCmd key (pageKeyWidth m+pad))
local notation "deg" => (4*Nat.clog 2 s)
local notation "ch" => (p.ticket w).child

open J6R52CacheWhole J6R51ParentFrames J6R82LayoutDebit J6R82LeafTime
open J6R9Recursive J6R58LeafScale J6R16ModeCost J6R14LayoutCost J6R68ActiveInputs
open V8NativeMessage.N2DLabels J6R10Repack
local instance sameScopeEdge : Fintype c.host.Edge := c.host.finiteEdge

open J6R59Public J6R27OriginalGate J6R30ProducedGateRegistry J6R52CacheSource

section ResidentReindex
variable {v : Ticket sel (exteriorChild G ell X.centre X.sample X.group)}
variable {A D : StoredSite T v key prec tw bw (pageKeyWidth m+pad)}

def moveResidentToSource (e : A=D) (R : ResidentBank A) : ResidentBank D := e ▸ R

theorem moved_resident_uses_the_same_rows (e : A=D) (R : ResidentBank A) :
    HEq (moveResidentToSource (X:=X) e R).rows R.rows := by
  cases e
  rfl
end ResidentReindex

section ActualNext
variable (u : (Plan sel).Slot (p.ticket w).child)
variable (K : Meter (HeldOwnerLoad (sourceState M p w) (u:=u) (gateHistory T (bootGates X) p)))
variable (cache : CachedParentFrames (sourceState M p w).site)
variable (keys : NativeCreationOwnerContext (sourceState M p w) K.result.load)
variable (picked : K.result.load=(M.demand (sourceState M p w) u).result)
variable (inj : Function.Injective (sourceState M (.step p w) u).site.oldKey)
local instance nextParentEdge : Fintype (p.ticket w).child.host.Edge := (p.ticket w).child.host.finiteEdge
variable (I : CallFormat (printedParams (f:=f) (ell:=ell) s) (p.ticket w).child)
variable (W : Ingress I) (units : ℕ) {a cp wid edges : ℕ}
variable (raw : KeptLayoutWords a cp wid edges) (axisBits : List Bool)
variable (same : ExistingRosterLabels (sourceState M (.step p w) u) (gateHistory T (bootGates X) (.step p w))
  (rosterActuallyCarriedToNext X M p w u K cache keys picked) I W units raw.rawView axisBits)

def inputFromTheActualChildInstall
    (resident : ResidentBank (cachedAdvance (sourceState M p w) u K.result.load cache).next) :
    Meter (OwnerTerminalInput X (.step p w) u (sourceState M (.step p w) u)) :=
  actualStoppedInputFromKeptTapes X M (.step p w) u
    (moveResidentToSource (X:=X) (prior_held_load_is_same_next_source X M p w u K cache picked) resident)
    (rosterActuallyCarriedToNext X M p w u K cache keys picked) inj I W units raw axisBits same

/-- Read exactly the bank handed to us by the physical publication. The
selected resident and owner tapes remain the installed ones, and no
operation reconstructs an ancestor or performs a second publication. -/
def readKeptAtThePublishedBank
    (resident : ResidentBank (cachedAdvance (sourceState M p w) u K.result.load cache).next)
    (fresh : Bank) : Meter (Block (T.frame (Path.step (Path.step p w) u).reached) ell) :=
  let A := inputFromTheActualChildInstall X M p w u K cache keys picked inj I W units raw axisBits same resident
  let F := T.frame (Path.step (Path.step p w) u).reached
  finishOwnerAttempt F (executeOwnerTerminal X (.step p w) u (sourceState M (.step p w) u) A F fresh)

/-- The equality is about the entire *new* Meter from the same reader
on the exact newly published bank, and not a replacement fee for an
old unmatched supplier. -/
theorem same_R65_meter_reads_the_actual_scoped_published_bank
    (resident : ResidentBank (cachedAdvance (sourceState M p w) u K.result.load cache).next)
    (initial : Bank) :
    readKeptAtThePublishedBank X M p w u K cache keys picked inj I W units raw axisBits same resident
      (afterOne (stackBank (borns M) initial (.step p w))
        (cachedAdvance (sourceState M p w) u K.result.load cache).next.birth.job)=
      readProvidedOnR65Bank X M (.step p w) u
        (inputFromTheActualChildInstall X M p w u K cache keys picked inj I W units raw axisBits same resident) initial := by
  rw [←actual_R65_entry_uses_the_same_held_child_bank X M p w u K cache picked initial]
  rfl

variable (retire : PageJob f ell key prec tw bw (pageKeyWidth m+pad)→ℕ)
variable (bad : Meter (Block (T.frame (Path.step (Path.step p w) u).reached) ell))

def visitActualHeldPositiveRead (B : Bank) : Meter (Block (T.frame (Path.step (Path.step p w) u).reached) ell×Bank) :=
  visitCachedBankOnce (sourceState M p w) ⟨K.result.load,K.steps⟩ cache retire
    (fun resident fresh=>
      let out := readKeptAtThePublishedBank X M p w u K cache keys picked inj I W units raw axisBits same resident fresh
      ⟨(out.result,fresh),out.steps+6⟩) bad B

/-- At the actual successful publication, a positive reader consumes
both previously paid tapes and the one resident install. The original
published scope and real retire operation remain in the bill. -/
theorem executed_scope_feeds_the_real_R65_positive_reader
    (initial : Bank)
    (ready : JobsReady (stackBank (borns M) initial (.step p w))
      [(cachedAdvance (sourceState M p w) u K.result.load cache).next.birth.job]) :
    let B := stackBank (borns M) initial (.step p w)
    let next := (cachedAdvance (sourceState M p w) u K.result.load cache).next
    let job := next.birth.job
    let write := J6R48GeneratedAddons.emit (K.result.load.directory.read (sourceState M p w) K.result.load.event)
      next.birth.native.physical.order
    let resident := installResidentBank next
    let actual := readProvidedOnR65Bank X M (.step p w) u
      (inputFromTheActualChildInstall X M p w u K cache keys picked inj I W units raw axisBits same resident.result) initial
    visitActualHeldPositiveRead X M p w u K cache keys picked inj I W units raw axisBits same retire bad B=
      ⟨(actual.result,B),(K.steps+(write.steps+resident.steps))+
        (publishFee B job.entry job.offset job.built+(actual.steps+6)+retire job+4)⟩ := by
  let B := stackBank (borns M) initial (.step p w)
  let next := (cachedAdvance (sourceState M p w) u K.result.load cache).next
  let read := fun (resident : ResidentBank next) (fresh : Bank)=>
    let out := readKeptAtThePublishedBank X M p w u K cache keys picked inj I W units raw axisBits same resident fresh
    (⟨(out.result,fresh),out.steps+6⟩ : Meter (_×Bank))
  have h := cached_scope_pays_one_install_and_the_actual_terminal (sourceState M p w)
    (⟨K.result.load,K.steps⟩ : Meter (LocalLoad (sourceState M p w) u)) cache retire read bad B ready
  dsimp only at h ⊢
  unfold visitActualHeldPositiveRead
  rw [h]
  dsimp only [read]
  rw [same_R65_meter_reads_the_actual_scoped_published_bank]

end ActualNext
#print axioms moved_resident_uses_the_same_rows
#print axioms same_R65_meter_reads_the_actual_scoped_published_bank
#print axioms executed_scope_feeds_the_real_R65_positive_reader
end
end J6R94HeldOwnerProvider