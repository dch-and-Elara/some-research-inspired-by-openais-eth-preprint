import J6R94HeldOwnerProviderRetainLayout
import J6R59PublicResidentStop
import J6R94HeldOwnerProviderRetainRoster
import J6R55SelectedPeakWords

/-! The two newly kept tapes are actual live arguments at the
successful R59 scope. The layout labels are retained once at their
parent; the full raw roster is charged by its actual child loader. -/
namespace J6R94HeldOwnerProvider
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R27OriginalGate
open J6R25PreparedSupply J6R26DescriptorTree J6R34ChildPath J6R36ChildFramedRoute
open J6R24MeteredRecursion J6R10Repack J6R11Blueprint J6R12Blueprint J6ActiveRun J1PPrinted
open J6R50SourceProducer J6R34RootAtlas J6R53OldOwner J6R58RequestSource
open J6R51Online J6R49SourceLayout J6R52CacheSource J6R52CacheWhole J6R51ParentFrames
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R30ProducedGateRegistry
open J6R55SelectedPeak J6R59Public J6R48DFS
set_option quotPrecheck false
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 5100
set_option maxHeartbeats 31000000
set_option Elab.async false

structure LiveOwnerPair {U : Type} {a copies w edges own gate key prec page : ℕ}
    (names : U→Word own) (values : U→OwnerData gate key prec page) where
  packed : KeptLayoutWords a copies w edges
  owners : CompleteRoster names values

/-- These are only the two additional selected payloads, not an
    observation of unrelated buffers or a heap allocation. -/
def liveOwnerPairBits {U : Type} {a copies w edges own gate key prec page : ℕ}
    {names : U→Word own} {values : U→OwnerData gate key prec page}
    (x : LiveOwnerPair (a:=a) (copies:=copies) (w:=w) (edges:=edges) names values) : ℕ :=
  selectedLabelBits x.packed.labels+(indexedOwnerTape x.owners.raw).length

/-- The wrapper passes immutable arguments to the called program;
    it does not copy or serialize either tape. -/
def withLiveOwnerPair {U Out : Type} {a copies w edges own gate key prec page : ℕ}
    {names : U→Word own} {values : U→OwnerData gate key prec page}
    (packed : KeptLayoutWords a copies w edges) (owners : CompleteRoster names values)
    (read : LiveOwnerPair (a:=a) (copies:=copies) (w:=w) (edges:=edges) names values→Meter Out) :
    Meter Out :=
  let args := ⟨packed,owners⟩
  let out := read args
  ⟨out.result,out.steps+6⟩

theorem recorded_pair_is_the_actual_arguments_and_control_fee
    {U Out : Type} {a copies w edges own gate key prec page : ℕ}
    {names : U→Word own} {values : U→OwnerData gate key prec page}
    (packed : KeptLayoutWords a copies w edges) (owners : CompleteRoster names values)
    (read : LiveOwnerPair (a:=a) (copies:=copies) (w:=w) (edges:=edges) names values→Meter Out) :
    let args : LiveOwnerPair (a:=a) (copies:=copies) (w:=w) (edges:=edges) names values := ⟨packed,owners⟩
    withLiveOwnerPair packed owners read=⟨(read args).result,(read args).steps+6⟩ ∧
      liveOwnerPairBits args=selectedLabelBits packed.labels+(indexedOwnerTape owners.raw).length := ⟨rfl,rfl⟩

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page gate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
variable {v : Ticket sel r} {u : (Plan sel).Slot v.child}
variable (Y : StoredSite T v key prec tw bw page)
variable (gates : v.parent.host.Row⊕v.parent.host.Col→Option (CodeGate (Word gate)))
variable (K : Meter (HeldOwnerLoad Y (u:=u) gates))
variable (cache : CachedParentFrames Y.site)
variable {a copies w edges : ℕ}
variable (packed : KeptLayoutWords a copies w edges)
variable {Out : Type}
variable (retire : PageJob f ell key prec tw bw page→ℕ)

abbrev HeldPairBody :=
  LiveOwnerPair (a:=a) (copies:=copies) (w:=w) (edges:=edges) (nameCurrentOwner Y) (childData Y gates)→
    ResidentBank (cachedAdvance Y u K.result.load cache).next→
    PageBank f ell key prec tw bw page→Meter (Out×PageBank f ell key prec tw bw page)

def resumeScopedPair (resume : HeldPairBody (a:=a) (copies:=copies) (w:=w) (edges:=edges) (Out:=Out) Y gates K cache)
    (res : ResidentBank (cachedAdvance Y u K.result.load cache).next) (B : PageBank f ell key prec tw bw page) :
    Meter (Out×PageBank f ell key prec tw bw page) :=
  withLiveOwnerPair packed K.result.held (fun both=>resume both res B)

/-- Keep the already-produced raw arguments through an actual R59
    scope. A later typed consumer can use the separate byte-preserving
    `carriedRosterForCachedChild` retype. -/
def visitScopedHeldOwnerPair
    (resume : HeldPairBody (a:=a) (copies:=copies) (w:=w) (edges:=edges) (Out:=Out) Y gates K cache)
    (bad : Meter Out) (B : PageBank f ell key prec tw bw page) :
    Meter (Out×PageBank f ell key prec tw bw page) :=
  visitCachedBankOnce Y ⟨K.result.load,K.steps⟩ cache retire
    (resumeScopedPair Y gates K cache packed resume) bad B

theorem actual_pair_resume_invokes_the_consumer_once
    (resume : HeldPairBody (a:=a) (copies:=copies) (w:=w) (edges:=edges) (Out:=Out) Y gates K cache)
    (res : ResidentBank (cachedAdvance Y u K.result.load cache).next)
    (B : PageBank f ell key prec tw bw page) :
    let done := resume ⟨packed,K.result.held⟩ res B
    resumeScopedPair Y gates K cache packed resume res B=⟨done.result,done.steps+6⟩ := rfl

theorem real_scope_keeps_both_paid_tapes_and_restores_the_same_bank
    (resume : HeldPairBody (a:=a) (copies:=copies) (w:=w) (edges:=edges) (Out:=Out) Y gates K cache)
    (bad : Meter Out) (B : PageBank f ell key prec tw bw page)
    (ready : JobsReady B [(cachedAdvance Y u K.result.load cache).next.birth.job]) :
    let X := (cachedAdvance Y u K.result.load cache).next
    let j := X.birth.job
    let write := J6R48GeneratedAddons.emit (K.result.load.directory.read Y K.result.load.event)
      X.birth.native.physical.order
    let res := installResidentBank X
    let called := resumeScopedPair Y gates K cache packed resume res.result (afterOne B j)
    visitScopedHeldOwnerPair Y gates K cache packed retire resume bad B=
      ⟨(called.result.1,B),(K.steps+(write.steps+res.steps))+
        (publishFee B j.entry j.offset j.built+called.steps+retire j+4)⟩ :=
  cached_scope_pays_one_install_and_the_actual_terminal Y ⟨K.result.load,K.steps⟩ cache
    retire (resumeScopedPair Y gates K cache packed resume) bad B ready

theorem actual_pair_callback_selected_fields_have_their_two_payload_sizes :
    let pair : LiveOwnerPair (a:=a) (copies:=copies) (w:=w) (edges:=edges)
      (nameCurrentOwner Y) (childData Y gates) := ⟨packed,K.result.held⟩
    liveOwnerPairBits pair=selectedLabelBits packed.labels+(indexedOwnerTape K.result.held.raw).length := rfl

#print axioms recorded_pair_is_the_actual_arguments_and_control_fee
#print axioms actual_pair_resume_invokes_the_consumer_once
#print axioms real_scope_keeps_both_paid_tapes_and_restores_the_same_bank
#print axioms actual_pair_callback_selected_fields_have_their_two_payload_sizes
end
end J6R94HeldOwnerProvider