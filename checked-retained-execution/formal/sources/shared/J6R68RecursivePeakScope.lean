import J6R66ActiveCompare
import J6R66BootPeakMount

/-! A success path of the actual R66 header interpreter. These equalities
are about its actual callback bank, creation record, and returned Meter;
parent restoration only holds after it has run the child on the enlarged
bank. The proof replay below is not an execution of a second publisher. -/
namespace J6R68.RecursivePeak
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R21Ancestor J6R26DescriptorTree
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R48DFS J6R50SourceProducer J6R24MeteredRecursion
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R51Online J6R51ParentFrames J6R52CacheWhole J6R52CacheSource J6R48RawRoute
open J6R54PeakInput J6R64Active J6R66Active J6R66.BootPeak
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 12000000
set_option maxRecDepth 4100
set_option Elab.async false

theorem the_actual_header_scope_enters_its_published_head
    {key prec tw bw : ℕ} {D Out : Type}
    (retire : Job (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) D→ℕ)
    (j : Job (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) D)
    (go : (R : Ledger key prec tw bw D)→OwnsHeader j.entry.result R→
        Meter (Out×Ledger key prec tw bw D))
    (bad : Meter Out) (B : Ledger key prec tw bw D) (legal : JobsReady B [j]) :
    let live := afterOne B j
    let entered := go live (show OwnsHeader j.entry.result live from rfl)
    withScopeHeader retire j go bad B=
      ⟨(entered.result.1,B),publishFee B j.entry j.offset j.built+entered.steps+retire j+4⟩ := by
  classical
  let old (R : Ledger key prec tw bw D) : Meter (Out×Ledger key prec tw bw D) :=
    if h : OwnsHeader j.entry.result R then go R h else ⟨(bad.result,R),bad.steps⟩
  have same (R : Ledger key prec tw bw D) (h : OwnsHeader j.entry.result R) :
      go R h=old R := by rw [show old R=(if e : OwnsHeader j.entry.result R then go R e else
        ⟨(bad.result,R),bad.steps⟩) from rfl,dif_pos h]
  have here : OwnsHeader j.entry.result (afterOne B j) := rfl
  rw [scope_same_meter_of_same_continuation retire j go old bad B same,
    J6R48DFS.paid_scope_exact _ _ _ _ _ legal]
  simp only [old,dif_pos here]

noncomputable section
attribute [local irreducible] J6R12Blueprint.printedParams
variable {f : ℤ[X]} {ell s C key prec tw bw page q cw ew : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "P" => (@Plan f ell s sel)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)

theorem one_emission_is_same_actual_next_site
    {v : Ticket sel r} {X : StoredSite T v key prec tw bw page} {u : (P).Slot v.child}
    (K : LocalLoad X u) (cache : CachedParentFrames X.site) :
    (produceCacheSidecarOnce K cache).result.next=K.advance.next := by
  unfold produceCacheSidecarOnce
  rw [shared_emission_preserves_the_actual_stored_site]
  exact congrArg Advance.next (cached_advance_exact X u K cache)

theorem open_once_enters_that_header_and_addon_bank
    {v : Ticket sel r} {X : StoredSite T v key prec tw bw page} {u : (P).Slot v.child}
    {Out : Type} (started : Meter (LocalLoad X u)) (cache : CachedParentFrames X.site)
    (retire : J→ℕ) (go : (next : StoredSite T (successorTicket v u) key prec tw bw page)→
      WithIncoming next Out) (bad : Meter Out) (B : L)
    (legal : JobsReady B [started.result.advance.next.birth.job]) :
    let made := produceCacheSidecarOnce started.result cache
    let next := started.result.advance.next
    let job := next.birth.job
    let child := afterOne B job
    let res := installResidentBank next
    let out := go next res.result child (show OwnsHeader job.entry.result child from rfl)
    openOnce started cache retire go bad B=
      ⟨(out.result.1,B),started.steps+(made.steps+res.steps)+
        (publishFee B job.entry job.offset job.built+out.steps+retire job+4)⟩ ∧
    mountedSelectedBits child=mountedSelectedBits B+mountedInsertionBits job := by
  let made := produceCacheSidecarOnce started.result cache
  have same : made.result.next=started.result.advance.next :=
    one_emission_is_same_actual_next_site started.result cache
  refine ⟨?_,publication_adds_exact_selected_record B _⟩
  let entry (next : StoredSite T (successorTicket v u) key prec tw bw page)
      (ok : JobsReady B [next.birth.job]) :
      let j := next.birth.job
      let after := afterOne B j
      let installed := installResidentBank next
      let done := go next installed.result after (show OwnsHeader j.entry.result after from rfl)
      withScopeHeader retire j (fun R owned=>go next installed.result R owned) bad B=
        ⟨(done.result.1,B),publishFee B j.entry j.offset j.built+done.steps+retire j+4⟩ :=
    the_actual_header_scope_enters_its_published_head retire next.birth.job _ bad B ok
  unfold openOnce
  dsimp only
  change (let next := made.result.next
          let res := installResidentBank next
          let out := withScopeHeader retire next.birth.job (fun R own=>go next res.result R own) bad B
          (⟨out.result,started.steps+(made.steps+res.steps)+out.steps⟩ : Meter (Out×L)))=_
  rw [same]
  dsimp only
  rw [entry _ legal]

theorem boot_header_enters_that_first_bank
    {w : (P).Slot r} {Out : Type}
    (boot : Meter (StoredSite T ((Path.root : Path sel r r).ticket w) key prec tw bw page))
    (retire : J→ℕ)
    (go : (k : StoredSite T ((Path.root : Path sel r r).ticket w) key prec tw bw page)→
      WithIncoming k Out) (bad : Meter Out) (B : L) (legal : JobsReady B [boot.result.birth.job]) :
    let job := boot.result.birth.job
    let next := afterOne B job
    let res := installResidentBank boot.result
    let out := go boot.result res.result next (show OwnsHeader job.entry.result next from rfl)
    bootWithHeader boot retire go bad B=
      ⟨(out.result.1,B),boot.steps+(publishFee B job.entry job.offset job.built+
        (res.steps+out.steps)+retire job+4)⟩ ∧
    mountedSelectedBits next=mountedSelectedBits B+mountedInsertionBits job := by
  refine ⟨?_,publication_adds_exact_selected_record B _⟩
  unfold bootWithHeader
  dsimp only
  rw [the_actual_header_scope_enters_its_published_head _ _ _ _ _ legal]

#print axioms the_actual_header_scope_enters_its_published_head
#print axioms one_emission_is_same_actual_next_site
#print axioms open_once_enters_that_header_and_addon_bank
#print axioms boot_header_enters_that_first_bank
end
end J6R68.RecursivePeak
