import J6R64ActiveScopeKernel
import J6R57ScopeFeeRetire

/-! The R66 header scope returns the captured parent Ledger and uses
retirement only as a Nat debit. This executable observer uses the
same install and continuation and exposes the two actually copied
fixed words on the successful return. No child Ledger is retained by
the extra observation. Its projection is the original full Meter. -/
namespace J6R68.RetireScratch
open AOracleMachineTime J6R27OriginalGate J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R57ScopeFee J6R64Active

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 8000000

structure TailCopyObservation (width : ℕ) where
  source : SavedDirectoryTails width
  copied : SavedDirectoryTails width

def tailDataBits {width : ℕ} (x : SavedDirectoryTails width) : ℕ :=
  x.headers.bits.length+x.records.bits.length

def TailCopyObservation.selectedBits {width : ℕ} (x : TailCopyObservation width) : ℕ :=
  tailDataBits x.source+tailDataBits x.copied

theorem actual_two_words_have_fixed_width {width : ℕ} (x : SavedDirectoryTails width) :
    tailDataBits x=2*width := by
  simp only [tailDataBits,x.headers.size,x.records.size,two_mul]

theorem observed_source_and_copy_are_four_words {width : ℕ} (x : TailCopyObservation width) :
    x.selectedBits=4*width := by
  unfold TailCopyObservation.selectedBits
  rw [actual_two_words_have_fixed_width,actual_two_words_have_fixed_width]
  omega

def observeHeaderScope {width key prec tw bw : ℕ} {D Out : Type}
    (tails : SavedDirectoryTails width)
    (j : Job (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) D)
    (go : (R : Ledger key prec tw bw D) → OwnsHeader j.entry.result R → Meter (Out×Ledger key prec tw bw D))
    (bad : Meter Out) (B : Ledger key prec tw bw D) :
    Meter (Out×Ledger key prec tw bw D) × Option (TailCopyObservation width) :=
  let q := j.install B
  if hit : q.result.2=true then
    let out := go q.result.1 (successful_publish_has_exact_head j B hit)
    let done := restoreSavedDirectory tails
    (⟨(out.result.1,B),q.steps+out.steps+done.steps+4⟩,some ⟨tails,done.result⟩)
  else (⟨(bad.result,B),q.steps+bad.steps+4⟩,none)

theorem observed_header_projects_to_same_actual_meter {width key prec tw bw : ℕ} {D Out : Type}
    (tails : SavedDirectoryTails width) (j : Job (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) D)
    (go : (R : Ledger key prec tw bw D) → OwnsHeader j.entry.result R → Meter (Out×Ledger key prec tw bw D))
    (bad : Meter Out) (B : Ledger key prec tw bw D) :
    (observeHeaderScope tails j go bad B).1=withScopeHeader (retireSavedDirectory tails) j go bad B := by
  by_cases hit : (j.install B).result.2=true
  · simp only [observeHeaderScope,withScopeHeader,dif_pos hit,retireSavedDirectory]
  · simp only [observeHeaderScope,withScopeHeader,dif_neg hit]

theorem illegal_header_scope_has_no_retire_copy {width key prec tw bw : ℕ} {D Out : Type}
    (tails : SavedDirectoryTails width) (j : Job (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) D)
    (go : (R : Ledger key prec tw bw D) → OwnsHeader j.entry.result R → Meter (Out×Ledger key prec tw bw D))
    (bad : Meter Out) (B : Ledger key prec tw bw D)
    (rejected : (j.install B).result.2≠true) :
    (observeHeaderScope tails j go bad B).2=none := by
  simp only [observeHeaderScope,dif_neg rejected]

theorem legal_header_observes_exact_tail_copy {width key prec tw bw : ℕ} {D Out : Type}
    (tails : SavedDirectoryTails width) (j : Job (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) D)
    (go : (R : Ledger key prec tw bw D) → OwnsHeader j.entry.result R → Meter (Out×Ledger key prec tw bw D))
    (bad : Meter Out) (B : Ledger key prec tw bw D) (legal : JobsReady B [j]) :
    (observeHeaderScope tails j go bad B).2=some ⟨tails,tails⟩ := by
  have hit : (j.install B).result.2=true := by rw [(next_job_exact B j [] legal).1]
  simp only [observeHeaderScope,dif_pos hit,restored_directory_handles_exact]

/-- Equal-width debit callbacks encode no evidence about which old
handle names, if any, refer to the caller's actual saved directory. -/
theorem unchanged_meter_cannot_bind_tail_bytes {width key prec tw bw : ℕ} {D Out : Type}
    (x y : SavedDirectoryTails width) (j : Job (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) D)
    (go : (R : Ledger key prec tw bw D) → OwnsHeader j.entry.result R → Meter (Out×Ledger key prec tw bw D))
    (bad : Meter Out) (B : Ledger key prec tw bw D) :
    withScopeHeader (retireSavedDirectory x) j go bad B=
      withScopeHeader (retireSavedDirectory y) j go bad B := by
  have arbitrary : (@retireSavedDirectory width key prec tw bw D x)=retireSavedDirectory y := by
    funext reg
    rw [retire_debit_is_the_fixed_handle_fee,retire_debit_is_the_fixed_handle_fee]
  rw [arbitrary]

#print axioms actual_two_words_have_fixed_width
#print axioms observed_source_and_copy_are_four_words
#print axioms observed_header_projects_to_same_actual_meter
#print axioms illegal_header_scope_has_no_retire_copy
#print axioms legal_header_observes_exact_tail_copy
#print axioms unchanged_meter_cannot_bind_tail_bytes
end J6R68.RetireScratch
